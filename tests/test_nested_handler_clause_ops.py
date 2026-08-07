"""#1211: a clause body's bare op belongs to the ENCLOSING context.

A handler clause is not part of the body it refines.  The checker says so
structurally — clauses are checked *before* the handled effect joins the
effect row (``vera/checker/control.py``), so a bare ``get``/``put`` written
in a clause body resolves against whatever encloses the ``handle``
expression, exactly like an outer slot reference in a clause body resolves
against the handler-declaration scope (§7.5.2).

Codegen used to disagree.  ``_translate_state_clause_op`` cleared the clause
registry before inlining a clause body — enough to stop a clause re-entering
itself — but left ``_effect_ops`` pointing at the handler's OWN host-cell
imports.  With two nested handlers over different cell families, a bare op in
the inner handler's clause body read and wrote the INNER cell while the
checker had typed it against the outer one: check-green, verify-clean, valid
WASM, silently wrong value.

Every expected value below is derived from the CHECKER's story, never from
what codegen happens to emit.  Each case is asserted on all three
components — the checker accepts it, the verifier discharges it cleanly, and
the compiled program produces the checker's value — so a future regression in
any one of them shows up as a disagreement rather than as a quietly shifted
oracle.  The `pre_fix` value on each case is what codegen actually produced
before the alignment; it is asserted to be *different*, so a case that stops
distinguishing the two semantics fails loudly instead of passing vacuously.
"""

from __future__ import annotations

import pytest

from tests.codegen_helpers import _run
from tests.checker_helpers import _check_ok
from tests.verifier_helpers import _verify_ok

# `probe` holds the shape; `main` just calls it, so every case shares one
# entry point and the compiled value is the shape's own.
_MAIN = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(())
}
"""

# --- depth 2, bare `put` inside the inner PUT clause ------------------
# Outer State<Int> = 111, inner State<Nat> = 7.
#   put(3)      -> inner put clause: stores 3 into the Nat cell, then its
#                  body's bare put(1000) targets the ENCLOSING State<Int>.
#   get(())     -> 3 (the Nat cell)
#   outer get   -> 1000
# => 3 * 100000 + 1000 = 301000.  Routing the clause-body put to the inner
# cell instead gives 1000 * 100000 + 111 = 100000111.
_PUT_IN_PUT_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { put(1000); resume(()) }
    } in {
      put(3);
      get(())
    };
    nat_to_int(@Nat.0) * 100000 + get(())
  }
}
"""

# --- depth 2, bare `put` inside the inner GET clause ------------------
# Outer State<Int> = 5, inner State<Nat> = 9.  The get clause captures the
# pre-read Nat state (9) and its body's put(77) targets the outer Int cell.
# => 9 * 1000 + 77 = 9077 (inner routing leaves the outer at 5: 9005).
_PUT_IN_GET_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 9) {
      get(@Unit) -> { put(77); resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) * 1000 + get(())
  }
}
"""

# --- depth 2, bare `get` inside a `with` state-update expression ------
# The `with` expression is clause scope too, so its bare get(()) reads the
# ENCLOSING State<Nat> (4), overriding the Int cell with 40 rather than with
# ten times the value just stored (70).  => 40 * 100 + 4 = 4004 (vs 7004).
# It also pins the inference mirror: `nat_to_int(get(()))` only type-checks
# in WASM if the op's result type came from the outer cell.
_GET_IN_WITH_EXPR = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 4) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    let @Int = handle[State<Int>](@Int = 1) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) } with @Int = nat_to_int(get(())) * 10
    } in {
      put(7);
      get(())
    };
    @Int.0 * 100 + nat_to_int(get(()))
  }
}
"""

# --- depth 3: the IMMEDIATELY enclosing handler, not the outermost ----
# Bool (outer) / Nat (middle) / Int (inner).  The inner get clause's bare
# put(33) must land in the MIDDLE Nat cell — proving the rule walks out one
# level, not all the way.  => 33 * 1000 + 7 = 33007 (inner routing: 20007).
# The Bool cell stays false throughout, which the final `if` reads.
_DEPTH_THREE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Bool>](@Bool = false) {
    get(@Unit) -> { resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    let @Int = handle[State<Nat>](@Nat = 20) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      let @Int = handle[State<Int>](@Int = 7) {
        get(@Unit) -> { put(33); resume(@Int.0) },
        put(@Int) -> { resume(()) }
      } in {
        get(())
      };
      nat_to_int(get(())) * 1000 + @Int.0
    };
    if get(()) then {
      0 - 1
    } else {
      @Int.0
    }
  }
}
"""

# --- the qualified spelling must agree with the bare one --------------
# `State.put(...)` delegates to the same dispatcher (PR #1202 round 4), so
# the enclosing-context rule has to hold for it too: same 301000.
_QUALIFIED_IN_CLAUSE = _PUT_IN_PUT_CLAUSE.replace(
    "put(@Nat) -> { put(1000); resume(()) }",
    "put(@Nat) -> { State.put(1000); resume(()) }",
)

# --- a nested handle expression INSIDE a clause body -----------------
# The nested handle owns its own registries: its body's get(()) reads ITS
# fresh Int cell (30), and when it pops, the clause's own bare put must be
# back on the DECLARATION-time registries — the enclosing State<Int> — not
# on the Nat handler's.  Same family as the outer handler on purpose: the
# fresh cell is pushed and popped, so a leak in either direction shows.
#   nested cell 30 -> put(32) into the OUTER Int cell; inner Nat stays 8
# => 8 * 1000 + 32 = 8032.  Restoring to the Nat handler instead writes 32
# into the Nat cell and leaves the outer at 111: 8111.
_HANDLE_INSIDE_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 8) {
      get(@Unit) -> {
        let @Int = handle[State<Int>](@Int = 30) {
          get(@Unit) -> { resume(@Int.0) },
          put(@Int) -> { resume(()) }
        } in {
          get(())
        };
        put(@Int.0 + 2);
        resume(@Nat.0)
      },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) * 1000 + get(())
  }
}
"""

# --- the op's RESULT TYPE mirrors follow the enclosing cell too -------
# `_effect_op_result_wt` types a bare get(()) in match-scrutinee position
# (#914 A2).  Outer cell is Option<Int> (an i32 pointer), inner is Nat (i64),
# so leaving that mirror at the inner handler emits an i64 scrutinee for an
# i32 value — invalid WASM, on a check-green program.
#   put(3)  -> Nat cell 3; clause body matches the OUTER Some(9) and writes
#              Some(10) back to it
# => 3 * 100 + 10 = 310.  (Pre-fix the whole clause body targeted the Nat
# cell: `match get(())` read an i64 as an Option pointer.)
_MATCH_SCRUTINEE_IN_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> {
        let @Int = match get(()) {
          Some(@Int) -> { @Int.0 },
          None -> { 0 }
        };
        put(Some(@Int.0 + 1));
        resume(())
      }
    } in {
      put(3);
      get(())
    };
    match get(()) {
      Some(@Int) -> { nat_to_int(@Nat.0) * 100 + @Int.0 },
      None -> { 0 - 1 }
    }
  }
}
"""

# The Vera-name twin: `_effect_op_result_vera` picks an array literal's
# ELEMENT layout (#1006), which the layout-ambiguous WAT type cannot.  Same
# nesting; the clause body wraps the outer cell's value in an array and puts
# it straight back, so the outer stays Some(9).  => 3 * 100 + 9 = 309.
_ARRAY_ELEMENT_IN_CLAUSE = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 7) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> {
        let @Array<Option<Int>> = [get(())];
        put(@Array<Option<Int>>.0[0]);
        resume(())
      }
    } in {
      put(3);
      get(())
    };
    match get(()) {
      Some(@Int) -> { nat_to_int(@Nat.0) * 100 + @Int.0 },
      None -> { 0 - 1 }
    }
  }
}
"""

# (case id, source, checker-derived value, value codegen produced pre-fix)
# `pre_fix = None` marks a shape that did not COMPILE before the alignment
# (invalid WASM from a check-green program) — distinguishing by construction.
_CASES = [
    ("put_in_put_clause", _PUT_IN_PUT_CLAUSE, 301000, 100000111),
    ("put_in_get_clause", _PUT_IN_GET_CLAUSE, 9077, 9005),
    ("get_in_with_expr", _GET_IN_WITH_EXPR, 4004, 7004),
    ("depth_three", _DEPTH_THREE, 33007, 20007),
    ("qualified_in_clause", _QUALIFIED_IN_CLAUSE, 301000, 100000111),
    ("handle_inside_clause", _HANDLE_INSIDE_CLAUSE, 8032, 8111),
    ("match_scrutinee_in_clause", _MATCH_SCRUTINEE_IN_CLAUSE, 310, None),
    ("array_element_in_clause", _ARRAY_ELEMENT_IN_CLAUSE, 309, None),
]


@pytest.mark.parametrize(
    ("source", "expected", "pre_fix"),
    [pytest.param(s, e, p, id=i) for i, s, e, p in _CASES],
)
def test_clause_body_op_targets_the_enclosing_cell(
    source: str, expected: int, pre_fix: int | None,
) -> None:
    """checker = codegen = verifier on every nested clause-body op shape.

    All three legs are asserted together on purpose: the defect this pins
    was check-green AND verify-clean, so either leg alone would have passed
    while the compiled program returned the wrong number.
    """
    program = source + _MAIN
    _check_ok(program)
    _verify_ok(program)
    assert _run(program) == expected


def test_every_case_distinguishes_the_two_semantics() -> None:
    """A case whose pre-fix and post-fix values coincide proves nothing.

    Each shape has to separate enclosing-cell routing from inner-cell
    routing — either by returning a different number (`pre_fix` is that
    number) or by not compiling at all under the old routing (`pre_fix` is
    None) — or it has quietly stopped being a regression test.  (The control
    that the alignment does not move anything ELSE is the corpus differential
    run for this change: over the 494 `.vera` programs in `examples/`,
    `tests/conformance/`, and `tests/probes/`, exactly the two
    nested-clause-body programs moved.)
    """
    for case_id, _src, expected, pre_fix in _CASES:
        assert expected != pre_fix, (
            f"{case_id} no longer distinguishes enclosing-cell routing "
            f"from inner-cell routing (both {expected})"
        )
