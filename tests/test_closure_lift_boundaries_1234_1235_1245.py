"""Closure lifting at refinement boundaries: #1234, #1245, #1235.

Three defects of one seam — the lifted-closure path in
`vera/codegen/closures.py` and the order `_compile_fn` drives it in.

* **#1245** — `_lift_pending_closures` ran BEFORE `_compile_postconditions`,
  so any closure created while lowering a refined RETURN guard, a tuple
  return's component guards, or an `ensures(...)` predicate was registered
  on the context and then never lifted.  The module's function table stayed
  empty, the `call_indirect` the closure's own construction emitted was
  orphaned, and the #1185 drop-propagation pass dropped the function and
  every caller: a check-green, verify-clean program compiled to ZERO
  exports.  Loud, but total.
* **#1234** — the lift worklist fed itself.  A refinement whose predicate
  contains a closure refined by the SAME type (`type R = { @Int | …
  fn(@R -> @Int) … }`, used in a signature) has each lifted closure's
  refined-formal guard lower a predicate containing that same `AnonFn`,
  which queues another closure, for ever.  `vera compile` never returned.
  The registration pre-scan has been cycle-guarded since #1232 round 7;
  this is the lift loop's own guard.
* **#1235** — the closure path emitted TOP-LEVEL formal / return refinement
  guards only.  A named function with a `Tuple<PosInt, Int>` formal gets
  per-component #746 boundary guards; a closure with the same formal
  crossed unguarded, so a violating component reaching an `AnonFn` through
  `apply_fn` was never checked where the named path checks it.

The three are tested together because they share one fix surface and one
invariant: what the closure path LOWERS must equal what the registration
derivation (`_signature_refinement_predicates`) ENUMERATES.  #1235's fix
flips that derivation's `FnDecl`-only component leg on for closures, and
the co-extension pin in `tests/test_state_exn_registration.py`
(`test_a_closure_tuple_formal_registers_what_it_now_lowers`) flipped with
it, from "nothing spurious is registered" to "what is lowered is declared".
"""

from __future__ import annotations

import threading
import time

import pytest

from tests.checker_helpers import _check_ok
from tests.codegen_helpers import (
    _assert_call_indirect_iff_table,
    _compile,
    _run,
    _run_refine_trap,
)
from tests.verifier_helpers import _verify_ok

# =====================================================================
# #1245 — a closure created by a RETURN-position guard must be lifted
# =====================================================================

# The characterization fixture from PR #1239's review, promoted to an
# executable oracle.  `array_range(18, 21)` is [18, 19, 20]: every element
# satisfies the predicate, so the return guard passes and the length is 3 —
# a value that cannot coincide with the zero-exports failure (which
# produces no value at all) nor with an empty-array vacuous truth.
_CLOSURE_IN_RETURN_REFINEMENT = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn mk(@Array<Nat> -> @Grown)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(mk(array_range(18, 21)))
}
"""

# The same predicate in PARAMETER position — lowered by `_compile_fn`
# BEFORE the lift, so it always worked.  Its presence is what makes the
# return-position failure a lift-ORDERING defect rather than a
# closure-in-a-predicate limitation.
_CLOSURE_IN_PARAM_REFINEMENT = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn take(@Grown -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Grown.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  take(array_range(18, 21))
}
"""

# The `ensures(...)` twin: the SAME ordering bug reached without any
# refinement at all, found while root-causing #1245.  A closure in a
# postcondition predicate is lowered by `_compile_postconditions` and was
# equally never lifted.
_CLOSURE_IN_ENSURES = """
public fn main(@Unit -> @Nat)
  requires(true)
  ensures(array_all(array_range(18, 21), fn(@Nat -> @Bool)
    effects(pure) { @Nat.0 >= 18 }))
  effects(pure)
{
  array_length(array_range(18, 21))
}
"""

# The guard must also ENFORCE, not merely exist: a body whose result
# violates the closure-bearing predicate traps at the return boundary.
_CLOSURE_IN_RETURN_REFINEMENT_VIOLATED = """
type Grown = { @Array<Nat> | array_all(@Array<Nat>.0, fn(@Nat -> @Bool)
  effects(pure) { @Nat.0 >= 18 }) };

private fn mk(@Array<Nat> -> @Grown)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(mk(array_range(1, 4)))
}
"""


class TestAClosureInAReturnPositionPredicateIsLifted:
    """#1245: check-green + verify-clean must mean a runnable module."""

    def test_the_return_refinement_program_runs(self) -> None:
        _check_ok(_CLOSURE_IN_RETURN_REFINEMENT)
        _verify_ok(_CLOSURE_IN_RETURN_REFINEMENT)
        assert _run(_CLOSURE_IN_RETURN_REFINEMENT) == 3

    def test_the_param_position_control_still_runs(self) -> None:
        """The always-worked half — pins that the fix changed the right one."""
        assert _run(_CLOSURE_IN_PARAM_REFINEMENT) == 3

    def test_an_ensures_clause_closure_runs(self) -> None:
        """The same ordering defect with no refinement in sight."""
        _check_ok(_CLOSURE_IN_ENSURES)
        assert _run(_CLOSURE_IN_ENSURES) == 3

    def test_the_module_exports_and_holds_its_table(self) -> None:
        """The observable the issue names: exports, and a table for the
        `call_indirect` the predicate's closure construction emits."""
        result = _compile(_CLOSURE_IN_RETURN_REFINEMENT)
        wat = result.wat or ""
        assert 'call_indirect' in wat, wat[:400]
        _assert_call_indirect_iff_table(wat)
        assert 'export "main"' in wat, wat[:400]

    def test_the_lifted_guard_actually_enforces(self) -> None:
        """A violating return traps — the guard is emitted, not just lifted."""
        _run_refine_trap(_CLOSURE_IN_RETURN_REFINEMENT_VIOLATED)


# =====================================================================
# #1234 — the lift worklist must not feed itself
# =====================================================================

_SELF_REFERENTIAL_IN_A_SIGNATURE = """
type SelfRef = { @Int | @Int.0 > 0 && apply_fn(fn(@SelfRef -> @Int)
  effects(pure) { @SelfRef.0 }, 3) > 0 };

private fn f(@SelfRef -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @SelfRef.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(7)
}
"""

# The control the guard must NOT catch: a refinement whose predicate
# contains a closure refined by a DIFFERENT refinement, which itself
# contains a closure over an unrefined base.  Two distinct `AnonFn` nodes,
# a finite chain — the lift must walk it and the program must run.  `Inner`
# holds for 4 (`4 > 0`), so `g(9)` returns 9: a value that coincides with
# neither 0 nor the argument of any predicate.
_NESTED_NON_CYCLIC_REFINEMENT = """
type Inner = { @Int | @Int.0 > 0 };

type Outer = { @Int | @Int.0 > 0 && apply_fn(fn(@Inner -> @Int)
  effects(pure) { @Inner.0 }, 4) > 0 };

private fn g(@Outer -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Outer.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(9)
}
"""


def _compile_within(source: str, budget_s: float) -> object:
    """Compile *source* on a daemon thread, failing if it outlives *budget_s*.

    A non-terminating lift must not hang the suite: the worker is a daemon,
    so an unfixed compiler leaves a live thread that never blocks
    interpreter exit while this assertion fails immediately.  ``pytest.fail``
    rather than ``assert`` so the message survives ``python -O``.
    """
    box: list[object] = []
    err: list[BaseException] = []

    def _work() -> None:
        try:
            box.append(_compile(source))
        except BaseException as exc:  # noqa: BLE001 — re-raised on the main thread
            err.append(exc)

    t = threading.Thread(target=_work, daemon=True)
    start = time.monotonic()
    t.start()
    t.join(budget_s)
    elapsed = time.monotonic() - start
    if t.is_alive():
        pytest.fail(
            f"compile did not terminate within {budget_s}s (#1234: the "
            "closure-lift worklist is feeding itself)"
        )
    if err:
        raise err[0]
    assert elapsed < budget_s, elapsed
    return box[0]


class TestTheLiftQueueIsCycleGuarded:
    """#1234: a self-referential refinement in a signature must terminate."""

    def test_it_terminates_with_a_loud_skip(self) -> None:
        _check_ok(_SELF_REFERENTIAL_IN_A_SIGNATURE)
        result = _compile_within(_SELF_REFERENTIAL_IN_A_SIGNATURE, 60.0)
        diags = getattr(result, "diagnostics", [])
        codes = [d.error_code for d in diags]
        assert "E602" in codes, [(d.error_code, d.description) for d in diags]
        # The skip must NAME the self-reference, not merely say "skipped".
        said = " ".join(
            d.description for d in diags if d.error_code == "E602")
        assert "SelfRef" in said, said
        assert "self-referential" in said.lower(), said

    def test_a_finite_nested_refinement_chain_still_lifts_and_runs(
        self,
    ) -> None:
        """The control: the guard must fire on a CYCLE, not on nesting."""
        _check_ok(_NESTED_NON_CYCLIC_REFINEMENT)
        assert _run(_NESTED_NON_CYCLIC_REFINEMENT) == 9


# =====================================================================
# #1235 — closure boundaries get the tuple-COMPONENT guards too
# =====================================================================

# The boundary under test is the FORMAL, so neither body reads the tuple:
# the guard has to fire on the value crossing, not on anything the callee
# does with it.  `probe` scales the result so the passing oracle (70) is a
# constant no default or dropped-function path produces.
_CLOSURE_TUPLE_COMPONENT = """
type PosInt = { @Int | @Int.0 > 0 };
type PairToInt = fn(Tuple<PosInt, Int> -> Int) effects(pure);

private fn make(@Unit -> @PairToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Tuple<PosInt, Int> -> @Int) effects(pure) { 7 }
}

private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @PairToInt = make(());
  apply_fn(@PairToInt.0, Tuple(@Int.0, 2)) * 10
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(FIRST)
}
"""

# The NAMED twin of the same boundary, so the two paths are compared on one
# program shape rather than on the closure path alone.
_NAMED_TUPLE_COMPONENT = """
type PosInt = { @Int | @Int.0 > 0 };

private fn takes(@Tuple<PosInt, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  takes(Tuple(@Int.0, 2)) * 10
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(FIRST)
}
"""


def _at(source: str, first: str) -> str:
    return source.replace("FIRST", first)


class TestAClosureTupleFormalIsComponentGuarded:
    """#1235: the closure path enforces what the named path enforces."""

    def test_the_closure_traps_on_a_violating_component(self) -> None:
        """`0 - 5` violates `PosInt` in component 0 — it must not cross."""
        _run_refine_trap(_at(_CLOSURE_TUPLE_COMPONENT, "0 - 5"))

    def test_the_named_path_traps_identically(self) -> None:
        """The oracle the closure path is being held to."""
        _run_refine_trap(_at(_NAMED_TUPLE_COMPONENT, "0 - 5"))

    def test_the_passing_path_still_runs(self) -> None:
        """7 satisfies `PosInt`: 70 through both paths, not a trap."""
        assert _run(_at(_CLOSURE_TUPLE_COMPONENT, "7")) == 70
        assert _run(_at(_NAMED_TUPLE_COMPONENT, "7")) == 70
