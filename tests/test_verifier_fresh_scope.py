"""Tests for vera.verifier — fresh-scope obligation walking (#779, #985).

The primitive-op walker (`_walk_for_primitive_op_obligations`) and the
@Nat-binding walker (`_walk_for_nat_binding_obligations`) recurse into
closure bodies (`AnonFn`), quantifier domains and predicates (`ForallExpr`
/ `ExistsExpr`), and handler state/body/clauses (`HandleExpr`), so a
trapping primitive op or a narrowing/widening binding inside one carries
a static obligation instead of vanishing from the stream (#779), and a
closure nested inside another closure's body has its return widening
obligated to match codegen's `_compile_lifted_closure` guard (#985).

Scope discipline (the #779 "care" clause): a handler's state-init and
body and a quantifier's domain evaluate in the ENCLOSING scope, so they
are walked with the enclosing slot environment at full precision — an
obligation there can prove Tier-1 from the function's requires.  Closure
bodies, quantifier predicates, and handler clause bodies bind FRESH
slots, so they are walked with an empty slot environment: a slot
reference inside one never resolves onto an outer same-named slot (which
could prove a FALSE Tier-1 against the outer function's facts), and
every slot-dependent obligation falls to the honest Tier-3 leg while
literal-only shapes still classify exactly (a manifest `5 / 0` is a loud
E526).  Shared helpers live in tests/verifier_helpers.py.
"""
from __future__ import annotations

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast

from tests.verifier_helpers import (
    _verify,
    _verify_err,
)


def _obligations_of(src: str, kind: str) -> list:
    result = _verify(src)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, (
        f"program must verify without errors, got: "
        f"{[(d.error_code, d.description[:60]) for d in errors]}"
    )
    return [o for o in result.obligations if o.kind == kind]


# =====================================================================
# #779 — primitive ops in closure bodies (fresh scope: Tier-3)
# =====================================================================

class TestClosureBodyPrimitiveOps:
    def test_div_in_closure_body_is_tier3(self) -> None:
        """A slot-dependent divisor in a closure body is obligated Tier-3
        (the fresh param is unconstrained; codegen's unconditional
        divide-by-zero trap backs it)."""
        obls = _obligations_of("""
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { 10 / @Int.0 })
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "tier3"

    def test_closure_param_never_proves_against_outer_requires(self) -> None:
        """THE soundness pin for the fresh-scope environment: the outer
        function constrains ITS `@Int.0` to be non-zero, but the closure's
        `@Int.0` is the closure's own fresh parameter — the obligation
        must NOT prove Tier-1 by mis-resolving the closure param onto the
        outer requires-constrained slot."""
        obls = _obligations_of("""
public fn f(@Int, @Array<Int> -> @Array<Int>)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { 10 / @Int.0 })
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status != "verified", (
            "closure param mis-resolved onto the outer requires-constrained "
            "slot — a false Tier-1"
        )

    def test_literal_zero_divisor_in_closure_is_loud_E526(self) -> None:
        """A manifest `5 / 0` inside a closure body is a genuine guaranteed
        trap when invoked — same loud E526 verdict as direct position."""
        errs = _verify_err("""
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Int.0 + (5 / 0) })
}
""", "zero")
        assert any(e.error_code == "E526" for e in errs)

    def test_index_in_closure_body_is_tier3(self) -> None:
        """An index over a captured array in a closure body is obligated
        Tier-3 (the captured length is beyond the fresh-scope fragment,
        #427; codegen's unconditional bounds trap backs it)."""
        obls = _obligations_of("""
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { @Array<Int>.0[0] })
}
""", "index_bounds")
        assert len(obls) == 1
        assert obls[0].status == "tier3"

    def test_nat_sub_in_closure_body_is_tier3(self) -> None:
        """`@Nat - @Nat` underflow on a fresh closure param is obligated
        Tier-3."""
        obls = _obligations_of("""
public fn f(@Array<Nat> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Nat>.0, fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0 - 1) })
}
""", "nat_sub")
        assert len(obls) == 1
        assert obls[0].status == "tier3"

    def test_nat_bind_in_closure_body_is_tier3_guarded(self) -> None:
        """`let @Nat = <closure Int param>` inside a closure body is a
        narrowing obligation, Tier-3 backed by the lifted closure's
        interior codegen guard — proven by the compile-and-run
        differential in tests/test_nat_narrowing_return_differential.py
        (TestClosureInteriorBindingDifferential779)."""
        obls = _obligations_of("""
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { let @Nat = @Int.0; nat_to_int(@Nat.0) })
}
""", "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "tier3"


# =====================================================================
# #779 — quantifier domains (enclosing scope) and predicates (fresh)
# =====================================================================

class TestQuantifierObligations:
    def test_forall_domain_div_proves_from_requires(self) -> None:
        """The quantifier DOMAIN evaluates in the enclosing scope, so its
        divisor is the outer requires-constrained slot and the obligation
        proves Tier-1 — full precision, not a blanket Tier-3."""
        obls = _obligations_of("""
public fn f(@Int, @Array<Int> -> @Bool)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  forall(@Int, 10 / @Int.0, fn(@Int -> @Bool) effects(pure) { true })
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_forall_predicate_div_is_tier3(self) -> None:
        """The quantifier PREDICATE binds the fresh quantified slot, so a
        divisor on it is obligated Tier-3."""
        obls = _obligations_of("""
public fn f(@Array<Int> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  forall(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { 10 / @Int.0 > 0 })
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "tier3"


# =====================================================================
# #779 — handler body (enclosing scope) and clause bodies (fresh)
# =====================================================================

class TestHandlerObligations:
    def test_handle_body_div_proves_from_requires(self) -> None:
        """The handle BODY is plain enclosing-scope code (handler state is
        not even visible there), so its divisor proves Tier-1 from the
        function's requires — full precision."""
        obls = _obligations_of("""
public fn f(@Int, @Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { 0 }
  } in {
    @Int.1 / @Int.0
  }
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_handle_clause_div_is_tier3(self) -> None:
        """A handler CLAUSE body binds the operation's fresh parameters, so
        a divisor on one is obligated Tier-3."""
        obls = _obligations_of("""
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 10 / @Int.0 }
  } in {
    @Int.0 + 1
  }
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "tier3"


# =====================================================================
# #985 — nested closure return widening
# =====================================================================

class TestNestedClosureWidening:
    def test_nested_closure_widen_return_is_obligated(self) -> None:
        """A closure nested inside another closure's body that widens
        `@Nat` into an `@Int` return carries a `nat_to_int_coerce`
        obligation matching codegen's `_compile_lifted_closure` guard —
        the #985 reporting-completeness residual of #820's single-level
        closure obligations."""
        result = _verify("""
public fn f(@Array<Nat>, @Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { nat_to_int(array_length(array_map(@Array<Nat>.0, fn(@Nat -> @Int) effects(pure) { @Nat.0 }))) })
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        widen = [
            o for o in result.obligations
            if o.kind == "nat_to_int_coerce" and o.status == "tier3"
        ]
        assert widen, (
            "the nested closure's @Nat body widening into its @Int return "
            "must be obligated (codegen guards it; the stream must say so)"
        )

    def test_nested_closure_narrow_return_is_obligated(self) -> None:
        """The narrowing twin (#984's closure dual, also #985): a nested
        closure whose bare `@Int` body narrows into a `@Nat` return
        carries a `nat_bind` obligation, Tier-3 backed by the lifted
        closure's return guard."""
        result = _verify("""
public fn f(@Array<Int>, @Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { nat_to_int(array_length(array_map(@Array<Int>.1, fn(@Int -> @Nat) effects(pure) { @Int.0 }))) })
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        narrows = [
            o for o in result.obligations
            if o.kind == "nat_bind" and o.status == "tier3"
        ]
        assert narrows, (
            "the nested closure's @Int body narrowing into its @Nat return "
            "must be obligated (codegen guards it; the stream must say so)"
        )


# =====================================================================
# Review round: the nat-binding walker descends assert / assume
# conditions (a call argument narrowing inside one is obligated) and
# carries the WALKER_COVERAGE marker so the #597 gate enforces its
# case split from now on.
# =====================================================================

class TestNatBindingWalkerAssertAssume:
    def test_narrowing_call_arg_inside_assert_condition_obligated(self) -> None:
        """`assert(takes_nat(0 - 5) > 0)` hosts an @Int→@Nat narrowing in
        the asserted condition; the nat-binding walker must reach it (the
        primitive-op and calls walkers already descend assert conditions)
        — before the fix it recorded ZERO nat_bind obligations and the
        provably-negative argument passed silently."""
        errs = _verify_err("""
private fn takes_nat(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ nat_to_int(@Nat.0) }

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assert(takes_nat(0 - 5) > 0);
  0
}
""", "narrowing")
        assert any(e.error_code == "E503" for e in errs)

    def test_narrowing_call_arg_inside_assume_condition_obligated(self) -> None:
        """The assume twin: the condition is taken on trust, but a
        narrowing op nested inside it still executes and is obligated."""
        errs = _verify_err("""
private fn takes_nat(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ nat_to_int(@Nat.0) }

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume(takes_nat(0 - 5) > 0);
  0
}
""", "narrowing")
        assert any(e.error_code == "E503" for e in errs)


# =====================================================================
# Mutation-derived battery (PR #1202 test-coverage review): each test
# below kills a specific mutant that survived the original 12 — the
# nat-binding walker's container arms and env-honesty were unobserved
# (a combined mutant deleting both arms passed the full suite).
# =====================================================================

class TestNatBindingFreshScopeHonesty:
    """The nat-binding twins of the primitive walker's soundness pin and
    scope-precision tests — the #779 care clause applies to BOTH walkers,
    and only distinguishing shapes (an outer requires-constrained slot of
    the same type) can tell an honest fresh env from a dishonest
    enclosing-env descent."""

    def test_closure_nat_bind_never_proves_against_outer_requires(self) -> None:
        """M8 killer: outer `requires(@Int.0 >= 0)`, closure narrows ITS
        OWN `@Int.0` — a dishonest enclosing-env descent would falsely
        prove the narrowing from the outer fact while codegen still traps
        a negative element."""
        obls = _obligations_of("""
public fn f(@Int, @Array<Int> -> @Array<Int>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { let @Nat = @Int.0; nat_to_int(@Nat.0) })
}
""", "nat_bind")
        assert len(obls) == 1
        assert obls[0].status != "verified", (
            "closure narrowing proved against the OUTER requires — the "
            "dishonest-env false Tier-1"
        )

    def test_handle_clause_nat_bind_never_proves_against_outer_requires(self) -> None:
        """M7 killer: the clause twin — the thrown payload can be negative
        (`throw(0 - 5)`) regardless of the outer function's requires."""
        obls = _obligations_of("""
public fn f(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { let @Nat = @Int.0; nat_to_int(@Nat.0) }
  } in {
    if @Int.0 == 0 then { throw(0 - 5) } else { @Int.0 }
  }
}
""", "nat_bind")
        assert len(obls) == 1
        assert obls[0].status != "verified", (
            "clause narrowing proved against the OUTER requires — the "
            "dishonest-env false Tier-1"
        )

    def test_handle_body_nat_bind_proves_from_requires(self) -> None:
        """M2 killer (enclosing-scope leg): a narrowing in the handle BODY
        is enclosing-scope code and proves Tier-1 from the requires."""
        obls = _obligations_of("""
public fn f(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  handle[Exn<String>] {
    throw(@String) -> { 0 }
  } in {
    let @Nat = @Int.0;
    nat_to_int(@Nat.0)
  }
}
""", "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_forall_domain_nat_formal_call_proves_from_requires(self) -> None:
        """M1 killer (domain leg): a @Nat-formal call argument in a
        quantifier DOMAIN proves Tier-1 from the enclosing requires."""
        obls = _obligations_of("""
private fn take(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ nat_to_int(@Nat.0) }

public fn f(@Int, @Array<Int> -> @Bool)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  forall(@Int, take(@Int.0), fn(@Int -> @Bool) effects(pure) { true })
}
""", "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_exists_predicate_nat_bind_is_tier3(self) -> None:
        """M1 killer (predicate leg, via `exists` to cover the tuple's
        second member in this walker): a narrowing on the fresh
        quantified slot is Tier-3."""
        obls = _obligations_of("""
public fn f(@Array<Int> -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  exists(@Int, array_length(@Array<Int>.0), fn(@Int -> @Bool) effects(pure) { nat_to_int({ let @Nat = @Int.0; @Nat.0 }) > 0 })
}
""", "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "tier3"


class TestFreshScopePerKindClassification:
    """Remaining per-kind fresh-scope classifications: the state-init
    enclosing walk (M3), the clause state-update descent (M4), the
    refined-narrowing disclosure, and loud-parity for assert / literal
    index in closures."""

    def test_handler_state_init_div_proves_from_requires(self) -> None:
        """M3 killer: the ONLY enclosing-scope walk with no corpus signal —
        a divisor in the handler state-init proves Tier-1 from requires."""
        obls = _obligations_of("""
public fn f(@Int -> @Int)
  requires(@Int.0 != 0)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 100 / @Int.0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_clause_state_update_div_is_tier3(self) -> None:
        """M4 killer: a slot-dependent divisor in a clause `with` state
        update (fresh scope) is Tier-3."""
        obls = _obligations_of("""
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = 10 / @Int.0
  } in {
    put(3);
    get(())
  }
}
""", "div_zero")
        assert len(obls) == 1
        assert obls[0].status == "tier3"

    def test_refined_let_in_closure_discloses_unguarded(self) -> None:
        """A refined narrowing inside a closure has no interior codegen
        guard and an untranslatable predicate under the empty env — it
        must disclose honestly: `tier3_unguarded` + the E506 warning (the
        only user-visible signal), never a silent pass or a false
        verdict."""
        result = _verify("""
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { let @Pos = @Int.0; @Pos.0 })
}
""")
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        refined = [o for o in result.obligations if o.kind == "refine_bind"]
        assert len(refined) == 1
        assert refined[0].status == "tier3_unguarded"
        warnings = [d for d in result.diagnostics if d.severity == "warning"]
        assert any(w.error_code == "E506" for w in warnings), (
            "the E506 disclosure is the only user-visible signal of an "
            "unguarded unproven refinement narrowing in a closure"
        )

    def test_refined_let_literal_in_closure_proves(self) -> None:
        """The literal-precision twin: `let @Pos = 5` in a closure proves
        (no slots involved — the empty env costs nothing)."""
        obls = _obligations_of("""
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { let @Pos = 5; @Pos.0 })
}
""", "refine_bind")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_false_assert_in_closure_is_loud(self) -> None:
        """Loud parity for assert: a literal-false asserted condition in a
        closure body is the same E507 verdict as direct position."""
        errs = _verify_err("""
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { assert(1 > 2); @Int.0 })
}
""", "assert")
        assert any(e.error_code == "E507" for e in errs)

    def test_literal_oob_index_in_closure_is_loud(self) -> None:
        """Loud parity for bounds: a literal out-of-bounds index in a
        closure body is the same E527 verdict as direct position."""
        errs = _verify_err("""
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Int) effects(pure) { [1, 2, 3][5] + @Int.0 })
}
""", "bounds")
        assert any(e.error_code == "E527" for e in errs)

    def test_ensures_position_quantifier_index_is_tier3(self) -> None:
        """The walker also runs on ensures clauses: an index inside an
        ensures-position quantifier predicate records Tier-3 (the common
        real-world contract shape — all corpus quantifiers are
        body-position, so this documents the intent)."""
        src = """
public fn f(@Array<Int> -> @Array<Int>)
  requires(true)
  ensures(forall(@Int, array_length(@Array<Int>.result), fn(@Int -> @Bool) effects(pure) { @Array<Int>.0[0] >= 0 }))
  effects(pure)
{
  @Array<Int>.0
}
"""
        # Self-protection (PR #1202 round-3 review): `_verify` discards
        # check diagnostics, so an ill-typed predicate would still satisfy
        # the tier3 assertions coincidentally — pin that the shape
        # type-checks before trusting the verify verdict.
        check_diags, _arts = typecheck_with_artifacts(parse_to_ast(src), src)
        assert not [d for d in check_diags if d.severity == "error"], (
            f"shape must type-check: {[d.description[:60] for d in check_diags]}"
        )
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        idx = [o for o in result.obligations if o.kind == "index_bounds"]
        assert len(idx) == 1
        assert idx[0].status == "tier3"


# =====================================================================
# Silent-failure review round: a NESTED constructor sub-pattern
# narrowing on an unprojectable scrutinee records an honest fallback
# instead of vanishing — under the fresh-scope descent, every match in
# a closure has an unprojectable scrutinee, so the silent `continue`
# turned a corner case into the common case (verify-clean, bare
# `anon_0` trap at runtime with zero disclosure).
# =====================================================================

_NESTED_SUBPAT_CLOSURE = """
private data Box {
  MkBox(Int)
}

private data Wrap {
  MkWrap(Box)
}

private fn mk(@Int -> @Wrap)
  requires(true)
  ensures(true)
  effects(pure)
{ MkWrap(MkBox(@Int.0)) }

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = array_map([@Int.0], fn(@Int -> @Int) effects(pure) { match mk(@Int.0) { MkWrap(MkBox(@Nat)) -> nat_to_int(@Nat.0) } });
  @Array<Int>.0[0]
}
"""


class TestNestedSubpatternFallback:
    def test_nested_nat_bind_in_closure_records_tier3(self) -> None:
        """The nested `@Nat` bind (`MkWrap(MkBox(@Nat))`) on a closure's
        unprojectable scrutinee records one guarded Tier-3 `nat_bind` —
        the run-trap differential in
        tests/test_nat_narrowing_return_differential.py proves the
        codegen guard it claims (both direct and closure positions trap
        a negative)."""
        result = _verify(_NESTED_SUBPAT_CLOSURE)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert len(binds) == 1, (
            f"nested sub-pattern narrowing vanished from the stream, "
            f"got {[(o.kind, o.status) for o in result.obligations]}"
        )
        assert binds[0].status == "tier3"


# =====================================================================
# #1203: handler boundary writes into a @Nat state cell are obligated —
# state-init (enclosing scope, provable), the builtin `put` argument,
# the `with` state update, and the `resume` argument.  Before the fix
# every one was verify-clean with zero obligations while `vera run`
# stored a negative through the cell (the run-trap differentials live in
# tests/test_nat_narrowing_return_differential.py).
# =====================================================================

_STATE_HANDLER = """\
  handle[State<Nat>](@Nat = {init}) {{
    get(@Unit) -> {{ resume({resume_arg}) }},
    put(@Nat) -> {{ resume(()) }}{with_clause}
  }} in {{
    {body}
  }}
"""


def _state_fixture(init="0", resume_arg="@Nat.0", with_clause="", body="nat_to_int(get(()))", requires="true"):
    return f"""
public fn go(@Int -> @Int)
  requires({requires})
  ensures(true)
  effects(pure)
{{
{_STATE_HANDLER.format(init=init, resume_arg=resume_arg, with_clause=with_clause, body=body)}
}}
"""


class TestHandlerStateBoundaryObligations:
    def test_state_init_unconstrained_narrowing_is_loud(self) -> None:
        """`(@Nat = @Int.0)` — the init is enclosing-scope code at FULL
        precision, so an unconstrained refutable narrowing is the same
        loud E503 as a direct-position `let @Nat = @Int.0` (the Tier-1
        twin below proves it from requires)."""
        errs = _verify_err(_state_fixture(init="@Int.0"),
                           "handler state init")
        assert any(e.error_code == "E503" for e in errs)

    def test_state_init_narrowing_proves_from_requires(self) -> None:
        """The enclosing-scope precision twin: `requires(@Int.0 >= 0)`
        discharges the init narrowing at Tier 1."""
        obls = _obligations_of(
            _state_fixture(init="@Int.0", requires="@Int.0 >= 0"), "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_put_argument_unconstrained_narrowing_is_loud(self) -> None:
        """`put(@Int.0)` in the handled BODY — enclosing-scope precision,
        so the refutable narrowing into the @Nat cell is the same loud
        E503 as a direct call argument (was a silent zero-obligation
        pass)."""
        errs = _verify_err(
            _state_fixture(body="put(@Int.0);\n  nat_to_int(get(()))"),
            "effect-op argument")
        assert any(e.error_code == "E503" for e in errs)

    def test_put_argument_narrowing_proves_from_requires(self) -> None:
        """The precision twin: `requires(@Int.0 >= 0)` discharges the put
        argument at Tier 1."""
        obls = _obligations_of(
            _state_fixture(body="put(@Int.0);\n  nat_to_int(get(()))",
                           requires="@Int.0 >= 0"),
            "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "verified"

    def test_with_update_narrowing_is_obligated(self) -> None:
        """`with @Nat = @Int.0` — the clause state update narrows the
        captured outer @Int into the @Nat cell; obligated Tier-3 (fresh
        clause scope)."""
        obls = _obligations_of(
            _state_fixture(
                with_clause=" with @Nat = @Int.0",
                body="put(5);\n  nat_to_int(get(()))"),
            "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "tier3"

    def test_resume_argument_narrowing_is_obligated(self) -> None:
        """`resume(@Int.0)` in the get clause — the resume value flows
        into the op's @Nat return; the narrowing is obligated."""
        obls = _obligations_of(
            _state_fixture(resume_arg="@Int.0"), "nat_bind")
        assert len(obls) == 1
        assert obls[0].status == "tier3"
