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
        interior codegen guard (verified by the run-trap differential
        below)."""
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
