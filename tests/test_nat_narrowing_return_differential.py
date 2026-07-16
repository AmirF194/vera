"""Verifier<->codegen behavioural differential for #758 — the @Int -> @Nat
narrowing obligation at the RETURN position.

The soundness contract (the return-position dual of the #813 widening
differential): at the function-return coercion slot the verifier's static
`nat_bind` verdict must AGREE with what code generation actually does at run
time —

  * an UNPROVEN narrowing (the value can be negative) leaves the return
    `nat_bind` obligation undischarged — a loud E503 `violated` when Z3
    witnesses a negative input, or `tier3` for an opaque value — and codegen
    MUST emit the return guard, so ``vera run`` with a negative input TRAPS
    rather than storing a negative in the @Nat slot (pre-#758 it returned the
    negative silently: `to_nat(0 - 5)` = -5).
  * a PROVEN narrowing (a `requires`/path-condition bound) discharges the
    return `nat_bind` at Tier 1, and codegen's guard is DEAD — ``vera run``
    returns the value with no trap.

A green per-site unit suite (``test_codegen_nat_guards`` asserts the trap,
``test_verifier_nat_obligations`` asserts the obligation status) can still hide
a desync between the two surfaces — the verifier obligating a site codegen
never guards (an unsound silent negative), or codegen guarding a site the
verifier proved Tier-1 (a spurious trap on a valid value).  This is the
required cross-component differential (project rule): for one corpus run BOTH
sides and compare, so "the verifier obligates this return" is checked against
the actual runtime guard, site for site.
"""

from __future__ import annotations

import tempfile
from pathlib import Path

import pytest

from vera.codegen.api import WasmTrapError

from collections.abc import Iterator
from contextlib import contextmanager

from vera.ast import Program
from vera.checker import CheckArtifacts, typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver, ResolvedModule
from vera.verifier import verify

_KIND = "nat_bind"

# u64.MAX stored in an i64 slot reads back as -1; used by the #984 closure
# controls to prove an @Nat -> @Nat closure return is NOT false-trapped.
U64_MAX = 18446744073709551615


@contextmanager
def _resolved_pipeline(
    source: str,
) -> Iterator[tuple[Program, CheckArtifacts, list[ResolvedModule], str]]:
    """Parse + resolve imports + typecheck *source* through the REAL CLI
    pipeline — a temp file, ``ModuleResolver``, and ``file=`` +
    ``resolved_modules=`` threaded into ``typecheck_with_artifacts`` — then
    yield ``(program, artifacts, resolved, path)`` for the verify / compile
    stages to reuse.

    The 48cbc1f fidelity principle: every side of this differential must
    measure the same pipeline the CLI drives, so a bare in-memory verify (no
    ``file`` / ``resolved_modules``) can never disagree with ``vera run`` for a
    reason the CLI would never hit."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        path = f.name
    try:
        program = parse_to_ast(source)
        resolver = ModuleResolver(_root=Path(path).parent)
        resolved = resolver.resolve_imports(program, Path(path))
        _diags, arts = typecheck_with_artifacts(
            program, source, file=path, resolved_modules=resolved,
        )
        yield program, arts, resolved, path
    finally:
        Path(path).unlink(missing_ok=True)


def _return_nat_bind_statuses(source: str) -> list[str]:
    """The status of every ``nat_bind`` obligation the verifier emits.

    Threads ``file=`` + ``resolved_modules=`` through BOTH typecheck and verify,
    exactly as the ``_run`` / ``_statuses_and_wat`` siblings do (the 48cbc1f
    fidelity principle) — a bare ``verify(program, source)`` skipped the
    side-tables the CLI supplies.  The corpus shapes below have exactly ONE @Nat
    narrowing site — the return slot — so every ``nat_bind`` obligation is the
    return-position one under test (no body-internal narrowing to filter out)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return [o.status for o in result.obligations if o.kind == _KIND]


def _statuses_and_wat(source: str) -> tuple[list[str], str]:
    """Verify AND compile the SAME program in ONE pipeline run, returning the
    ``nat_bind`` statuses and the compiled WAT — so a single call cross-checks
    the verifier's tier verdict against the codegen guard it promises (the
    tier3 quadrant of the differential: verify says ``tier3`` / promises a
    runtime guard, codegen must emit one)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        statuses = [o.status for o in result.obligations if o.kind == _KIND]
        comp = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        return statuses, comp.wat


def _run(source: str, fn: str, arg: int) -> int | None:
    """Compile + execute *fn* with one i64 arg; ``None`` if it traps."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            exec_result = execute(result, fn_name=fn, args=[arg])
        except WasmTrapError:
            return None
        return exec_result.value


def _trap_kind(source: str, fn: str, arg: int) -> str | None:
    """The normalized trap kind for running *fn(arg)*, or ``None`` if no trap
    — so trap assertions can pin the narrowing guard's bare ``unreachable``
    net specifically (the widen dual's convention), not just "some trap"."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            execute(result, fn_name=fn, args=[arg])
        except WasmTrapError as exc:
            return exc.kind
        return None


# (label, source, fn, neg_input) — an @Int -> @Nat narrowing at the return
# position where the value CAN be negative.  The verifier leaves the return
# nat_bind undischarged (not "verified"), and codegen guards it so
# run(neg_input) TRAPS.  A non-negative input passes the guard unchanged.
_UNPROVEN = [
    ("bare_slot", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "f", -5),
    ("if_neg_arm", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { 0 } else { @Int.0 } }
""", "f", -5),
    # The narrowing `_` arm returns the raw @Int scrutinee.  The whole match is
    # target-typed to the @Nat return, so the verifier's side-table reports it
    # @Nat — the return-boundary detection must descend to the arm to catch it,
    # exactly the site codegen's syntactic guard covers (pre-fix this desynced:
    # codegen trapped while the verifier stayed silent).
    ("match_wildcard_arm", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ match @Int.0 { 0 -> 0, _ -> @Int.0 } }
""", "f", -5),
    # A leading `let` statement before the narrowing tail: the return-boundary
    # descent must skip block statements and reach the trailing @Int leaf (the
    # let value flows straight through), matching where codegen guards it.
    ("let_before_tail", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @Int = @Int.0; @Int.0 }
""", "f", -5),
    # A NESTED if-in-if join: the innermost else leaf `@Int.0` is unguarded, so
    # the descent must recurse through both join levels to obligate it — the
    # per-leaf codegen guard covers the same nested leaf (a whole-body-only
    # check would mask it behind the target-typed @Nat join).
    ("nested_if_join", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ if @Int.0 == 0 then { 0 } else { if @Int.0 > 5 then { @Int.0 } else { @Int.0 } } }
""", "f", -5),
    # #983 review — a bare @Nat return through a `type Count = Nat` ALIAS must
    # behave IDENTICALLY to the bare-@Nat `bare_slot` case above: the verifier's
    # 7d gate resolves the alias, and (post-fix) codegen's alias-aware gate
    # guards it too — so the differential holds through the alias.
    ("alias_bare_slot", """
type Count = Nat;
public fn f(@Int -> @Count) requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "f", -5),
]

# (label, source, fn, neg_input, expect) — a PROVEN @Int -> @Nat return
# narrowing: the verifier discharges the return nat_bind at Tier 1, codegen's
# guard is dead, and run returns the value with no trap.
_PROVEN = [
    ("abs_if", """
public fn f(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 } }
""", "f", -5, 5),
    ("requires_bound", """
public fn f(@Int -> @Nat) requires(@Int.0 >= 0) ensures(true) effects(pure)
{ @Int.0 }
""", "f", 5, 5),
]

# (label, source, fn) — the TIER-3 quadrant: an OPAQUE @Int -> @Nat return
# narrowing the solver cannot translate (`float_to_int` parses a machine float,
# which Z3 does not model), so the verifier records the return nat_bind `tier3`
# — a PROMISE that codegen guards it at run time — and codegen MUST emit the
# guard.  (`array_length` is NOT tier3: the verifier models its `>= 0`
# postcondition and proves the narrowing at Tier 1 — so it is a `verified`
# case, not the opaque one this quadrant needs; `float_to_int` is a genuine
# codegen-supported builtin whose result Z3 leaves opaque.)
_TIER3 = [
    ("float_to_int", """
public fn f(@Float64 -> @Nat) requires(true) ensures(true) effects(pure)
{ float_to_int(@Float64.0) }
""", "f"),
]


class TestNatReturnNarrowingDifferential758:
    @pytest.mark.parametrize("label,source,fn,neg", _UNPROVEN,
                             ids=[c[0] for c in _UNPROVEN])
    def test_unproven_return_obligated_and_run_traps(
        self, label: str, source: str, fn: str, neg: int,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        # The verifier obligates the return slot (exactly one narrowing site)...
        assert statuses, f"{label}: no return nat_bind obligation emitted"
        assert all(s != "verified" for s in statuses), (
            f"{label}: an unprovable narrowing must not verify Tier-1: {statuses}"
        )
        # ...and codegen makes good on it: a negative input traps rather than
        # storing a reinterpreted negative in the @Nat slot.
        assert _run(source, fn, neg) is None, (
            f"{label}: the verifier obligated this return, but run({neg}) did "
            f"NOT trap — an unsound silent negative @Nat"
        )
        # A non-negative input takes a non-negative return path, so the guard
        # does NOT trip (it returns some value, not None) — the guard fires only
        # on the bad path, never spuriously on a valid one.
        assert _run(source, fn, 4) is not None, (
            f"{label}: a valid (non-negative) input must pass the guard"
        )

    @pytest.mark.parametrize("label,source,fn,neg,expect", _PROVEN,
                             ids=[c[0] for c in _PROVEN])
    def test_proven_return_verified_and_run_no_trap(
        self, label: str, source: str, fn: str, neg: int, expect: int,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        # The verifier proves the return narrowing at Tier 1...
        assert statuses == ["verified"], f"{label}: {statuses}"
        # ...and codegen's guard is dead — run returns the value, never traps.
        assert _run(source, fn, neg) == expect, (
            f"{label}: verifier proved Tier-1 but run({neg}) trapped or gave "
            f"the wrong value — a spurious trap or a codegen<->verifier desync"
        )

    @pytest.mark.parametrize("label,source,fn", _TIER3,
                             ids=[c[0] for c in _TIER3])
    def test_tier3_return_promised_guard_is_emitted(
        self, label: str, source: str, fn: str,
    ) -> None:
        """The tier-3 quadrant, cross-checked in ONE pipeline run: the verifier
        records the opaque return narrowing ``tier3`` (a runtime-guard promise)
        AND the SAME compiled program carries the codegen guard — so ``tier3``
        can never mean "promised but never emitted" (the alias-blind gate's
        exact soundness gap: verify obligated ``tier3`` while codegen emitted
        nothing through the alias)."""
        statuses, wat = _statuses_and_wat(source)
        assert statuses == ["tier3"], (
            f"{label}: expected a single tier3 return nat_bind, got {statuses}"
        )
        idx = wat.find(f"(func ${fn} ")
        assert idx >= 0, f"{label}: function {fn} not found in WAT"
        end = wat.find("\n  (func ", idx + 1)
        body = wat[idx:end if end >= 0 else len(wat)]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"{label}: the verifier promised a tier3 runtime guard, but codegen "
            f"emitted none:\n{body}"
        )


# ---------------------------------------------------------------------------
# #984 — the @Int -> @Nat narrowing at a LIFTED CLOSURE's return.  The #758
# return nat-bind hole reachable only through `_compile_lifted_closure`: pre-fix
# `fn(@Int -> @Nat) { @Int.0 }` applied to -5 returned -5 through the @Nat slot
# on a verify-clean program (no obligation, no guard).  The closure body is
# opaque to the verifier's SMT layer, so — like the #820 widening dual — the
# return narrowing is obligated SHALLOW-syntactically (always `tier3`, never a
# false Tier-1 / E503) and codegen guards it PER NARROWING LEAF in the lifted
# body (the whole-body wrap would false-trap a legitimate @Nat leaf).  Each
# program wraps the closure in a `mk` producer and a `go` driver that
# `apply_fn`s it, so `_run(source, "go", arg)` exercises the real closure path
# end to end.
# ---------------------------------------------------------------------------

# (label, source, neg_input) — a closure whose return genuinely narrows: the
# verifier records the closure-return nat_bind `tier3` (opaque -> guarded), and
# codegen's per-leaf guard traps on the negative; a non-negative input passes.
_CLOSURE_TRAP = [
    ("closure_bare", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { @Int.0 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5),
    # A per-leaf narrowing: only the else-arm @Int.0 leaf is a genuine narrowing
    # (the then-arm literal 0 is not), so the guard must sit on the else leaf, not
    # wrap the whole body.  -5 routes to else -> traps; +7 routes to then -> 0.
    ("closure_if_else_leaf", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { if @Int.0 >= 0 then { 0 } else { @Int.0 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5),
    # A @Nat-alias return must behave identically to the bare-@Nat case: the
    # verifier's `_is_nat_type` resolves the alias and codegen's alias-aware
    # `_type_expr_base_is_nat` guards it.
    ("closure_alias", """
type Count = Nat;
type F = fn(Int -> Count) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Count) effects(pure) { @Int.0 } }
public fn go(@Int -> @Count) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5),
]

# (label, source, neg_input, expect) — an abs-style closure body: BOTH leaves
# narrow (both guarded; tier3 because the closure is opaque, never proven
# Tier-1), yet the abs logic keeps every returned value non-negative, so the
# live guard never trips — sound over-guarding, no spurious trap.
_CLOSURE_SAFE = [
    ("closure_abs", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { if @Int.0 >= 0 then { @Int.0 } else { 0 - @Int.0 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5, 5),
]

# (label, source, input, expect) — a closure whose return does NOT narrow: no
# closure-return nat_bind obligation, no guard, and no false trap.
_CLOSURE_UNOBLIGATED = [
    # @Nat -> @Nat: the return is already @Nat, so no narrowing; a u64.MAX value
    # (reads as -1 i64) MUST pass through without a guard false-trapping it.
    ("closure_natnat", """
type F = fn(Nat -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { @Nat.0 } }
public fn go(@Nat -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(0); apply_fn(@F.0, @Nat.0) }
""", U64_MAX, -1),
    # @Int -> @Int: no @Nat slot in sight; a negative flows through untouched.
    ("closure_intint", """
type F = fn(Int -> Int) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Int) effects(pure) { @Int.0 } }
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{ let @F = mk(0); apply_fn(@F.0, @Int.0) }
""", -5, -5),
    # An intrinsically-@Nat body (`let @Nat = 5` bound, then returned): the
    # trailing @Nat.0 does not narrow, so the closure-return gate adds NO second
    # guard on top of the already-clean value.
    ("closure_intrinsic_nat", """
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Int -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { let @Nat = 5; @Nat.0 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(@Int.0); apply_fn(@F.0, @Int.0) }
""", -5, 5),
]

# A closure nested inside ANOTHER closure's body — the #985 reporting gap, now
# confirmed for the narrowing direction.
_NESTED_CLOSURE = """
type Inner = fn(Int -> Nat) effects(pure);
type Outer = fn(Int -> Inner) effects(pure);
private fn mk(@Int -> @Outer) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Inner) effects(pure) { fn(@Int -> @Nat) effects(pure) { @Int.0 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @Outer = mk(@Int.0); let @Inner = apply_fn(@Outer.0, @Int.0); apply_fn(@Inner.0, @Int.0) }
"""


class TestClosureReturnNarrowingDifferential984:
    @pytest.mark.parametrize("label,source,neg", _CLOSURE_TRAP,
                             ids=[c[0] for c in _CLOSURE_TRAP])
    def test_closure_narrowing_obligated_tier3_and_run_traps(
        self, label: str, source: str, neg: int,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        # The closure body is opaque, so the return narrowing is obligated
        # shallow-syntactically — exactly ONE tier3 (a runtime-guard promise),
        # NEVER a false Tier-1 "verified" (which would silence a real negative).
        assert statuses == ["tier3"], f"{label}: {statuses}"
        # ...and codegen makes good on the promise: a negative input traps
        # rather than returning it silently through the @Nat slot (the #984 bug).
        kind = _trap_kind(source, "go", neg)
        assert kind == "unreachable", (
            f"{label}: the verifier obligated this closure return, but "
            f"run({neg}) gave trap kind {kind!r} — expected the narrowing "
            f"guard's bare `unreachable` net (None = no trap at all: an "
            f"unsound silent negative @Nat)"
        )
        # ...while a non-negative input passes the per-leaf guard unharmed.
        assert _run(source, "go", 7) is not None, (
            f"{label}: a valid (non-negative) input must pass the guard"
        )

    @pytest.mark.parametrize("label,source,neg,expect", _CLOSURE_SAFE,
                             ids=[c[0] for c in _CLOSURE_SAFE])
    def test_closure_overguard_tier3_but_no_spurious_trap(
        self, label: str, source: str, neg: int, expect: int,
    ) -> None:
        # The closure is opaque, so even a provably-abs body is tier3 (over-
        # guarded, never proven Tier-1)...
        assert _return_nat_bind_statuses(source) == ["tier3"], label
        # ...but every returned value stays non-negative, so the live guard
        # never trips — over-guarding is sound, not a false-positive trap.
        assert _run(source, "go", neg) == expect, (
            f"{label}: run({neg}) trapped or gave the wrong value — a spurious "
            f"trap on a value the abs body keeps non-negative"
        )
        assert _run(source, "go", 5) == 5, f"{label}: +5 path altered"

    @pytest.mark.parametrize("label,source,inp,expect", _CLOSURE_UNOBLIGATED,
                             ids=[c[0] for c in _CLOSURE_UNOBLIGATED])
    def test_closure_non_narrowing_unobligated_and_not_trapped(
        self, label: str, source: str, inp: int, expect: int,
    ) -> None:
        # No @Nat narrowing at the closure return -> the verifier records NO
        # nat_bind, so codegen must emit no guard: the value flows through
        # unchanged.  A false guard on `closure_natnat` would trap a legitimate
        # @Nat above i64.MAX (the widen dual's false-trap hazard).
        assert _return_nat_bind_statuses(source) == [], (
            f"{label}: a non-narrowing closure return must carry no obligation"
        )
        assert _run(source, "go", inp) == expect, (
            f"{label}: the value was altered or trapped — a spurious guard on a "
            f"non-narrowing closure return"
        )

    def test_nested_closure_guarded_by_codegen_but_verifier_underreports_985(
        self,
    ) -> None:
        """A closure nested inside ANOTHER closure's body: codegen guards its
        @Int -> @Nat return (every lifted closure passes through
        ``_compile_lifted_closure``) but the verifier's ``AnonFn`` walk is
        terminal — it does not recurse into the outer closure's body — so the
        nested return narrowing carries NO obligation.  Sound OVER-guarding (an
        extra real trap, never a false proof), but a reporting-completeness gap:
        the narrowing dual of the #985 widening residual.  Pinned so a future
        change that DROPS the guard (unsound silent negative) or that STARTS
        obligating (closing #985) is caught here and this test updated."""
        # The verifier under-reports: no nat_bind for the nested closure return.
        assert _return_nat_bind_statuses(_NESTED_CLOSURE) == [], (
            "nested: an obligation appeared — did #985 close?  Update this test."
        )
        # ...yet codegen still guards it, so a negative traps (sound).
        assert _run(_NESTED_CLOSURE, "go", -5) is None, (
            "nested: codegen guard missing -> a silent negative @Nat"
        )
        assert _run(_NESTED_CLOSURE, "go", 7) is not None, (
            "nested: a valid (non-negative) input must pass the guard"
        )

_CLOSURE_BOUNDARY = """\
type F = fn(Int -> Nat) effects(pure);
private fn mk(@Unit -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Nat) effects(pure) { @Int.0 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(()); apply_fn(@F.0, @Int.0) }
"""

_CLOSURE_REFINED = """\
type Pos = { @Nat | @Nat.0 > 0 };
type F = fn(Int -> Pos) effects(pure);
private fn mk(@Unit -> @F) requires(true) ensures(true) effects(pure)
{ fn(@Int -> @Pos) effects(pure) { if @Int.0 > 0 then { @Int.0 } else { 1 } } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @F = mk(()); apply_fn(@F.0, @Int.0) }
"""


class TestClosureNarrowingBoundary984:
    """Sign-boundary behavior of the closure return guard (`result >= 0`):
    zero must SURVIVE (an off-by-one `i64.le_s` mutant would false-trap it),
    the tightest negative and i64.MIN must trap with the bare `unreachable`
    net.  Behavioral pins — not WAT-string matches — so a guard-comparison
    regression is caught by execution, not by implementation coupling."""

    def test_zero_survives_the_guard(self) -> None:
        assert _run(_CLOSURE_BOUNDARY, "go", 0) == 0

    def test_minus_one_traps(self) -> None:
        assert _trap_kind(_CLOSURE_BOUNDARY, "go", -1) == "unreachable"

    def test_i64_min_traps(self) -> None:
        assert _trap_kind(_CLOSURE_BOUNDARY, "go", -(2 ** 63)) == "unreachable"

    def test_i64_max_passes(self) -> None:
        assert _run(_CLOSURE_BOUNDARY, "go", 2 ** 63 - 1) == 2 ** 63 - 1

    def test_refined_return_single_guard_no_double(self) -> None:
        """A refinement-over-@Nat closure return is guarded EXACTLY ONCE — by
        the #1032 refined-return guard in the lifted body — and the #984
        narrowing gate must NOT add a second sign check on top
        (`_refinement_guard_parts is None` exclusion: removing it compiles a
        redundant `i64.lt_s`; the refinement guard's predicate already
        conjoins the @Nat base's `>= 0`).  Pin by guard counts in the lifted
        closure's WAT, plus behavior: 5 round-trips, 0 takes the clamping arm.
        (Pre-#1032 this pinned ZERO guards of any kind, on the then-false
        assumption that a boundary guard existed at the call/return site.)"""
        statuses, wat = _statuses_and_wat(_CLOSURE_REFINED)
        anon = wat[wat.index("(func $anon_"):]
        depth = 0
        for i, ch in enumerate(anon):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    anon = anon[: i + 1]
                    break
        # Exactly ZERO narrowing sign checks in the lifted body: ANY i64.lt_s
        # here is the #984 leaf gate wrongly firing on a refined return
        # (measured: 0 at head, 1 with the `_refinement_guard_parts is None`
        # exclusion removed) — the refinement guard below uses ge_s/gt_s.
        assert anon.count("i64.lt_s") == 0, (
            f"refined closure return picked up a narrowing guard: "
            f"{anon.count('i64.lt_s')} sign checks in the lifted body"
        )
        # ...and exactly ONE refinement guard: the #1032 return-value check.
        # 0 would be the pre-#1032 silent leak; 2+ would be double-guarding
        # (e.g. the #984 gate un-excluded, or the return guard emitted twice).
        assert anon.count("call $vera.contract_fail") == 1, (
            f"expected exactly one refinement return guard in the lifted "
            f"body, found {anon.count('call $vera.contract_fail')}"
        )
        assert _run(_CLOSURE_REFINED, "go", 5) == 5
        # 0 takes the else arm and returns the clamped 1 — the body never
        # produces a refinement-violating value, so the (now-live) return
        # guard does not trip; the guard-count pins above are what this test
        # exists for.
        assert _run(_CLOSURE_REFINED, "go", 0) == 1


# ---------------------------------------------------------------------------
# #1017 — the @Int -> @Nat narrowing at an apply_fn ARGUMENT position (into the
# closure's @Nat FORMAL), the narrowing dual of the #820 apply_fn @Nat -> @Int
# argument WIDENING.  Pre-fix `apply_fn(clo_with_nat_formal, 0 - 5)` verified
# clean (the verifier's apply_fn branch obligated only the widening direction)
# AND `_translate_apply_fn` emitted only the widen guard — so a provably-
# negative @Int flowed into the @Nat formal with NO obligation and NO runtime
# backstop: a false Tier-1 AND a silent negative (`apply_fn(clo, @Int.0)` on -5
# returned the body value rather than trapping).  The verifier now obligates the
# argument narrowing at its apply_fn branch (mirroring the generic call-argument
# narrowing) and codegen guards the call_indirect argument (mirroring its
# @Int-formal widen guard).  Every closure body below returns a CONSTANT, so the
# ONLY narrowing/guard in play is the ARGUMENT — any trap is the arg guard, not
# a closure-return guard (the #984 corpus above covers that dual).
# ---------------------------------------------------------------------------

# (label, source) — a provably-NEGATIVE apply_fn arg narrowing into a @Nat
# formal: the verifier witnesses the negative constant and reports the arg
# nat_bind `violated` (a loud E503), never the pre-fix empty obligation list.
_APPLYFN_ARG_VIOLATED = [
    # The #1017 issue repro verbatim: a @NatToInt closure PARAMETER (formal
    # recovered from its declared fn-type) applied to a constant-negative arg.
    ("issue_param_closure", """
type NatToInt = fn(Nat -> Int) effects(pure);
private fn f(@NatToInt -> @Int) requires(true) ensures(true) effects(pure)
{ apply_fn(@NatToInt.0, 0 - 5) }
"""),
    # A locally-constructed closure literal applied to a constant-negative arg —
    # the formal is recovered from the inline AnonFn's declared parameter type.
    ("literal_closure_const_neg", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Unit -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, 0 - 5) }
"""),
]

# (label, source, fn) — a RUNTIME @Int argument (unknown sign) narrowing into a
# @Nat formal.  The verifier obligates it (never "verified"), and codegen guards
# the call_indirect argument, so run(-5) TRAPS (pre-fix it silently returned the
# closure body's constant) while run(4) passes the guard.
_APPLYFN_ARG_TRAP = [
    ("runtime_arg", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, @Int.0) }
""", "go"),
]

# (label, source, fn, arg, expect) — a PROVABLY non-negative narrowing (a
# `requires(@Int.0 >= 0)` bound): the verifier discharges the arg nat_bind at
# Tier 1, codegen's guard is dead, and run returns the body constant, no trap.
_APPLYFN_ARG_PROVEN = [
    ("requires_bound", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Int -> @Nat) requires(@Int.0 >= 0) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, @Int.0) }
""", "go", 4, 5),
]

# (label, source, fn, arg, expect) — a @Nat argument into a @Nat formal: NO
# narrowing, so no obligation and no guard.  A u64.MAX value (reads as -1 in the
# i64 slot) must pass through unguarded — the narrowing-side dual of the widen
# guard's false-trap hazard.
_APPLYFN_ARG_UNOBLIGATED = [
    ("nat_arg_nat_formal", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Nat -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, @Nat.0) }
""", "go", U64_MAX, 5),
]

# (label, source, fn) — the TIER-3 quadrant: an OPAQUE @Int argument the solver
# cannot translate (`float_to_int` parses a machine float, which Z3 does not
# model) narrowing into a @Nat formal, so the verifier records the arg nat_bind
# `tier3` — a PROMISE that codegen guards it at run time — and codegen MUST emit
# the guard.  Directly exercises the `guarded=True` deferral path (the crux of
# the cross-component soundness argument); the mirror of the #758 return `_TIER3`
# quadrant.  Not run (the int-arg `_run` helper cannot drive a @Float64 param).
_APPLYFN_ARG_TIER3 = [
    ("opaque_float_arg", """
type NatToNat = fn(Nat -> Nat) effects(pure);
private fn mk(@Unit -> @NatToNat) requires(true) ensures(true) effects(pure)
{ fn(@Nat -> @Nat) effects(pure) { 5 } }
public fn go(@Float64 -> @Nat) requires(true) ensures(true) effects(pure)
{ let @NatToNat = mk(()); apply_fn(@NatToNat.0, float_to_int(@Float64.0)) }
""", "go"),
]


class TestApplyFnArgNarrowingDifferential1017:
    @pytest.mark.parametrize("label,source", _APPLYFN_ARG_VIOLATED,
                             ids=[c[0] for c in _APPLYFN_ARG_VIOLATED])
    def test_provably_negative_arg_obligated_violated(
        self, label: str, source: str,
    ) -> None:
        # The verifier now emits the argument nat_bind and Z3 witnesses the
        # negative constant, so it is `violated` (E503) — never the pre-fix
        # empty obligation list (the #1017 silent Tier-1 pass).
        statuses = _return_nat_bind_statuses(source)
        assert statuses == ["violated"], (
            f"{label}: expected one violated arg nat_bind, got {statuses} "
            f"(pre-fix: [] — the #1017 false Tier-1)"
        )

    @pytest.mark.parametrize("label,source,fn", _APPLYFN_ARG_TRAP,
                             ids=[c[0] for c in _APPLYFN_ARG_TRAP])
    def test_runtime_arg_obligated_and_run_traps(
        self, label: str, source: str, fn: str,
    ) -> None:
        statuses = _return_nat_bind_statuses(source)
        assert statuses and all(s != "verified" for s in statuses), (
            f"{label}: an unprovable arg narrowing must be obligated, not "
            f"verified: {statuses}"
        )
        # ...and codegen makes good on it: a negative argument traps at the
        # call_indirect boundary rather than entering the @Nat formal silently.
        assert _trap_kind(source, fn, -5) == "unreachable", (
            f"{label}: the verifier obligated this arg, but run(-5) did not trap "
            f"with the narrowing guard's bare `unreachable` net — a silent "
            f"negative @Nat (the #1017 hole)"
        )
        # ...while a non-negative argument passes the guard unharmed.
        assert _run(source, fn, 4) is not None, (
            f"{label}: a valid (non-negative) argument must pass the guard"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect", _APPLYFN_ARG_PROVEN,
                             ids=[c[0] for c in _APPLYFN_ARG_PROVEN])
    def test_proven_arg_verified_and_run_no_trap(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A requires-bounded argument proves the narrowing at Tier 1 (exactly one
        # nat_bind, discharged)...
        assert _return_nat_bind_statuses(source) == ["verified"], (
            f"{label}: a requires-bounded arg narrowing must prove Tier-1"
        )
        # ...and codegen's guard is dead — run returns the value, never traps.
        assert _run(source, fn, arg) == expect, (
            f"{label}: verifier proved Tier-1 but run({arg}) trapped or gave the "
            f"wrong value — a spurious trap or codegen<->verifier desync"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect",
                             _APPLYFN_ARG_UNOBLIGATED,
                             ids=[c[0] for c in _APPLYFN_ARG_UNOBLIGATED])
    def test_nat_arg_unobligated_and_not_trapped(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A @Nat->@Nat argument does not narrow -> no obligation, no guard: the
        # value flows through unchanged.  A false guard here would trap a
        # legitimate @Nat above i64.MAX (the widen dual's false-trap hazard).
        assert _return_nat_bind_statuses(source) == [], (
            f"{label}: a @Nat->@Nat argument does not narrow — no obligation"
        )
        assert _run(source, fn, arg) == expect, (
            f"{label}: a non-narrowing @Nat argument was altered or trapped — a "
            f"spurious guard (u64.MAX reads as -1 in the i64 slot)"
        )

    @pytest.mark.parametrize("label,source,fn", _APPLYFN_ARG_TIER3,
                             ids=[c[0] for c in _APPLYFN_ARG_TIER3])
    def test_tier3_arg_promised_guard_is_emitted(
        self, label: str, source: str, fn: str,
    ) -> None:
        """The tier-3 quadrant, cross-checked in ONE pipeline run: an opaque @Int
        argument the solver cannot translate records the arg narrowing `tier3` (a
        runtime-guard promise) AND the SAME compiled program carries the codegen
        guard in the applying function — so `guarded=True` can never mean
        "promised but never emitted" (the false-tier3 soundness hole this whole
        differential exists to catch)."""
        statuses, wat = _statuses_and_wat(source)
        assert statuses == ["tier3"], (
            f"{label}: expected a single tier3 arg nat_bind, got {statuses}"
        )
        idx = wat.find(f"(func ${fn} ")
        assert idx >= 0, f"{label}: function {fn} not found in WAT"
        end = wat.find("\n  (func ", idx + 1)
        body = wat[idx:end if end >= 0 else len(wat)]
        assert "i64.lt_s" in body and "unreachable" in body, (
            f"{label}: the verifier promised a tier3 runtime guard, but codegen "
            f"emitted none in {fn}:\n{body}"
        )


# ---------------------------------------------------------------------------
# #1024 — the refinement-PREDICATE narrowing at an apply_fn ARGUMENT position
# (into the closure's REFINED formal), the refinement dual of the #1017 @Nat
# argument narrowing.  Pre-fix `apply_fn(clo, 0)` where the closure formal is
# `{ @Nat | @Nat.0 > 0 }` verified CLEAN and ran silently (returned the body
# value): the #1017 apply_fn arm obligated the formal as a bare @Nat — proving
# only the base's `>= 0` (which 0 satisfies) — so the STRICT `> 0` predicate was
# unchecked (a false Tier-1), and `_compile_lifted_closure` emitted no
# param-entry guard.  The verifier now obligates the argument against the FULL
# predicate at its apply_fn branch (refined-FIRST, ahead of the #1017 @Nat arm,
# mirroring the generic call-argument path) and codegen guards each refined
# closure formal at the lifted body's prologue (`_compile_lifted_closure`,
# mirroring `_compile_fn`'s refined-param guard).  The named-call equivalent
# (`take(0)` into a `@Pos` param) already behaved this way — E505 at verify, a
# `contract_violation` trap at run — so these pin the apply_fn path to the same
# contract.  The discriminating input is 0: it clears the #1017 `>= 0` backstop
# but violates `> 0`, so any test that traps/obligates 0 is exercising the
# refined predicate specifically, not the @Nat base.
# ---------------------------------------------------------------------------

_REFINE_KIND = "refine_bind"
_POS = "type Pos = { @Nat | @Nat.0 > 0 };"


def _refine_bind_statuses(source: str) -> list[str]:
    """The status of every ``refine_bind`` obligation the verifier emits — the
    refinement-predicate analogue of :func:`_return_nat_bind_statuses` (#1024).

    Threads ``file=`` + ``resolved_modules=`` through BOTH typecheck and verify
    (the 48cbc1f fidelity principle).  The corpus shapes below apply a closure
    whose formal is a refinement, so the only ``refine_bind`` site is the
    apply_fn argument under test (the closure body returns a constant, and a
    closure-param declaration raises no narrowing obligation of its own)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return [o.status for o in result.obligations if o.kind == _REFINE_KIND]


def _trap_message(source: str, fn: str, arg: int) -> str | None:
    """The trap MESSAGE for running *fn(arg)*, or ``None`` if it does not trap —
    so a refinement-guard trap can be pinned by its ``Refinement violation``
    message text, not merely "some trap" (#1024, the refined dual of
    :func:`_trap_kind`)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = codegen_compile(
            program, source=source, file=path, resolved_modules=resolved,
            expr_semantic_types=arts.expr_semantic_types,
        )
        try:
            execute(result, fn_name=fn, args=[arg])
        except WasmTrapError as exc:
            return str(exc)
        return None


# (label, source) — a provably-refinement-violating CONSTANT arg into a refined
# closure formal: the verifier witnesses the constant and reports the argument
# refine_bind `violated` (a loud E505), never the pre-fix empty list (the #1024
# false Tier-1, where the #1017 @Nat arm silently proved only `>= 0`).
_APPLYFN_REFINED_ARG_VIOLATED = [
    # The #1024 issue repro: a @PosToInt closure PARAMETER (refined formal
    # recovered from its declared fn-type alias) applied to a constant 0, which
    # satisfies the @Nat base's `>= 0` but violates the strict `> 0`.
    ("issue_param_closure", f"""
{_POS}
type PosToInt = fn(Pos -> Int) effects(pure);
private fn f(@PosToInt -> @Int) requires(true) ensures(true) effects(pure)
{{ apply_fn(@PosToInt.0, 0) }}
"""),
    # A locally-constructed closure literal applied to a constant 0 — the refined
    # formal is recovered from the inline AnonFn's declared parameter type.
    ("literal_closure_zero", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Unit -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, 0) }}
"""),
]

# (label, source, fn) — a RUNTIME arg (unknown sign) narrowing into a refined
# formal.  The verifier obligates it (never "verified"), and codegen guards the
# closure's refined formal at its prologue, so run(0) — which clears `>= 0` but
# fails `> 0` — TRAPS with a `contract_violation` Refinement-violation message
# (pre-fix it silently returned the body constant) while run(7) passes.
_APPLYFN_REFINED_ARG_TRAP = [
    ("runtime_arg", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, @Int.0) }}
""", "go"),
]

# (label, source, fn, arg, expect) — a PROVEN refined arg narrowing: a constant
# satisfying the predicate, or a `requires`-bounded arg, discharges the refine
# _bind at Tier 1, codegen's guard is dead, and run returns the body value with
# no trap.  `const_satisfying` is the #1024 c2 healthy pin (arg 5 > 0, body 42).
_APPLYFN_REFINED_ARG_PROVEN = [
    ("const_satisfying", f"""
{_POS}
type PosToInt = fn(Pos -> Int) effects(pure);
private fn mk(@Unit -> @PosToInt) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Int) effects(pure) {{ 42 }} }}
public fn go(@Int -> @Int) requires(true) ensures(true) effects(pure)
{{ let @PosToInt = mk(()); apply_fn(@PosToInt.0, 5) }}
""", "go", 0, 42),
    ("requires_bound", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Int -> @Nat) requires(@Int.0 > 0) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, @Int.0) }}
""", "go", 7, 5),
]

# (label, source, fn, arg, expect) — a @Pos arg into a @Pos formal: the source
# already carries the EXACT refinement (base AND predicate), so
# `_narrows_into_refined` does not fire — no refine_bind, no guard, the value
# flows through.  Guards against the refined-first arm over-firing on a value
# whose refinement was already discharged where it was produced.
_APPLYFN_REFINED_ARG_UNOBLIGATED = [
    ("pos_arg_pos_formal", f"""
{_POS}
type PosToNat = fn(Pos -> Nat) effects(pure);
private fn mk(@Unit -> @PosToNat) requires(true) ensures(true) effects(pure)
{{ fn(@Pos -> @Nat) effects(pure) {{ 5 }} }}
public fn go(@Pos -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @PosToNat = mk(()); apply_fn(@PosToNat.0, @Pos.0) }}
""", "go", 7, 5),
]


class TestApplyFnArgRefinedNarrowing1024:
    @pytest.mark.parametrize("label,source", _APPLYFN_REFINED_ARG_VIOLATED,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_VIOLATED])
    def test_provably_violating_arg_obligated_violated(
        self, label: str, source: str,
    ) -> None:
        # The verifier now emits the argument refine_bind and Z3 witnesses the
        # violating constant, so it is `violated` (E505) — never the pre-fix
        # empty list (the #1024 false Tier-1).  0 clears the @Nat base's `>= 0`,
        # so ONLY the refined-first arm (the FULL predicate) catches it — the
        # #1017 @Nat arm's `>= 0` alone would have proved it "verified".
        statuses = _refine_bind_statuses(source)
        assert statuses == ["violated"], (
            f"{label}: expected one violated arg refine_bind, got {statuses} "
            f"(pre-fix: [] — the #1024 false Tier-1)"
        )

    @pytest.mark.parametrize("label,source,fn", _APPLYFN_REFINED_ARG_TRAP,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_TRAP])
    def test_runtime_arg_obligated_and_run_traps(
        self, label: str, source: str, fn: str,
    ) -> None:
        statuses = _refine_bind_statuses(source)
        assert statuses and all(s != "verified" for s in statuses), (
            f"{label}: an unprovable refined arg narrowing must be obligated, "
            f"not verified: {statuses}"
        )
        # The crux of #1024: 0 clears the @Nat base's `>= 0` but fails the strict
        # `> 0`, so the closure's refined-formal prologue guard must trap it — the
        # #1017 `>= 0` backstop alone would let it through silently.
        assert _trap_kind(source, fn, 0) == "contract_violation", (
            f"{label}: run(0) did not trap at the closure's refined-formal guard "
            f"— the strict predicate `> 0` is unguarded (the #1024 hole)"
        )
        assert "Refinement violation" in (_trap_message(source, fn, 0) or ""), (
            f"{label}: the trap did not carry a refinement-violation message"
        )
        # ...while a value satisfying the predicate passes the guard unharmed.
        assert _run(source, fn, 7) is not None, (
            f"{label}: a valid (> 0) argument must pass the guard"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect",
                             _APPLYFN_REFINED_ARG_PROVEN,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_PROVEN])
    def test_proven_arg_verified_and_run_no_trap(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A constant satisfying the predicate, or a `requires`-bounded arg, proves
        # the narrowing at Tier 1 (exactly one refine_bind, discharged)...
        assert _refine_bind_statuses(source) == ["verified"], (
            f"{label}: a provable refined arg narrowing must prove Tier-1"
        )
        # ...and codegen's guard is dead — run returns the value, never traps.
        assert _run(source, fn, arg) == expect, (
            f"{label}: verifier proved Tier-1 but run({arg}) trapped or gave the "
            f"wrong value — a spurious trap or codegen<->verifier desync"
        )

    @pytest.mark.parametrize("label,source,fn,arg,expect",
                             _APPLYFN_REFINED_ARG_UNOBLIGATED,
                             ids=[c[0] for c in _APPLYFN_REFINED_ARG_UNOBLIGATED])
    def test_matching_refined_arg_unobligated_and_not_trapped(
        self, label: str, source: str, fn: str, arg: int, expect: int,
    ) -> None:
        # A @Pos arg into a @Pos formal already carries the exact refinement, so
        # `_narrows_into_refined` does not fire — no obligation, no guard: the
        # value flows through unchanged (a spurious guard would re-check a value
        # the source already established, and could false-trap).
        assert _refine_bind_statuses(source) == [], (
            f"{label}: a @Pos->@Pos argument does not narrow — no obligation"
        )
        assert _run(source, fn, arg) == expect, (
            f"{label}: a non-narrowing refined argument was altered or trapped"
        )


# ---------------------------------------------------------------------------
# #1032 — the refinement-predicate narrowing at a LIFTED CLOSURE's RETURN, the
# return-side dual of the #1024 formal narrowing above (found while fixing it).
# Pre-fix `fn(@Int -> @Pos) { @Int.0 }` (Pos = `{ @Nat | @Nat.0 > 0 }`) applied
# to -5 or 0 returned the violating value through the refined slot on a
# verify-CLEAN program: the verifier's AnonFn walk had widen (#820) and
# bare-@Nat narrow (#984) arms but no refined arm, and `_compile_lifted_closure`
# guarded the @Nat/@Int returns but not the refinement's predicate — while the
# #984 leaf-guard gate excluded refinements on the (then-false) assumption that
# "the refinement's own boundary guard lives at the call/return boundary".  The
# verifier now records the refined closure return `tier3` guarded (the closure
# body is opaque to SMT — same shallow-syntactic, never-false-Tier-1 treatment
# as the #820/#984 arms) and codegen guards the lifted body's return value,
# mirroring the named path's refined-return guard (`_compile_postconditions`).
# 0 is the discriminating input again: it clears any `>= 0` backstop but
# violates the strict `> 0`.
# ---------------------------------------------------------------------------

_CLOSURE_REFINED_RET_LEAK = f"""
{_POS}
type F = fn(Int -> Pos) effects(pure);
private fn mk(@Unit -> @F) requires(true) ensures(true) effects(pure)
{{ fn(@Int -> @Pos) effects(pure) {{ @Int.0 }} }}
public fn go(@Int -> @Nat) requires(true) ensures(true) effects(pure)
{{ let @F = mk(()); apply_fn(@F.0, @Int.0) }}
"""


class TestClosureRefinedReturn1032:
    def test_refined_return_obligated_tier3(self) -> None:
        # The closure body is opaque to the SMT layer, so the refined return is
        # obligated shallow-syntactically — exactly ONE tier3 refine_bind (a
        # runtime-guard promise), NEVER a false Tier-1 and never the pre-fix
        # empty list (no obligation at all: the #1032 hole).
        statuses = _refine_bind_statuses(_CLOSURE_REFINED_RET_LEAK)
        assert statuses == ["tier3"], (
            f"expected one tier3 closure-return refine_bind, got {statuses} "
            f"(pre-fix: [] — the #1032 silent clean verify)"
        )

    @pytest.mark.parametrize("bad", [-5, 0], ids=["neg", "zero"])
    def test_violating_return_traps(self, bad: int) -> None:
        # ...and codegen makes good on the promise: a body value violating the
        # predicate traps at the closure's return guard with the refinement
        # message (pre-fix it flowed out silently).  0 is the crux: it clears
        # the @Nat base's `>= 0`, so only the FULL predicate catches it.
        kind = _trap_kind(_CLOSURE_REFINED_RET_LEAK, "go", bad)
        assert kind == "contract_violation", (
            f"run({bad}) gave trap kind {kind!r} — expected the refinement "
            f"return guard (None = no trap: the #1032 silent leak)"
        )
        msg = _trap_message(_CLOSURE_REFINED_RET_LEAK, "go", bad) or ""
        assert "Refinement violation" in msg and "return value" in msg, (
            f"trap message did not name the refined return: {msg!r}"
        )

    def test_satisfying_return_passes_guard(self) -> None:
        # A body value satisfying the predicate passes the guard unharmed.
        assert _run(_CLOSURE_REFINED_RET_LEAK, "go", 5) == 5

    def test_healthy_refined_return_tier3_and_no_trap(self) -> None:
        # The always-satisfying body (`if @Int.0 > 0 then { @Int.0 } else
        # { 1 }`): still tier3 (the closure is opaque — over-guarded, never
        # proven Tier-1, matching the #984 `_CLOSURE_SAFE` philosophy), verify
        # stays non-erroring, and the live guard never trips.
        assert _refine_bind_statuses(_CLOSURE_REFINED) == ["tier3"], (
            "a healthy refined closure return must be an honest tier3, "
            "never E505-violated"
        )
        assert _run(_CLOSURE_REFINED, "go", 5) == 5
        assert _run(_CLOSURE_REFINED, "go", 0) == 1


_CLOSURE_REFINED_STR_RET = """\
type NonEmptyStr = { @String | string_length(@String.0) > 0 };
type IntToStr = fn(Int -> NonEmptyStr) effects(pure);

private fn call_it(@IntToStr, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NonEmptyStr = apply_fn(@IntToStr.0, @Int.0);
  string_length(@NonEmptyStr.0)
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  call_it(fn(@Int -> @NonEmptyStr) effects(pure) {
    if @Int.0 > 0 then { "vera" } else { "" }
  }, @Int.0)
}
"""

_CLOSURE_REFINED_STR_FORMAL = """\
type NonEmptyStr = { @String | string_length(@String.0) > 0 };
type StrToInt = fn(NonEmptyStr -> Int) effects(pure);

private fn call_it(@StrToInt, @String -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@StrToInt.0, @String.0)
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then {
    call_it(fn(@NonEmptyStr -> @Int) effects(pure) {
      string_length(@NonEmptyStr.0)
    }, "abc")
  } else {
    call_it(fn(@NonEmptyStr -> @Int) effects(pure) {
      string_length(@NonEmptyStr.0)
    }, "")
  }
}
"""


class TestClosureRefinedPair1032:
    """The i32_pair (String/Array) halves of the #1032/#1024 closure guards.

    A pair value is (ptr, len) on the WASM stack; the guards must save BOTH
    halves, run the predicate over the ptr (`string_length` reads the length
    from memory, as the named-function pair guard does), and re-push in the
    right order — an ordering bug would corrupt the value or read garbage.
    The scalar tests above cannot see any of that, so the pair paths carry
    their own end-to-end pins.
    """

    def test_pair_return_obligated_and_guarded(self) -> None:
        # Verifier half: the refined String RETURN records the same honest
        # guarded tier3 as the scalar shape.
        statuses = _refine_bind_statuses(_CLOSURE_REFINED_STR_RET)
        assert statuses == ["tier3"], (
            f"expected one tier3 pair-return refine_bind, got {statuses}"
        )
        # Codegen half: the empty string violates `string_length > 0` at the
        # closure's return guard...
        kind = _trap_kind(_CLOSURE_REFINED_STR_RET, "go", 0)
        assert kind == "contract_violation", (
            f"go(0) gave trap kind {kind!r} — the pair return guard must trap "
            f"an empty NonEmptyStr (None = the value leaked through)"
        )
        # ...and a satisfying value survives the save-guard-reload INTACT:
        # length 4 proves the (ptr, len) pair was re-pushed unharmed.
        assert _run(_CLOSURE_REFINED_STR_RET, "go", 5) == 4

    def test_pair_formal_obligated_and_guarded(self) -> None:
        # The argument-side (#1024) pair dual: a refined String FORMAL through
        # apply_fn — entry guard traps the empty string, passes "abc" with the
        # value intact (length 3 read through the guarded param).
        statuses = _refine_bind_statuses(_CLOSURE_REFINED_STR_FORMAL)
        assert statuses == ["tier3"], (
            f"expected one tier3 pair-formal refine_bind, got {statuses}"
        )
        kind = _trap_kind(_CLOSURE_REFINED_STR_FORMAL, "go", 0)
        assert kind == "contract_violation", (
            f"go(0) gave trap kind {kind!r} — the pair entry guard must trap "
            f"an empty NonEmptyStr argument"
        )
        assert _run(_CLOSURE_REFINED_STR_FORMAL, "go", 1) == 3


_REFINED_NONPLAIN_PRELUDE = """\
type NEPosArr = { @Array<{ @Int | @Int.0 > 0 }> | array_length(@Array<{ @Int | @Int.0 > 0 }>.0) > 0 };
"""

_NONPLAIN_CLOSURE_RET = _REFINED_NONPLAIN_PRELUDE + """\
type MK = fn(Array<{ @Int | @Int.0 > 0 }> -> NEPosArr) effects(pure);

public fn go(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @MK = fn(@Array<{ @Int | @Int.0 > 0 }> -> @NEPosArr) effects(pure) {
    @Array<{ @Int | @Int.0 > 0 }>.0
  };
  let @Array<{ @Int | @Int.0 > 0 }> = apply_fn(@MK.0, []);
  array_length(@Array<{ @Int | @Int.0 > 0 }>.0)
}
"""

_NONPLAIN_CLOSURE_FORMAL = _REFINED_NONPLAIN_PRELUDE + """\
type TK = fn(NEPosArr -> Nat) effects(pure);

public fn go(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @TK = fn(@NEPosArr -> @Nat) effects(pure) {
    array_length(@NEPosArr.0)
  };
  apply_fn(@TK.0, [])
}
"""

_NONPLAIN_NAMED_FORMAL = _REFINED_NONPLAIN_PRELUDE + """\
private fn take(@NEPosArr -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@NEPosArr.0)
}

public fn go(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  take([])
}
"""

_NONPLAIN_NAMED_RET = _REFINED_NONPLAIN_PRELUDE + """\
public fn mk(@Array<{ @Int | @Int.0 > 0 }> -> @NEPosArr)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<{ @Int | @Int.0 > 0 }>.0
}
"""


class TestRefinedNonPlainBaseDisclosure1036:
    """A refinement base with a NON-PLAIN type argument (a nested refinement
    or fn type, e.g. `Array<{ @Int | ... }>`) gets NO codegen guard at any
    boundary — `_refinement_guard_parts` cannot spell the binder slot and
    bails (#1036).  The verifier's `guarded=` must say so: these obligations
    record `tier3_unguarded` (E506 disclosure, excluded from the runtime
    totals), never a guarded `tier3` promise the runtime does not keep
    (PR #1034 adversarial review: an empty array flowed through a
    NonEmpty-refined closure boundary silently while verify claimed a
    runtime check).
    """

    @pytest.mark.parametrize(
        ("src", "site"),
        [
            (_NONPLAIN_CLOSURE_RET, "closure return"),
            (_NONPLAIN_CLOSURE_FORMAL, "closure argument"),
            (_NONPLAIN_NAMED_FORMAL, "call argument"),
            (_NONPLAIN_NAMED_RET, "return type"),
        ],
        ids=["closure-ret", "closure-formal", "named-formal", "named-ret"],
    )
    def test_nonplain_base_records_unguarded(self, src: str, site: str) -> None:
        statuses = _refine_bind_statuses(src)
        assert statuses and all(s == "tier3_unguarded" for s in statuses), (
            f"a non-plain-arg refined {site} has no codegen guard — expected "
            f"only tier3_unguarded disclosures, got {statuses} (a 'tier3' here "
            f"is an unfulfilled runtime-guard promise, #1036)"
        )

    def test_plain_base_still_promises_guard(self) -> None:
        # The control: a PLAIN NamedType base keeps its honest guarded tier3
        # (the closure guards fire for these — pinned by the classes above).
        assert _refine_bind_statuses(_CLOSURE_REFINED_RET_LEAK) == ["tier3"]


def _obligation_kinds_statuses(source: str) -> set[tuple[str, str]]:
    """Every (kind, status) pair in the verifier's obligation stream — for
    intersection shapes where ONE value carries obligations of two kinds
    (a refinement over `@Int` receiving an intrinsically-`@Nat` value gets
    both the predicate obligation and the widen obligation)."""
    with _resolved_pipeline(source) as (program, arts, resolved, path):
        result = verify(
            program, source, file=path, resolved_modules=resolved,
            expr_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        return {
            (o.kind, o.status) for o in result.obligations
            if o.kind in (_REFINE_KIND, "nat_to_int_coerce", "int_widen")
        }


_CAP_RET_INTERSECTION = """\
type Cap = { @Int | @Int.0 < 100 };
type F = fn(Nat -> Cap) effects(pure);

public fn go(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Nat -> @Cap) effects(pure) { @Nat.0 };
  apply_fn(@F.0, @Nat.0)
}
"""

_CAP_FORMAL_INTERSECTION = """\
type Cap = { @Int | @Int.0 < 100 };
type F = fn(Cap -> Int) effects(pure);

public fn go(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Cap -> @Int) effects(pure) { @Cap.0 };
  apply_fn(@F.0, @Nat.0)
}
"""


class TestRefinedOverIntWidenIntersection:
    """A refinement OVER `@Int` receiving an intrinsically-`@Nat` value is an
    INTERSECTION: codegen emits BOTH the refinement guard (the predicate) and
    the #820 widen guard (`value < 0` = a u64 above i64.MAX reinterpreted) —
    the predicate may not imply fit-in-i64 (`< 100` is SATISFIED by a
    reinterpreted negative), so the widen guard is not subsumable.  The
    obligation stream must describe both guards (PR #1034 review): the
    refined-first arm records the predicate obligation AND the widen
    obligation, never an either/or.
    """

    def test_refined_int_return_with_nat_body_records_both(self) -> None:
        kinds = _obligation_kinds_statuses(_CAP_RET_INTERSECTION)
        assert (_REFINE_KIND, "tier3") in kinds, kinds
        assert any(k != _REFINE_KIND and s == "tier3" for k, s in kinds), (
            f"the #820 widen guard codegen emits for this return has no "
            f"obligation describing it — got only {kinds}"
        )

    def test_refined_int_formal_with_nat_arg_records_both(self) -> None:
        # The formal side discharges via full SMT (unlike the opacity-shallow
        # return), so the refine_bind here is a correct E505 `violated` — an
        # unconstrained @Nat can exceed the `< 100` predicate.  The pin is
        # the WIDEN kind's presence: the call-site widen guard codegen emits
        # must have an obligation describing it, whatever the predicate
        # obligation resolved to.
        kinds = _obligation_kinds_statuses(_CAP_FORMAL_INTERSECTION)
        assert any(k == _REFINE_KIND for k, _ in kinds), kinds
        assert any(
            k != _REFINE_KIND and s in ("tier3", "verified")
            for k, s in kinds
        ), (
            f"the #820 call-site widen guard for this formal has no "
            f"obligation describing it — got only {kinds}"
        )

    def test_intersection_runtime_behavior_pinned(self) -> None:
        # The guards themselves: a satisfying value passes intact; a value
        # violating the predicate traps at the refinement guard.  (The widen
        # guard's own firing needs a u64 above i64.MAX and is pinned by the
        # #820 suites; here we pin that adding the obligation changed no
        # runtime behavior.)
        assert _run(_CAP_RET_INTERSECTION, "go", 5) == 5
        kind = _trap_kind(_CAP_RET_INTERSECTION, "go", 150)
        assert kind == "contract_violation", kind
