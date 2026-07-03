"""Regression tests for #912 — a composite (ADT / Option / Tuple) equality in
``ensures`` position must lower its RUNTIME check to STRUCTURAL equality, so a
postcondition ``vera verify`` proves at Tier 1 does not spuriously TRAP at run.

The bug (SEVERE — a proved postcondition traps on itself):

    private data Box { MkBox(Int) }
    private fn mk(@Int -> @Box)
      requires(true) ensures(@Box.result == MkBox(@Int.0)) effects(pure)
    { MkBox(@Int.0) }

``vera check`` OK; ``vera verify`` OK ("verified (Tier 1)"); ``vera run`` → exit
1 ``Postcondition violation in mk``.  The postcondition is TRUE — the result IS
``MkBox(@Int.0)`` — and Z3 proves it structurally, but codegen lowered the
composite ``==`` in the runtime postcondition check to a raw ``i32.eq`` (a
*pointer* compare).  The freshly-built ``MkBox(@Int.0)`` return value and the
freshly-built ``MkBox(@Int.0)`` contract operand are structurally equal but live
at different heap addresses, so ``i32.eq`` returns false → a spurious trap on a
proved contract.

Root cause: the ``ResultRef`` operand of ``==`` (``@Box.result``) resolved to a
``None`` Vera type via ``_infer_vera_type`` (it was in that walker's
"cannot occur" set), so the ADT-structural-``==`` dispatch in
``vera/wasm/operators.py`` was skipped (its ``lv is not None and lv_base in
adt_type_names`` guard) and the code fell through to the scalar ``i32.eq``
default.  ``_infer_expr_wasm_type`` already handled ``ResultRef`` (#891), so the
*width* was right (i32 vs i32) — only the *Vera-type* dispatch was missing.

Fix: ``_infer_vera_type`` resolves a ``ResultRef`` to its declared ``@Type``
(reusing the ``SlotRef`` logic), so a composite ``@T.result == ctor``
postcondition routes through the SAME structural-``==`` codegen that ``eq(a, b)``
and ``ctor == ctor`` already use — which recurses fields and works at runtime.

Written test-first: every RED test below TRAPS on the pre-fix compiler with a
``Postcondition violation`` and passes after the fix.  The NEGATIVE-CONTROL
tests pin the soundness invariant: a genuinely-FALSE composite postcondition
must STILL be rejected by ``vera verify`` (E500) AND trap at runtime — the fix
must make true composite postconditions pass, never false ones.
"""

from __future__ import annotations

import tempfile

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import CompileResult, compile as codegen_compile, execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_file, parse_to_ast
from vera.transform import transform
from vera.verifier import VerifyResult, verify


# ---------------------------------------------------------------------
# Helpers (mirror tests/test_eq_contract_874.py)
# ---------------------------------------------------------------------

def _compile(source: str) -> CompileResult:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    tree = parse_file(path)
    ast = transform(tree)
    return codegen_compile(ast, source=source, file=path)


def _run(source: str, fn: str | None = None) -> int:
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected compile errors: {errors}"
    exec_result = execute(result, fn_name=fn)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _verify(source: str) -> VerifyResult:
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    return verify(
        ast, source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


# Program bodies -------------------------------------------------------

_BOX = """
private data Box {{ MkBox(Int) }}
private fn mk(@Int -> @Box)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  MkBox(@Int.0)
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ MkBox(@Int) -> @Int.0 }}
}}
"""

_OPTION = """
private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  Some(@Int.0)
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ Some(@Int) -> @Int.0, None -> 0 }}
}}
"""

# NB: no `Tuple` case here.  `Tuple` is intentionally NOT `Eq`-derivable
# (spec §9.8 / std-lib §"Eq": Array/Map/handle/tuple fields are non-derivable,
# rejected with E613), so a `Tuple<...> == Tuple<...>` postcondition is an
# invalid program the checker *should* reject — a distinct, pre-existing gap
# (the E613 Eq-derivability gate is not enforced in contract position; a
# `Tuple` `==` in an `ensures` therefore reaches codegen and raises an uncaught
# `AdtEqNotDerivableError`, on the base compiler too).  That is out of scope for
# #912, which is about *Eq-derivable* composites (user ADTs, Option, nested)
# trapping despite being provable.

_NESTED = """
private data Inner {{ MkInner(Int) }}
private data Outer {{ MkOuter(Inner) }}
private fn mk(@Int -> @Outer)
  requires(true)
  ensures({ensures})
  effects(pure)
{{
  MkOuter(MkInner(@Int.0))
}}
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(5) {{ MkOuter(@Inner) -> match @Inner.0 {{ MkInner(@Int) -> @Int.0 }} }}
}}
"""


# =====================================================================
# RED: a TRUE composite postcondition must run without a spurious trap
# =====================================================================

class TestCompositePostconditionRuns912:
    def test_adt_result_eq_ctor_runs(self) -> None:
        # The canonical #912 repro: `@Box.result == MkBox(@Int.0)`.  TRUE (the
        # result IS MkBox(5)); pre-fix it trapped on `i32.eq` (pointer compare).
        src = _BOX.format(ensures="@Box.result == MkBox(@Int.0)")
        assert _run(src, fn="main") == 5

    def test_adt_ctor_eq_result_runs_reversed_order(self) -> None:
        # Operand order flipped: `MkBox(@Int.0) == @Box.result`.  The left
        # operand is a ConstructorCall (already type-resolvable), so this order
        # worked pre-fix — pin it so the fix keeps BOTH orders green.
        src = _BOX.format(ensures="MkBox(@Int.0) == @Box.result")
        assert _run(src, fn="main") == 5

    def test_adt_result_neq_ctor_runs(self) -> None:
        # `!=` on composites must also lower structurally: `@Box.result !=
        # MkBox(@Int.0 + 1)` is TRUE (MkBox(5) != MkBox(6)); pre-fix `i32.ne`
        # of two distinct pointers was *accidentally* true here, but the fix
        # must keep it true via structural inequality, not pointer luck.
        src = _BOX.format(ensures="@Box.result != MkBox(@Int.0 + 1)")
        assert _run(src, fn="main") == 5

    def test_option_result_eq_ctor_runs(self) -> None:
        # `@Option<Int>.result == Some(@Int.0)` — the built-in Option ADT.
        src = _OPTION.format(ensures="@Option<Int>.result == Some(@Int.0)")
        assert _run(src, fn="main") == 5

    def test_nested_adt_result_eq_ctor_runs(self) -> None:
        # Nested user ADT: `@Outer.result == MkOuter(MkInner(@Int.0))`.  The
        # structural eq must recurse through Outer's field into Inner.
        src = _NESTED.format(ensures="@Outer.result == MkOuter(MkInner(@Int.0))")
        assert _run(src, fn="main") == 5


# =====================================================================
# NEGATIVE CONTROL (soundness): a FALSE composite postcondition must be
# rejected by verify AND trap at runtime — the fix must not let it pass.
# =====================================================================

class TestFalseCompositePostconditionRejected912:
    def test_false_adt_ensures_rejected_by_verify(self) -> None:
        # `@Box.result == MkBox(0)` while the body returns MkBox(@Int.0): FALSE
        # for any input != 0.  Must be a Tier-1 counterexample (E500), never a
        # silent pass — the structural-eq codegen fix must not weaken this.
        src = _BOX.format(ensures="@Box.result == MkBox(0)")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors, (
            "A false composite postcondition must fail Tier-1 verification"
        )
        assert any(d.error_code == "E500" for d in errors), (
            f"Expected E500 postcondition counterexample, got {errors}"
        )

    def test_false_adt_ensures_traps_at_runtime(self) -> None:
        # The runtime check must still ENFORCE a false composite postcondition:
        # structural `MkBox(5) == MkBox(0)` is false → trap.  (A structural-eq
        # regression that returned true for unequal ADTs would make this pass —
        # this is the soundness half of the differential.)
        src = _BOX.format(ensures="@Box.result == MkBox(0)")
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected compile errors: {errors}"
        with pytest.raises(WasmTrapError, match="Postcondition violation") as exc:
            execute(result, fn_name="main")
        assert exc.value.kind == "contract_violation"

    def test_false_option_ensures_rejected_by_verify(self) -> None:
        # Sibling built-in: `@Option<Int>.result == Some(0)` is false for input
        # != 0.  Must be an E500 counterexample.
        src = _OPTION.format(ensures="@Option<Int>.result == Some(0)")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert any(d.error_code == "E500" for d in errors), (
            f"Expected E500 for false Option postcondition, got {errors}"
        )

    def test_false_nested_ensures_traps_at_runtime(self) -> None:
        # Nested: `@Outer.result == MkOuter(MkInner(0))` false for input != 0.
        # Structural eq must recurse and return false → trap.
        src = _NESTED.format(ensures="@Outer.result == MkOuter(MkInner(0))")
        result = _compile(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, f"Unexpected compile errors: {errors}"
        with pytest.raises(WasmTrapError, match="Postcondition violation"):
            execute(result, fn_name="main")


# =====================================================================
# Verify: the TRUE composite postcondition proves at Tier 1 (no false
# Tier-1, no spurious deferral for the user-ADT case).
# =====================================================================

class TestCompositePostconditionVerifies912:
    def test_true_adt_ensures_verified_tier1(self) -> None:
        # `@Box.result == MkBox(@Int.0)` must prove at Tier 1 (it did pre-fix —
        # the bug was purely in the runtime lowering, not the verifier).  Pin it
        # so the codegen fix does not accidentally perturb the proof path.
        src = _BOX.format(ensures="@Box.result == MkBox(@Int.0)")
        result = _verify(src)
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert errors == [], f"Unexpected verify errors: {errors}"
        assert result.summary.tier1_verified >= 1
