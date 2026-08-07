"""Codegen's refinement guard and :mod:`vera.naming` share ONE derivation.

The runtime guard for a refined parameter has to bind its predicate under
exactly the key the predicate's own ``@Base.n`` resolves to — and under the
key the checker bound that binder to.  Two hand-maintained derivations of
"chase the alias chain, name the base, conjoin the base's implicit range"
existed (``ContractsMixin._refinement_guard_parts`` and
:func:`vera.naming.refinement_binder_parts`) and had already drifted at two
corners, so this pins the surviving one against its consumer.

A DIFFERENTIAL, not a unit test on either side: the failure mode is the two
disagreeing, which a green test of each alone cannot see.  Codegen's two
WASM-specific decisions — reject a nested refinement base loudly (E618),
emit no guard at all for an erased base — are layered on top and are pinned
here too, because "converge the derivations" must not quietly drop them.
"""
from __future__ import annotations

import pytest

from vera import ast, naming
from vera.codegen import CodeGenerator
from vera.parser import parse_to_ast

from tests.codegen_helpers import _compile, _compile_ok, _run


_PRELUDE = """\
type Pos = { @Int | @Int.0 > 0 };
type Pos2 = Pos;
type Count = Nat;
type SmallCount = { @Count | @Count.0 < 10 };
type Txt = String;
type Sized = { @Array<Txt> | array_length(@Array<Txt>.0) > 0 };
type Small = { @Byte | @Byte.0 > 5 };
type Plain = Int;
"""


def _generator(source: str) -> CodeGenerator:
    """A CodeGenerator with *source*'s aliases registered, mid-compile state.

    Compiling is what populates the flat alias maps and the ``_alias_env``
    derived from them, so the guard derivation is exercised against the same
    environment a real compile uses rather than a hand-built one.
    """
    gen = CodeGenerator(source=source, file="<conv>")
    gen.compile_program(parse_to_ast(source))
    return gen


_SHAPES = ["Pos", "Pos2", "SmallCount", "Sized", "Small", "Count", "Plain"]


@pytest.mark.parametrize("alias", _SHAPES)
def test_codegen_guard_and_naming_agree(alias: str) -> None:
    """One derivation: codegen's guard is naming's answer, or naming says None.

    Covers a direct refinement, a refinement reached through an alias hop, a
    ``@Nat``-based and a ``@Byte``-based refinement (both range-conjoining),
    a composite base whose binder is a RESOLVED argument list
    (``Array<String>``, not the source's ``Array<Txt>``), and two
    non-refinements that must return ``None`` on both sides.
    """
    source = _PRELUDE + f"""
public fn probe(@{alias} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}
"""
    gen = _generator(source)
    te = ast.NamedType(name=alias, type_args=None)

    parts = naming.refinement_binder_parts(te, gen._alias_env)
    guard = gen._refinement_guard_parts(te)

    if parts is None:
        assert guard is None, (
            f"codegen emits a guard for @{alias} that naming reports no "
            f"binder for: {guard}"
        )
        return
    assert guard is not None, (
        f"naming derives a binder for @{alias} ({parts.binder_name}) that "
        "codegen drops"
    )
    predicate, binder_name = guard
    assert binder_name == parts.binder_name
    assert predicate == parts.predicate


def test_binder_is_the_key_a_predicate_reference_resolves_to() -> None:
    """The property the convergence exists to hold: bind side == reference side.

    A guard that pushes the value under one name while the predicate's
    ``@Base.n`` resolves under another emits a check that reads nothing.
    """
    source = _PRELUDE + """
public fn probe(@Sized -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""
    gen = _generator(source)
    guard = gen._refinement_guard_parts(
        ast.NamedType(name="Sized", type_args=None))
    assert guard is not None
    _, binder_name = guard
    assert binder_name == naming.slot_ref_key(
        ast.SlotRef(
            type_name="Array",
            type_args=(ast.NamedType(name="Txt", type_args=None),),
            index=0,
        ),
        gen._alias_env,
    )


def test_nested_refinement_base_still_rejected_loudly() -> None:
    """The E618 codegen layers on top of the shared derivation (#746 review).

    Naming reports the shape (``base_is_refinement``); codegen decides it is
    an error, because the guard it could emit would check only the OUTER
    predicate and silently drop the inner membership — accepting ``-1`` for
    ``type Tiny = { @Pos | @Pos.0 < 10 }`` over ``Pos = { @Int | @Int.0 > 0 }``.
    """
    source = """
type Pos = { @Int | @Int.0 > 0 };
type Tiny = { @Pos | @Pos.0 < 10 };
public fn f(@Tiny -> @Int) requires(true) ensures(true) effects(pure) { 0 }
"""
    result = _compile(source)
    errs = [d for d in result.diagnostics
            if d.severity == "error" and d.error_code == "E618"]
    assert errs, f"expected E618; diagnostics: {result.diagnostics}"
    assert "resolves to another refinement" in errs[0].description


def test_erased_base_emits_no_guard() -> None:
    """Codegen's other layered decision: a base with no WASM local.

    ``@Unit`` erases, so there is nothing to load into a boundary check and
    codegen emits no guard — naming has no opinion, because whether a type
    has a runtime representation is not a naming question.
    """
    source = """
type Nothing = { @Unit | true };
public fn f(@Nothing -> @Int) requires(true) ensures(true) effects(pure) { 0 }
"""
    gen = _generator(source)
    te = ast.NamedType(name="Nothing", type_args=None)
    assert naming.refinement_binder_parts(te, gen._alias_env) is not None
    assert gen._refinement_guard_parts(te) is None


def test_byte_range_still_conjoined_at_runtime() -> None:
    """The range conjunction is not merely structural — it traps.

    ``300`` satisfies ``> 5`` but not ``<= 255``; the guard rejects it, which
    is what proves the shared derivation's conjunction reaches the emitted
    check rather than only the returned AST.
    """
    from vera.codegen import execute

    source = """
type BigByte = { @Byte | @Byte.0 > 5 };
public fn f(@BigByte -> @Byte)
  requires(true) ensures(true) effects(pure)
{ @BigByte.0 }
"""
    result = _compile_ok(source)
    with pytest.raises(RuntimeError, match=r"@Byte\.0 <= 255"):
        execute(result, fn_name="f", args=[300])
    assert _run(source, fn="f", args=[7]) == 7


def test_codegen_really_consumes_the_shared_derivation() -> None:
    """Mutation validation: perturb naming, watch codegen's guard move.

    The parametrized differential above is green whether or not the two sides
    share an implementation — that is exactly what let a second copy drift
    unnoticed.  This is the assertion that distinguishes them: replace
    :func:`vera.naming.refinement_binder_parts` with one that renames the
    binder, and codegen's guard must report the renamed binder.  A codegen
    that still carries its own copy of the walk answers the old name and
    fails here.
    """
    source = _PRELUDE + """
public fn probe(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""
    gen = _generator(source)
    te = ast.NamedType(name="Pos", type_args=None)
    assert gen._refinement_guard_parts(te) == (
        naming.refinement_binder_parts(te, gen._alias_env).predicate,  # type: ignore[union-attr]
        "Int",
    )

    original = naming.refinement_binder_parts

    def perturbed(
        te_: ast.TypeExpr, env: naming.AliasEnv,
    ) -> naming.RefinementBinder | None:
        parts = original(te_, env)
        if parts is None:
            return None
        return naming.RefinementBinder(
            predicate=parts.predicate,
            binder_name=parts.binder_name + "$MUTANT",
            base=parts.base,
            base_is_refinement=parts.base_is_refinement,
        )

    naming.refinement_binder_parts = perturbed  # type: ignore[assignment]
    try:
        mutated = gen._refinement_guard_parts(te)
    finally:
        naming.refinement_binder_parts = original  # type: ignore[assignment]

    assert mutated is not None
    assert mutated[1] == "Int$MUTANT", (
        "codegen's refinement guard did not follow vera.naming — it is still "
        f"deriving the binder itself; got {mutated[1]!r}"
    )
