"""#1274: a module generic that does not own the importer's bare name must be
reached under its module-qualified ``mod$<path>$name`` identity.

Pre-fix, only a PRIVATE module generic was rerouted onto that identity (#1000 /
#1029).  A PUBLIC one was rerouted never — so a module's own body calling its
own generic by bare name was resolved in the IMPORTER's flat namespace, where
the bare name belongs to whatever the importer declares.  Three consequences,
all reproduced below:

* **False Tier-1** — the importer's same-named generic clone silently runs in
  place of the module's.  ``vera check`` / ``verify`` are clean and the module's
  own ``ensures`` is violated at run (the module promises 111, the importer's
  body returns 999).
* **Invalid WASM** on a type-discriminating shape — both modules' ``gen2``
  mangle to one ``gen2$Bool``, so the surviving clone has the other's WAT type.
* **A dangling ``$gen2``** where the module generic is public but outside the
  importer's import filter: it was registered in NO clone namespace at all.

The rule the fix installs is the one non-generics already follow
(``_register_shadowed_import``): a module function is reached under
``mod$<path>$name`` exactly when its bare name in the importer's flat namespace
does not denote that module's declaration — public **and** in-filter **and**
unshadowed.  Generic and non-generic now share that one predicate
(:func:`vera.monomorphize.module_qualified_generic_names`).

Every cell asserts the verify verdict AND the runtime value in ONE test,
against the standalone oracle: the library compiled ALONE answers 111, so 111
is what every import shape must answer.
"""

from __future__ import annotations

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.verifier import verify

# The library's private answer.  Chosen so it cannot coincide with the
# importer's (999) nor with any default/fallback in the mangler.
LIB_ANSWER = 111
MAIN_ANSWER = 999


def _lib(gen_vis: str) -> str:
    """A module whose public door calls its own generic by BARE name."""
    return f"""\
module lib;

private fn v(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}

{gen_vis} forall<T> fn gen2(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ v(()) }}

public fn door(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ gen2(@Bool.0) }}
"""


def _main(gen_vis: str, imports: str) -> str:
    """An importer that declares its OWN ``gen2`` (and its own ``v``)."""
    imp = "import lib;" if imports is None else f"import lib({imports});"
    return f"""\
{imp}

private fn v(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

{gen_vis} forall<T> fn gen2(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ v(()) }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen2(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""


# The oracle: the library compiled ALONE, with its own driver in place of the
# importer.  Whatever the import door does, this is the answer the module's
# source (and its proved `ensures`) commits to.
_STANDALONE = _lib("private").replace("module lib;\n", "") + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{ door(true) }
"""


def _build(tmp_path, files: dict[str, str], main_name: str = "main.vera"):
    """Type-check + verify + compile *main_name* exactly as ``vera run`` does.

    Returns ``(verify_errors, compile_result_or_None, codegen_errors)``.
    """
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    main_path = tmp_path / main_name
    source = files[main_name]
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    check_errors = [d.description for d in diags if d.severity == "error"]
    assert not check_errors, f"typecheck errors: {check_errors}"
    vres = verify(program, source, file=str(main_path),
                  resolved_modules=resolved)
    verify_errors = [
        d.description for d in vres.diagnostics if d.severity == "error"
    ]
    result = codegen_compile(
        program, source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    cg_errors = [
        d.description for d in result.diagnostics if d.severity == "error"
    ]
    return verify_errors, result, cg_errors


def _value(result, fn: str = "main"):
    """``(kind, payload)`` — ``("ok", value)`` or ``("trap", message)``."""
    try:
        return "ok", execute(result, fn_name=fn).value
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError) as exc:
        return "trap", str(exc)


def _assert_cell(tmp_path, lib_vis: str, main_vis: str, imports: str) -> None:
    """The whole obligation for one cell, in ONE test: check + verify clean,
    valid WASM, and the DECLARING module's answer at run."""
    verify_errors, result, cg_errors = _build(
        tmp_path, {"lib.vera": _lib(lib_vis),
                   "main.vera": _main(main_vis, imports)},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    kind, payload = _value(result)
    # Verify and run must AGREE.  A clean verify beside a runtime postcondition
    # violation is the false Tier-1 this issue is about, so both halves are
    # asserted together rather than in sibling tests.
    assert not verify_errors, f"verify errors: {verify_errors}"
    assert kind == "ok", (
        f"lib={lib_vis} main={main_vis} imports={imports!r}: the module's own "
        f"generic did not run — {payload}"
    )
    assert payload == LIB_ANSWER, (
        f"lib={lib_vis} main={main_vis} imports={imports!r}: ran the IMPORTER's "
        f"gen2 ({payload}) where the declaring module's body answers "
        f"{LIB_ANSWER} — a false Tier-1 (verify was clean)"
    )
    # The local generic must be untouched by the fix: it still owns the bare
    # name for the importer's own call.
    lkind, lvalue = _value(result, "useLocal")
    assert (lkind, lvalue) == ("ok", MAIN_ANSWER), (
        f"the importer's own gen2 must still answer {MAIN_ANSWER}, "
        f"got {lkind}/{lvalue}"
    )


class TestStandaloneOracle:
    """What the library's source commits to, with no importer in the picture."""

    def test_standalone_library_answers_111(self, tmp_path) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, {"main.vera": _STANDALONE},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestVisibilityMatrix:
    """All four cells of (module generic visibility x importer generic
    visibility).  Pre-fix the two ``lib=public`` cells were false Tier-1s; the
    ``lib=private`` cells were already correct (#1000's reroute) and are the
    regression half of the matrix."""

    @pytest.mark.parametrize("lib_vis", ["public", "private"])
    @pytest.mark.parametrize("main_vis", ["public", "private"])
    def test_cell(self, tmp_path, lib_vis: str, main_vis: str) -> None:
        _assert_cell(tmp_path, lib_vis, main_vis, "door")


class TestImportFilterDimension:
    """The importer's filter changes which names it can SPELL, never which body
    the module's own call runs.  All three spellings answer the module's 111."""

    @pytest.mark.parametrize(
        "imports", ["door", "gen2, door", None],
        ids=["out_of_filter", "in_filter", "wildcard"],
    )
    def test_filter_shape(self, tmp_path, imports) -> None:
        _assert_cell(tmp_path, "public", "private", imports)


class TestUnshadowedOutOfFilter:
    """A public module generic OUTSIDE the importer's filter, with NO local
    shadow, was registered in no clone namespace at all: its module's own bare
    call assembled to ``unknown func: failed to find name $gen2``.  Loud, but
    the same registration hole."""

    def test_module_generic_outside_filter_is_emitted(self, tmp_path) -> None:
        main = f"""\
import lib(door);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""
        verify_errors, result, cg_errors = _build(
            tmp_path, {"lib.vera": _lib("public"), "main.vera": main},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestTypeDiscriminating:
    """Two same-named generics whose clones have DIFFERENT WAT result types.
    Collapsing them onto one ``gen2$Bool`` produced a module whose surviving
    clone had the other's signature — invalid WASM from check-green source, or
    (as here) an i64 flowing out of a ``@Bool``-returning function."""

    _LIB = """\
module lib;

public forall<T> fn gen2(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn door(@Bool -> @Bool)
  requires(true)
  ensures(@Bool.result == @Bool.0)
  effects(pure)
{ gen2(@Bool.0) }
"""

    _MAIN = """\
import lib(door);

private forall<T> fn gen2(@T -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{ 7 }

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{ gen2(true) }

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(@Bool.result == true)
  effects(pure)
{ door(true) }
"""

    def test_both_clones_keep_their_own_wat_type(self, tmp_path) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, {"lib.vera": self._LIB, "main.vera": self._MAIN},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        # The module's own `gen2<Bool>` is the identity, so `door(true)` is
        # `true` — NOT the importer's `gen2<Bool> -> 7`.
        assert _value(result, "main") == ("ok", True), (
            "door(true) must run the module's identity gen2<Bool>"
        )
        assert _value(result, "useLocal") == ("ok", 7)

    def test_wat_has_distinct_clone_symbols(self, tmp_path) -> None:
        """The naming rule, read straight off the emitted WAT: the module's
        clone carries its ``mod$lib$`` qualification, so the two ``gen2<Bool>``
        clones are two symbols, not one."""
        _, result, cg_errors = _build(
            tmp_path, {"lib.vera": self._LIB, "main.vera": self._MAIN},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        wat = result.wat
        assert "$mod$lib$gen2$Bool" in wat, (
            "the module generic's clone must be qualified by its owning "
            "module, like every other shadowed module function"
        )
