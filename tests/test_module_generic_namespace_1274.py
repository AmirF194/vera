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

import re
from pathlib import Path

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.codegen.core import CodeGenerator
from vera.monomorphize import importer_occupied_bare_names
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver, ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.verifier import ContractVerifier, verify

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


def _build(
    tmp_path: Path, files: dict[str, str],
    main_name: str = "main.vera",
) -> tuple[list[str], CompileResult, list[str]]:
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


def _value(
    result: CompileResult, fn: str = "main",
) -> tuple[str, object]:
    """``(kind, payload)`` — ``("ok", value)`` or ``("trap", message)``."""
    try:
        return "ok", execute(result, fn_name=fn).value
    except (WasmTrapError, wasmtime.WasmtimeError, wasmtime.Trap) as exc:
        return "trap", str(exc)


def _assert_cell(
    tmp_path: Path, lib_vis: str, main_vis: str,
    imports: str | None,
) -> None:
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
    def test_filter_shape(
        self, tmp_path: Path, imports: str | None,
    ) -> None:
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


class TestModuleToModuleHop:
    """A module's bare call to ANOTHER module's qualified-only generic (F1).

    The classification was per-module-own, so ``mid`` — which declares no
    generics at all — had nothing rerouted and its bare ``gen(...)`` was
    resolved in the importer's flat namespace, where the ENTRY's same-named
    generic owns the name.  ``vera verify`` clean, ``mid``'s proved
    postcondition violated at run (or, with a looser contract, a silent 999
    where the declaring module answers 111).

    The reroute now consults each module's imports under the SAME predicate,
    keyed by owner, because ``mod$<path>$name`` is per-owner: ``mid``'s call
    must reach ``mod$deep$gen``.
    """

    _DEEP = f"""\
module deep;

private fn vd(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ vd(()) }}
"""

    _MID = f"""\
module mid;

import deep;

public fn door(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""

    # The loud spelling: `door`'s own postcondition pins the answer, so a
    # captured call is a runtime violation.
    _MAIN_LOUD = f"""\
import mid(door);

private fn vm(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ vm(()) }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    # The SILENT spelling: every contract here is satisfied by both answers, so
    # nothing traps — the wrong body just returns the wrong number.  This is the
    # shape a contract-only assertion would miss entirely.
    _MAIN_SILENT = f"""\
import mid(door);

private fn vm(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{ vm(()) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{{ door(true) }}
"""

    def _files(self, main_src: str) -> dict[str, str]:
        return {
            "deep.vera": self._DEEP,
            "mid.vera": self._MID,
            "main.vera": main_src,
        }

    @pytest.mark.parametrize(
        "main_src", [_MAIN_LOUD, _MAIN_SILENT], ids=["loud", "silent"],
    )
    def test_hop_runs_the_declaring_module(self, tmp_path, main_src) -> None:
        verify_errors, result, cg_errors = _build(
            tmp_path, self._files(main_src),
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        kind, payload = _value(result)
        assert kind == "ok", f"the hop did not compile to a runnable module: {payload}"
        assert payload == LIB_ANSWER, (
            f"mid's bare call to deep's generic ran the IMPORTER's body "
            f"({payload}) where deep answers {LIB_ANSWER}"
        )

    def test_hop_is_symmetric_between_the_two_sides(self, tmp_path) -> None:
        """Both sides must key the hop's clone identically, or the clone that
        runs is verified under a name nobody checked."""
        tmp_path.mkdir(parents=True, exist_ok=True)
        files = self._files(self._MAIN_LOUD)
        for name, src in files.items():
            (tmp_path / name).write_text(src, encoding="utf-8")
        mods = [
            ResolvedModule(
                path=(stem,), file_path=tmp_path / f"{stem}.vera",
                program=parse_to_ast(files[f"{stem}.vera"]),
                source=files[f"{stem}.vera"],
            )
            for stem in ("deep", "mid")
        ]
        mainp = tmp_path / "main.vera"
        gen = CodeGenerator(
            source=self._MAIN_LOUD, file=str(mainp), resolved_modules=mods,
        )
        gen.compile_program(parse_to_ast(self._MAIN_LOUD))
        codegen_set = set(getattr(gen, "_emitted_instances", set()))
        verifier = ContractVerifier(
            source=self._MAIN_LOUD, file=str(mainp), resolved_modules=mods,
        )
        verifier.register_program(parse_to_ast(self._MAIN_LOUD))
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
        assert ("mod$deep$gen", ("Bool",)) in codegen_set, (
            f"the hop's clone must be emitted under its OWNING module's base, "
            f"got {sorted(codegen_set)}"
        )
        assert codegen_set == verifier_set, (
            f"codegen {sorted(codegen_set)} != verifier {sorted(verifier_set)}"
        )

    def test_module_own_generic_reached_transitively(self, tmp_path) -> None:
        """The neighbouring shape, and the one this PR covered first: `mid`
        calls a NON-generic door of `deep`, and it is `deep`'s OWN body that
        bare-calls its own qualified-only generic.  Two hops from the entry, so
        the classification has to reach a module the entry never imported."""
        deep = f"""\
module deep;

public forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ {LIB_ANSWER} }}

public fn cap(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ g(@Bool.0) }}
"""
        mid = f"""\
module mid;

import deep(cap);

public fn use(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ cap(@Bool.0) }}
"""
        main = f"""\
import mid(use);

private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ {MAIN_ANSWER} }}

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ g(true) }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ use(true) }}
"""
        verify_errors, result, cg_errors = _build(
            tmp_path,
            {"deep.vera": deep, "mid.vera": mid, "main.vera": main},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"
        assert _value(result) == ("ok", LIB_ANSWER)


class TestImporterBareNamesAreOneSet:
    """The importer-side input to the predicate must be the SAME set on both
    sides, or the shared predicate classifies one imported generic two ways.

    Codegen consults it AFTER Pass 0's two helper renames (the generic-helper
    qualification #1014 and the non-generic hoist #991); the verifier holds the
    pre-transform AST.  A private walk on each side counted `where`-helpers
    differently, so an imported ``gen2`` owned the bare name for codegen and was
    qualified-only for the verifier: codegen emitted ``gen2$Bool`` while the
    verifier verified ``mod$lib$gen2$Bool`` — each side's clone uncovered by the
    other, which is a false Tier-1 in the direction the #732 differential exists
    to catch.
    """

    _LIB = _lib("public")

    # A NON-generic where-helper shadowing the imported name: hoisted away by
    # codegen, still nested for the verifier.
    _MAIN_NONGENERIC_HELPER = f"""\
import lib;

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen2(true) }}
  where {{
    fn gen2(@Bool -> @Int)
      requires(true)
      ensures(@Int.result == {MAIN_ANSWER})
      effects(pure)
    {{ {MAIN_ANSWER} }}
  }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    # The GENERIC twin: renamed to `useLocal$where$gen2` by the qualification,
    # so it too stops occupying the bare name — but only if both sides say so.
    _MAIN_GENERIC_HELPER = f"""\
import lib;

public fn useLocal(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {MAIN_ANSWER})
  effects(pure)
{{ gen2(true) }}
  where {{
    forall<T> fn gen2(@T -> @Int)
      requires(true)
      ensures(@Int.result == {MAIN_ANSWER})
      effects(pure)
    {{ {MAIN_ANSWER} }}
  }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LIB_ANSWER})
  effects(pure)
{{ door(true) }}
"""

    @pytest.mark.parametrize(
        "main_src",
        [_MAIN_NONGENERIC_HELPER, _MAIN_GENERIC_HELPER],
        ids=["nongeneric_where_helper", "generic_where_helper"],
    )
    def test_both_sides_name_one_clone(self, tmp_path, main_src: str) -> None:
        tmp_path.mkdir(parents=True, exist_ok=True)
        libp = tmp_path / "lib.vera"
        mainp = tmp_path / "main.vera"
        libp.write_text(self._LIB, encoding="utf-8")
        mainp.write_text(main_src, encoding="utf-8")
        mod = ResolvedModule(
            path=("lib",), file_path=libp,
            program=parse_to_ast(self._LIB), source=self._LIB,
        )
        gen = CodeGenerator(
            source=main_src, file=str(mainp), resolved_modules=[mod],
        )
        gen.compile_program(parse_to_ast(main_src))
        codegen_set = set(getattr(gen, "_emitted_instances", set()))
        verifier = ContractVerifier(
            source=main_src, file=str(mainp), resolved_modules=[mod],
        )
        verifier.register_program(parse_to_ast(main_src))
        verifier_set = {
            (n, ct) for n, cts in verifier._instances.items() for ct in cts
        }
        assert not codegen_set - verifier_set, (
            f"codegen emits clones the verifier never discovers: "
            f"{sorted(codegen_set - verifier_set)}"
        )
        assert not verifier_set - codegen_set, (
            f"the verifier discovers clones codegen never emits: "
            f"{sorted(verifier_set - codegen_set)}"
        )

    def test_bare_name_set_is_idempotent_across_the_hoist(self) -> None:
        """The property that lets one derivation serve both sides: run it on the
        POST-transform program and the answer this predicate consumes — the
        ``$``-free names — is unchanged.  Only mangled entries are added, and a
        mangled name can never equal a module's source identifier."""
        pre = parse_to_ast(self._MAIN_NONGENERIC_HELPER)
        gen = CodeGenerator(source=self._MAIN_NONGENERIC_HELPER, file="m.vera")
        post = gen._hoist_nongeneric_where_helpers(pre)
        bare_pre = {n for n in importer_occupied_bare_names(pre) if "$" not in n}
        bare_post = {
            n for n in importer_occupied_bare_names(post) if "$" not in n
        }
        assert bare_pre == bare_post, (
            f"the derivation is not hoist-idempotent: pre={sorted(bare_pre)} "
            f"post={sorted(bare_post)}"
        )
        assert "gen2" not in bare_pre, (
            "a non-generic where-helper does not occupy a bare name after the "
            "hoist, so it must not be counted as shadowing an import"
        )


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
        kind, payload = _value(result, "main")
        assert kind == "ok", f"door(true) trapped: {payload}"
        assert payload == 1, (
            f"door(true) must run the module's identity gen2<Bool> and answer "
            f"`true`, got {payload!r}"
        )
        # The value alone cannot carry the type — the host hands a `@Bool` back
        # as a plain `1` — so the discriminating claim is asserted where it is
        # actually visible: `main` must be declared `(result i32)`.  If the two
        # clones had collapsed onto one symbol, `main` would carry the other's
        # i64 and this would be the only assertion that noticed.
        assert re.search(
            r"\(func \$main[^\n]*\(result i32\)", result.wat,
        ), (
            "main returns @Bool, so its WAT result type must be i32 — an i64 "
            "here is the type-discriminating collapse this shape exists to "
            "catch"
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
        symbols = set(re.findall(r"\(func (\$[\w$]+)", result.wat))
        gen2_syms = sorted(x for x in symbols if "gen2" in x)
        # WHOLE-symbol matches: `$gen2$Bool` is a suffix of
        # `$mod$lib$gen2$Bool`, so a substring test for the bare clone is
        # satisfied by the qualified one alone and the "two distinct
        # symbols" claim would be vacuous.
        assert "$mod$lib$gen2$Bool" in symbols, (
            f"the module generic's clone must be qualified by its owning "
            f"module, like every other shadowed module function — "
            f"got {gen2_syms}"
        )
        assert "$gen2$Bool" in symbols, (
            f"the IMPORTER's own gen2<Bool> must still occupy the bare "
            f"clone name — got {gen2_syms}"
        )
