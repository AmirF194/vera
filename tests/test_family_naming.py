"""The State/Exn cell FAMILY is the cell the checker typed (#1209).

The checker resolves an effect instance's type arguments in full
(``_resolve_effect_ref`` -> ``_resolve_type``), so ``State<MyAlias>`` under
``type MyAlias = Option<Int>`` and ``State<Option<Int>>`` are ONE
``EffectInstance``: one handler handles both spellings, and a call across
them type-checks.  Codegen used to name the family from the SOURCE spelling
for anything that did not resolve to a scalar (the #1205 gate), so those two
spellings minted two host cells — one per checker, two per codegen, a silent
state split behind a green check.

:func:`vera.naming.family_name` is now the one family renderer for every
site (registration, per-function lowering, the ``old(State<T>)`` snapshot),
so the cell identity codegen emits is the cell identity the checker typed.

What this file pins, in order:

* the collapse is OBSERVABLE — a mixed-spelling program returns the value
  the shared cell holds, not the untouched one a split cell leaves behind;
* the import surface COLLAPSES with it — one family, one set of host
  imports, not two;
* it holds across a MODULE boundary, where each side names against its own
  alias namespace;
* distinct cells stay distinct — the collapse is resolution, not erasure;
* a resolution that cannot be MANGLED keeps the opaque spelling, because a
  family name is a WAT symbol before it is anything else;
* alias-free programs are byte-identical, which is what says the change
  reaches exactly the alias spellings and nothing else.

The whole-corpus measurement behind the last point lives in
``tests/test_slot_naming_blast_radius.py``; the unit-level rendering rules
live in ``tests/test_slot_naming.py``.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import CompileResult, compile as codegen_compile, execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver

_ROOT = Path(__file__).resolve().parent.parent

_STATE_GET_RE = re.compile(r'\(import "vera" "(state_get_[A-Za-z0-9_$?]*)"')
_STATE_IMPORT_RE = re.compile(r'\(import "vera" "(state_[a-z]+_[A-Za-z0-9_$?]*)"')
_EXN_TAG_RE = re.compile(r"\(tag \$(exn_[A-Za-z0-9_$?]*)")


# =====================================================================
# Helpers
# =====================================================================


def _compile_source(source: str, tmp_path: Path, name: str = "m") -> CompileResult:
    """Compile *source* through the real file-based pipeline."""
    path = tmp_path / f"{name}.vera"
    path.write_text(source, encoding="utf-8")
    return _compile_path(path)


def _compile_path(path: Path) -> CompileResult:
    """Parse + resolve + check + compile *path*, asserting a clean check."""
    source = path.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(program, path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(path), resolved_modules=resolved,
    )
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, (
        f"{path.name} must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )
    return codegen_compile(
        program, source=source, file=str(path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
    )


def _compile_ok(source: str, tmp_path: Path, name: str = "m") -> CompileResult:
    """:func:`_compile_source`, asserting codegen raised no hard error."""
    result = _compile_source(source, tmp_path, name)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, (
        f"expected a clean compile, got: "
        f"{[(d.error_code, d.description[:90]) for d in hard]}"
    )
    return result


def _families(wat: str) -> set[str]:
    """Every State import and Exn tag family symbol emitted in *wat*."""
    return set(_STATE_IMPORT_RE.findall(wat)) | set(_EXN_TAG_RE.findall(wat))


# =====================================================================
# (1) The collapse is observable in what a program COMPUTES
# =====================================================================

# A callee declares the effect one way, the handler spells it the other.  A
# split family gives the handler's cell the initial value forever (the
# callee's `put` lands in a cell nothing reads); a collapsed one gives the
# value the callee wrote, which is what the checker's single instance means.
_MIXED_STATE_COMPOSITE = """\
type MaybeInt = Option<Int>;

private fn stash(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Option<Int>>>)
{
  put(Some(7))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<MaybeInt>](@MaybeInt = None) {
    get(@Unit) -> { resume(@MaybeInt.0) },
    put(@MaybeInt) -> { resume(()) }
  } in {
    stash(());
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""

# The same shape through a PARAMETERISED alias, which reaches the collapse by
# substitution rather than by a bare name follow.
_MIXED_STATE_PARAM_ALIAS = """\
type Boxed<T> = Option<T>;

private fn stash(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Option<Int>>>)
{
  put(Some(7))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Boxed<Int>>](@Boxed<Int> = None) {
    get(@Unit) -> { resume(@Boxed<Int>.0) },
    put(@Boxed<Int>) -> { resume(()) }
  } in {
    stash(());
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""


@pytest.mark.parametrize(
    ("source", "why"),
    [
        (_MIXED_STATE_COMPOSITE, "bare composite alias"),
        (_MIXED_STATE_PARAM_ALIAS, "parameterised composite alias"),
    ],
    ids=["bare_composite_alias", "parameterised_composite_alias"],
)
def test_mixed_spelling_state_cell_is_one_cell(
    source: str, why: str, tmp_path: Path,
) -> None:
    """The handler reads what the differently-spelled callee wrote.

    ``0 - 1`` is the value a SPLIT family produces (the handler's ``None``
    survives because the callee's ``put`` went to a second cell), so the
    assertion distinguishes the two outcomes rather than merely observing
    that the program runs.
    """
    result = _compile_ok(source, tmp_path)
    assert execute(result).value == 7, f"{why}: the two spellings share a cell"


_MIXED_EXN_STRING_ALIAS = """\
type Msg = String;

private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  throw("abcde")
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Msg>] {
    throw(@Msg) -> { string_length(@Msg.0) }
  } in {
    boom(())
  }
}
"""


def test_mixed_spelling_exn_string_payload_moves_its_pair(
    tmp_path: Path,
) -> None:
    """An ``Exn<Msg>`` handler catches an ``Exn<String>`` throw, pair intact.

    ``String`` is an ``i32_pair`` payload — the tag carries ``(ptr, len)`` —
    so this is the shape where a family split is not merely a wrong value
    but a wrong ARITY: the thrower's two-i32 tag and the catcher's tag have
    to be the same tag.  ``string_length`` reads the ``len`` half, so a
    payload that arrived through the wrong tag cannot answer 5 by accident.
    """
    result = _compile_ok(_MIXED_EXN_STRING_ALIAS, tmp_path)
    assert _families(result.wat) == {"exn_String"}, result.wat[:400]
    assert execute(result).value == 5


# =====================================================================
# (2) One collapsed family, one set of host imports
# =====================================================================


def test_one_import_per_collapsed_family(tmp_path: Path) -> None:
    """The mixed-spelling program declares the ``Option<Int>`` family ONCE.

    Every host binding is synthesised per registered family (wasmtime in
    ``vera/runtime/state.py``, the browser bundle by regex over the import
    names), so a family that splits fans the import surface out too — the
    #808 hazard.  Counting the ``state_get_`` imports, not just checking the
    set, catches a duplicate registration under one name as well.
    """
    result = _compile_ok(_MIXED_STATE_COMPOSITE, tmp_path)
    gets = _STATE_GET_RE.findall(result.wat)
    assert gets == ["state_get_Option_LInt_R"], result.wat[:600]
    assert _families(result.wat) == {
        "state_get_Option_LInt_R", "state_put_Option_LInt_R",
        "state_push_Option_LInt_R", "state_pop_Option_LInt_R",
    }


# =====================================================================
# (3) The collapse crosses a module boundary
# =====================================================================

_XMOD_LIB = """\
module paylib;

type Payload = Option<Int>;

public fn stash(@Int -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Payload>>)
{
  put(Some(@Int.0))
}
"""

_XMOD_MAIN = """\
import paylib;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = None) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    stash(7);
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""


def test_cross_module_composite_alias_collapses(tmp_path: Path) -> None:
    """A module-private composite alias joins the importer's cell.

    Each side renders against its OWN alias namespace — ``Payload`` exists
    only in ``paylib`` — and they still have to land on one family, because
    the checker types one instance across the import.  The value oracle is
    the same distinguishing 7-vs--1 as the single-module case.
    """
    (tmp_path / "paylib.vera").write_text(_XMOD_LIB, encoding="utf-8")
    (tmp_path / "main.vera").write_text(_XMOD_MAIN, encoding="utf-8")
    result = _compile_path(tmp_path / "main.vera")
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, [(d.error_code, d.description[:90]) for d in hard]
    assert _STATE_GET_RE.findall(result.wat) == ["state_get_Option_LInt_R"]
    assert execute(result).value == 7


# =====================================================================
# (4) Distinct cells stay distinct — the negative
# =====================================================================

_TWO_DISTINCT_CELLS = """\
type MaybeInt = Option<Int>;
type MaybeBool = Option<Bool>;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<MaybeInt>](@MaybeInt = Some(4)) {
    put(@MaybeInt) -> { resume(()) }
  } in {
    handle[State<MaybeBool>](@MaybeBool = None) {
      put(@MaybeBool) -> { resume(()) }
    } in {
      put(Some(true))
    };
    option_unwrap_or(get(()), 0 - 1)
  }
}
"""


def test_two_aliases_of_different_types_keep_two_families(
    tmp_path: Path,
) -> None:
    """Collapsing is RESOLUTION, not erasure of the type argument.

    ``Option<Int>`` and ``Option<Bool>`` are two checker instances, so they
    must stay two cells: two import families, and the outer cell still
    holding 4 after the inner handler wrote to its own.  A family renderer
    that dropped type arguments (the pre-#914 one-level bug) would pass the
    positive tests above and fail here.
    """
    result = _compile_ok(_TWO_DISTINCT_CELLS, tmp_path)
    assert set(_STATE_GET_RE.findall(result.wat)) == {
        "state_get_Option_LInt_R", "state_get_Option_LBool_R",
    }, result.wat[:600]
    assert execute(result).value == 4


# =====================================================================
# (5) A family name is a WAT symbol before it is anything else
# =====================================================================

_NESTED_FN_CELL = """\
type Handler = Option<fn(Int -> Int) effects(pure)>;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Handler>](@Handler = None) {
    put(@Handler) -> { resume(()) }
  } in {
    0
  }
}
"""

# The #1219 flip made observable: a callee declares the cell by its RESOLVED
# spelling, the handler by the alias.  Pre-flip those were two families, so
# the callee's `put` landed in a cell nothing read and `main` returned the
# handler's initial `0 - 1`; post-flip they are one cell and it returns 5.
_MIXED_FN_CELL = """\
type Handler = Option<fn(Int -> Int) effects(pure)>;

private fn stash(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Option<fn(Int -> Int) effects(pure)>>>)
{
  put(Some(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Handler>](@Handler = None) {
    get(@Unit) -> { resume(@Handler.0) },
    put(@Handler) -> { resume(()) }
  } in {
    stash(());
    match get(()) {
      Some(@Fn) -> 5,
      None -> 0 - 1
    }
  }
}
"""

# The elision the spellability gate had been masking.  `Option<Pos>` and
# `Option<Neg>` are two checker instances, and both render
# `Option<{@Int | ...}>` through `pretty_type` — so dropping the gate
# WITHOUT moving to the structural key would have merged them.
_TWO_REFINED_ARG_CELLS = """\
type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Pos>>](@Option<Pos> = None) {
    put(@Option<Pos>) -> { resume(()) }
  } in {
    handle[State<Option<Neg>>](@Option<Neg> = None) {
      put(@Option<Neg>) -> { resume(()) }
    } in {
      0
    };
    0
  }
}
"""


def test_fn_type_composite_cell_takes_its_resolved_family(
    tmp_path: Path,
) -> None:
    """A cell whose resolution carries a function type DOES take it (#1219).

    ``Option<fn(Int -> Int) effects(pure)>`` renders with parentheses and an
    arrow, which the pre-#1219 escape did not cover — emitting it produced
    an import name the WAT parser rejects, so ``family_name`` gated on the
    spellable ``Head<arg, arg>`` grammar and kept the alias-opaque
    ``Handler``.  With the mangler total, the resolved rendering IS the
    family and the symbol is its mangling: the ``_U28_``/``_U29_`` are the
    parentheses, ``_U2d__R`` the arrow.
    """
    result = _compile_ok(_NESTED_FN_CELL, tmp_path)
    assert _STATE_GET_RE.findall(result.wat) == [
        "state_get_Option_Lfn_U28_Int_S_U2d__R_SInt_U29__Seffects"
        "_U28_pure_U29__R"
    ]
    assert execute(result).value == 0


def test_mixed_spelling_fn_type_cell_is_one_cell(tmp_path: Path) -> None:
    """The alias and its resolution name ONE cell, proved by the value.

    ``0 - 1`` is what a split family produces — the handler's ``None``
    survives because ``stash``'s ``put`` went to a second cell — and ``5``
    is reachable only when the handler's ``get`` observes the ``Some`` the
    differently-spelled callee wrote.  This is the run-level half of #1219:
    the symbol assertion above says the two names agree, this says the two
    SITES do.  Neither outcome is a zero default.
    """
    result = _compile_ok(_MIXED_FN_CELL, tmp_path)
    assert len(set(_STATE_GET_RE.findall(result.wat))) == 1, result.wat[:600]
    assert execute(result).value == 5


_BARE_FN_CELL = """\
type F = fn(Int -> Int) effects(pure);

public fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<F>](@F = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }) {
    get(@Unit) -> { resume(@F.0) },
    put(@F) -> { resume(()) }
  } in {
    apply_fn(get(()), 41)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(())
}
"""


def test_bare_fn_type_cell_still_takes_the_fallback_and_is_refused(
    tmp_path: Path,
) -> None:
    """What is LEFT for ``family_fallback_name`` after #1219, pinned.

    #1219 removed the mangle-safety gate, not the fallback: a type
    expression whose resolution IS a bare function type has no cell type to
    name at all, so ``family_name`` returns the fallback and the cell keeps
    its alias-opaque spelling — ``F``, never ``fn(Int -> Int)
    effects(pure)``.  The other survivor is an unresolvable type expression
    (a removed alias, an alias applied at the wrong arity), which renders
    ``?``; keeping the spelling there stops two unrelated broken cells from
    merging onto one ``?`` family.

    Inert either way, and this pins that too: the shape is refused
    downstream, the enclosing function dropped loudly (E616 for the closure
    read, then E602/E620), so the fallback name reaches an import
    declaration and nothing that calls it.  Splitting it is therefore free,
    and merging it would be the only thing with a cost.

    Promoted from ``tests/probes/state_handlers/alias_families/
    p7_fn_alias_state_arg.vera``, which asked this question and was deleted
    with the #1219 disposition.
    """
    result = _compile_source(_BARE_FN_CELL, tmp_path)
    assert _families(result.wat) == {
        "state_get_F", "state_put_F", "state_push_F", "state_pop_F",
    }, result.wat[:400]
    codes = {d.error_code for d in result.diagnostics}
    assert {"E602", "E620"} <= codes, codes
    assert "(func $probe" not in result.wat
    assert "(func $main" not in result.wat


def test_two_refinements_of_one_base_in_argument_position_stay_apart(
    tmp_path: Path,
) -> None:
    """Dropping the gate must not merge what ``pretty_type`` elides (#1219).

    ``Option<Pos>`` and ``Option<Neg>`` are two checker instances that
    ``pretty_type`` renders identically (``Option<{@Int | ...}>``), because
    a refinement in argument position prints its predicate as ``...``.  The
    spellability gate refused that rendering and both cells fell back to
    their alias spellings, so the elision never reached a symbol; removing
    the gate without moving to the structural key would have merged them.
    Two families here is the assertion that the move happened.
    """
    result = _compile_ok(_TWO_REFINED_ARG_CELLS, tmp_path)
    families = set(_STATE_GET_RE.findall(result.wat))
    assert len(families) == 2, families


# =====================================================================
# (6) Alias-free programs are byte-identical
# =====================================================================

# Every corpus program that emits a family symbol and contains no alias in
# the cell position: the exact symbol set, pinned.  The #1209 flip moved
# NONE of these — that is what says it reaches alias spellings only.
_STABLE_SYMBOLS: tuple[tuple[str, frozenset[str]], ...] = (
    ("examples/increment.vera", frozenset({
        "state_get_Int", "state_put_Int", "state_push_Int", "state_pop_Int"})),
    ("examples/effect_handler.vera", frozenset({
        "state_get_Int", "state_put_Int", "state_push_Int", "state_pop_Int",
        "exn_Int"})),
    ("tests/conformance/ch07_state_composite.vera", frozenset({
        "state_get_Option_LInt_R", "state_put_Option_LInt_R",
        "state_push_Option_LInt_R", "state_pop_Option_LInt_R",
        "state_get_Tuple_LInt_CInt_R", "state_put_Tuple_LInt_CInt_R",
        "state_push_Tuple_LInt_CInt_R", "state_pop_Tuple_LInt_CInt_R"})),
    ("tests/conformance/ch07_exn_composite.vera", frozenset({
        "exn_Option_LInt_R", "exn_Tuple_LInt_CInt_R"})),
    ("tests/conformance/ch07_exn_string.vera", frozenset({"exn_String"})),
    ("tests/conformance/ch07_state_old_composite.vera", frozenset({
        "state_get_Option_LInt_R", "state_put_Option_LInt_R",
        "state_push_Option_LInt_R", "state_pop_Option_LInt_R"})),
    # The #1205 scalar-alias collapse, unchanged by the composite one.
    ("tests/conformance/ch07_state_alias.vera", frozenset({
        "state_get_Nat", "state_put_Nat", "state_push_Nat", "state_pop_Nat"})),
)


@pytest.mark.parametrize(
    ("rel", "expected"), _STABLE_SYMBOLS, ids=[s[0] for s in _STABLE_SYMBOLS],
)
def test_family_symbols_are_stable(rel: str, expected: frozenset[str]) -> None:
    """The emitted family symbols of a corpus program, pinned exactly.

    These are the ABI: a host binds ``state_get_<family>`` by name, so a
    renderer change that renames a family silently breaks every host that
    already provides it.  Asserting the exact set (not a subset) catches a
    rename, an extra family, and a dropped one alike.
    """
    result = _compile_path(_ROOT / rel)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, [(d.error_code, d.description[:90]) for d in hard]
    assert _families(result.wat) == set(expected)


# =====================================================================
# (7) The measured radius: every corpus file the flip moved
# =====================================================================

# The whole `.vera` corpus (examples, conformance, the PR #1202 probe corpus)
# was captured before and after: `vera check --json` for every program,
# `vera run` for every probe, and the emitted `state_*` / `exn_*` symbols for
# everything that compiles.  SIX shapes differ, in two classes:
#
#   (a) two spellings of one cell now SHARE it, so the program computes a
#       different — and correct — value;
#   (b) the family symbol RENAMES from the source spelling to the resolved
#       cell (and, where both spellings appear, two families become one).
#
# No `check` diagnostic moved anywhere.  Pinning the whole set (not a sample)
# is what makes "something else also moved" a finding rather than noise.
#
# Each shape was measured on a probe program and now lives in the conformance
# suite, which is where the promotion put it; the entry point named here is
# the one whose value the probe pinned, so the assertions are the measured
# ones and not a re-baseline.
_C8_DIVERGENT: tuple[
    tuple[str, str | None, int | str, frozenset[str], str], ...
] = (
    (
        "ch07_state_composite_alias_cross_spelling.vera", None, 7, frozenset({
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(a)+(b) `State<MaybeInt>` handler around a `State<Option<Int>>` "
        "callee: EIGHT symbols (two families) collapse to four, and the "
        "program goes -1 -> 7 — the callee's write is now visible",
    ),
    (
        "ch07_state_composite_alias.vera", "roundtrip", 3, frozenset({
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(b) `state_*_MaybeInt` -> `state_*_Option_LInt_R`; single spelling, "
        "so the value is unchanged",
    ),
    (
        "ch07_state_composite_alias.vera", "put_then_read", 42, frozenset({
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(b) the same rename with a `match get(())` scrutinee",
    ),
    (
        "ch08_state_alias_per_module.vera", None, 16, frozenset({
            "state_get_Nat", "state_put_Nat",
            "state_push_Nat", "state_pop_Nat",
            "state_get_Option_LInt_R", "state_put_Option_LInt_R",
            "state_push_Option_LInt_R", "state_pop_Option_LInt_R"}),
        "(b) two modules declare `Hid<T>` differently — the module's `= T` "
        "stays the `Nat` family, the importer's `= Option<T>` renames from "
        "`Hid<Int>` to `Option<Int>`: each resolved in ITS OWN namespace",
    ),
    (
        "ch07_exn_string_alias.vera", "catch_text", "caught: negative",
        frozenset({"exn_String"}),
        "(b) `exn_Name` -> `exn_String` for `type Name = String`; the "
        "two-i32 payload still arrives intact",
    ),
    (
        "ch07_exn_string_alias.vera", "catch_length", 3,
        frozenset({"exn_String"}),
        "(b) `exn_Msg` -> `exn_String`, same pair payload through "
        "`string_length`",
    ),
)

_CONFORMANCE = _ROOT / "tests" / "conformance"


@pytest.mark.parametrize(
    ("rel", "fn", "expected", "families", "why"),
    _C8_DIVERGENT,
    ids=[f"{d[0]}::{d[1] or 'main'}" for d in _C8_DIVERGENT],
)
def test_moved_corpus_file_lands_where_it_was_measured(
    rel: str, fn: str | None, expected: int | str, families: frozenset[str],
    why: str,
) -> None:
    """Each shape the flip moved, at the symbols AND the value it moved to.

    Asserting the value as well as the symbol set is what separates "the
    families collapsed" from "the families collapsed onto the right cell":
    a merge into the WRONG family also produces one symbol set.
    """
    result = _compile_path(_CONFORMANCE / rel)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, (
        f"{rel} should compile clean — {why}\n"
        f"got: {[(d.error_code, d.description[:90]) for d in hard]}"
    )
    assert _families(result.wat) == set(families), why
    ran = execute(result) if fn is None else execute(result, fn_name=fn)
    assert ran.value == expected, why


def test_moved_set_is_exactly_this_size() -> None:
    """Every pinned entry is distinct, and each names a file that exists.

    A count alone would pass on a table that repeated one entry six times, or
    that named a program since renamed away; this pins the shape of the table
    itself.  That the table is the WHOLE measured radius rather than a sample
    is the corpus sweep's claim, not this test's (PR #1224 review).
    """
    assert len(_C8_DIVERGENT) == 6
    assert len({(d[0], d[1]) for d in _C8_DIVERGENT}) == 6
    for rel, *_ in _C8_DIVERGENT:
        assert (_CONFORMANCE / rel).is_file(), rel
