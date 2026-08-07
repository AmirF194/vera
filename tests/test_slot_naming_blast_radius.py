"""The measured blast radius of the #1208 slot-naming core flip.

Every subsystem downstream of the checker — the monomorphizer, codegen, the
verifier, and the SMT layer — now derives slot names and slot-reference keys
from :mod:`vera.naming`, on the BIND side and the REFERENCE side together.
The rule itself did not change: ``tests/test_slot_naming.py`` states it and
``tests/test_slot_naming_differential.py`` proves the module renders what the
checker renders.  What changed is WHO renders, and this file pins what that
moved.

The whole `.vera` corpus (examples, conformance programs, the PR #1202 probe
corpus — 510 files) was captured before and after: ``vera check --json``
diagnostics for every program, plus ``vera run`` for every probe.  SIX files
differ, all in ``tests/probes/``, all one class:

    (a) a program that died with a dangling-slot ``[E699]`` now resolves and
        runs, with the value the CHECKER's binding rule gives.

No ``check`` diagnostic moved anywhere in the corpus — the checker was already
delegating (commit 1ae8b368), so its answers were the fixed point the others
moved onto.  No example and no conformance program is affected: the shapes
that diverged need an alias in TYPE-ARGUMENT position, which the probe corpus
was written to reach and the rest of the corpus does not contain.

The tests below re-run only those six plus five sentinels.  A regression that
re-splits the naming is caught here as a named file going back to ``[E699]``,
not as a diffuse failure somewhere in the suite.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.checker import typecheck_with_artifacts

_ROOT = Path(__file__).resolve().parent.parent
_PROBES = _ROOT / "tests" / "probes" / "state_handlers"


# =====================================================================
# The divergent set — every file the flip moved, and what it moved to
# =====================================================================

# (relative path, entry fn, arguments, expected value, one-line change class)
# The entry is each file's own `main` where it has one — the probe corpus
# writes its expectation into `main`'s contract — and the sole public function
# otherwise.
_DIVERGENT: tuple[tuple[str, str, tuple[int, ...], int, str], ...] = (
    (
        "alias_families/p2_family_nested_alias.vera", "main", (), 7,
        "(a) `State<Id<Id<Nat>>>`: the twice-applied alias cell dangled at "
        "[E699]; now runs, and `main`'s own `ensures(@Int.result == 7)` is "
        "the value oracle",
    ),
    (
        "alias_families/p_nested_app.vera", "go", (5,), 5,
        "(a) the same nested application as a bare handler round-trip: "
        "[E699] -> the cell returns what was put",
    ),
    (
        "clause_scoping/p1b_nested_alias_clause_value.vera", "main", (), 5,
        "(a) pattern `@Option<Id<Id<Int>>>`, `with`-ref `@Option<Id<Int>>.0`: "
        "[E699] -> 5, the STATE, which is what the file's header records the "
        "checker as meaning (9 would be the put argument)",
    ),
    (
        "clause_scoping/p1d_single_alias_ref.vera", "main", (), 5,
        "(a) an alias-SPELLED reference to a canonically-spelled binding: "
        "[E699] -> 5, the value the file's header predicted for the checker",
    ),
    (
        "clause_scoping/p4b_alias_arg_pattern.vera", "main", (), 100,
        "(a) alias inside a composite clause pattern: [E699] -> 100, the "
        "STATE (bound last, so index 0), per the file's header; codegen's old "
        "separate stack would have given the put argument 7",
    ),
    (
        "clause_scoping/p4e_fn_param_baseline.vera", "main", (), 5,
        "(a) the same split on an ordinary fn parameter, no handler: a "
        "parameter written `@Option<Cnt>` read as `@Option<Int>.0` was "
        "[E699]; `--explain-slots` names that parameter `@Option<Int>` and it "
        "now resolves",
    ),
)

# Programs that exercise slot naming hard and were NOT touched — the control
# that says the flip moved what it aimed at and nothing else.  Kept small on
# purpose: the exhaustive sweep is the capture, this is its sentinel.
_SENTINELS: tuple[str, ...] = (
    "examples/effect_handler.vera",
    "examples/generics.vera",
    "tests/conformance/ch03_slot_indexing.vera",
    "tests/conformance/ch07_state_composite.vera",
    "tests/conformance/ch07_state_alias.vera",
)


def _compile_file(path: Path) -> object:
    """Parse + resolve + check + compile *path* through the CLI's pipeline."""
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
        f"{[(d.error_code, d.description[:70]) for d in errors]}"
    )
    return codegen_compile(
        program, source=source, file=str(path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
    )


@pytest.mark.parametrize(
    ("rel", "fn", "args", "expected", "why"),
    _DIVERGENT,
    ids=[d[0] for d in _DIVERGENT],
)
def test_divergent_file_now_runs_with_the_checkers_semantics(
    rel: str, fn: str, args: tuple[int, ...], expected: int, why: str,
) -> None:
    """Each pinned file compiles clean and returns the CHECKER's value.

    Before the flip every one of these raised the codegen dangling-slot
    invariant on a program the checker had accepted: the binding was minted
    under one rendering and the reference looked up under another.  The value
    is asserted, not merely the absence of the error — a program that
    resolves to the WRONG member of a merged class also stops dangling.
    """
    result = _compile_file(_PROBES / rel)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, (
        f"{rel} should compile clean now — {why}\n"
        f"got: {[(d.error_code, d.description[:90]) for d in hard]}"
    )
    assert execute(result, fn_name=fn, args=list(args)).value == expected, why


def test_divergent_set_is_exactly_this_size() -> None:
    """The pinned set is the WHOLE measured radius, not a sample.

    If a later change moves a seventh file, the capture that produced this
    list has to be re-run and the new file classified — the point of pinning
    the set is that "something else also moved" is a finding, not noise.
    """
    assert len(_DIVERGENT) == 6
    assert len({d[0] for d in _DIVERGENT}) == 6
    for rel, *_ in _DIVERGENT:
        assert (_PROBES / rel).is_file(), rel


@pytest.mark.parametrize("rel", _SENTINELS)
def test_sentinel_programs_are_unmoved(rel: str) -> None:
    """Slot-heavy programs outside the radius still compile clean.

    These carry State handlers, generic containers, and the canonical
    De Bruijn indexing test — everything the flip touches — through NO alias
    in type-argument position, which is what keeps them on the far side of
    the change.  A regression that renders more (or less) than the checker
    does would not respect that line.
    """
    result = _compile_file(_ROOT / rel)
    hard = [d for d in result.diagnostics if d.severity == "error"]
    assert not hard, (
        f"{rel} is a sentinel and must stay clean; got: "
        f"{[(d.error_code, d.description[:90]) for d in hard]}"
    )


def test_explain_slots_names_the_merged_parameter_stack() -> None:
    """``--explain-slots`` is the user-facing oracle for the merge, and it
    reports the checker's names (#1208).

    ``p4e_fn_param_baseline`` is the corpus's only SIGNATURE-level rename: a
    parameter written ``@Option<Cnt>`` under ``type Cnt = Int``.  The table
    must name it ``Option<Int>`` — the key the body's ``@Option<Int>.0``
    looks up and the key codegen now binds — because a table that still said
    ``Option<Cnt>`` would be telling the user something no consumer agrees
    with, which is how this bug class stayed invisible.
    """
    from vera.naming import alias_env_from_declarations
    from vera.slots import slot_table

    path = _PROBES / "clause_scoping/p4e_fn_param_baseline.vera"
    program = parse_to_ast(path.read_text(encoding="utf-8"))
    env = alias_env_from_declarations(program.declarations)
    fn = next(t.decl for t in program.declarations
              if getattr(t.decl, "name", None) == "f")
    assert slot_table(fn.params, env) == {"Option<Int>": [1]}


# =====================================================================
# The module-scope hazard the flip opened, and closed (#1208 / #1111)
# =====================================================================

_MODULE_GENERIC_LIB = """\
module lib;
type Cnt = Int;

public forall<A> fn pick(@Option<Cnt>, @Option<A> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Cnt>.0 {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""

_MODULE_GENERIC_MAIN = """\
import lib;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  lib::pick(Some(11), Some(22))
}
"""

_LOCAL_GENERIC = """\
type Cnt = Int;

private forall<A> fn pick(@Option<Cnt>, @Option<A> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Cnt>.0 {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Some(11), Some(22))
}
"""


def _run_files(tmp_path: Path, files: dict[str, str]) -> int | None:
    """Write *files*, resolve + compile + run ``main.vera``'s ``main``."""
    from vera.resolver import ModuleResolver

    main_file = tmp_path / "main.vera"
    for rel, content in files.items():
        p = tmp_path / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    source = main_file.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=tmp_path)
    resolved = resolver.resolve_imports(program, main_file)
    assert not resolver.errors, [e.description for e in resolver.errors]
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_file), resolved_modules=resolved,
    )
    assert not [d for d in diags if d.severity == "error"], [
        (d.error_code, d.description[:80]) for d in diags
        if d.severity == "error"
    ]
    result = codegen_compile(
        program, source=source, file=str(main_file),
        resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
    )
    assert not [d for d in result.diagnostics if d.severity == "error"], [
        (d.error_code, d.description[:90]) for d in result.diagnostics
        if d.severity == "error"
    ]
    return execute(result, fn_name="main").value


def test_local_generic_merges_on_substitution(tmp_path: Path) -> None:
    """The control, in ONE namespace.

    `pick(@Option<Cnt>, @Option<A>)` at `A = Int` collapses two formerly
    distinct classes into one `Option<Int>` stack, so the body's
    `@Option<Cnt>.0` — index 0 of its own class before substitution — must be
    recounted to index 1 (parameter 2 is the more recent binding).  It reads
    parameter 1, which is `Some(11)`; parameter 2 is `Some(22)`, so the value
    names which binding the recount landed on.
    """
    assert _run_files(tmp_path, {"main.vera": _LOCAL_GENERIC}) == 11


def test_imported_generic_merges_in_its_own_namespace(
    tmp_path: Path,
) -> None:
    """The SAME generic, imported — and the reason `monomorphize_fn` takes
    an alias environment rather than reading the driver's (#1208 / #1111).

    `Cnt` is a MODULE-LOCAL alias (spec §8.4.1): it is not in the importer's
    namespace at all.  The De Bruijn recount has to render the clone's
    binders in `lib`'s namespace, where both parameters are `Option<Int>` and
    the merge is visible.  Rendered in the importer's, parameter 1 stays the
    opaque `Option<Cnt>`, no merge is seen, the index is left at 0 — and the
    clone, which codegen emits under `lib`'s own alias scope, then resolves
    that reference onto parameter 2.  Silently: right arity, right type,
    wrong argument (22).

    The corpus could not catch this — it holds no cross-module generic over a
    module-local alias — so it is pinned here against its single-namespace
    control above.
    """
    got = _run_files(tmp_path, {
        "main.vera": _MODULE_GENERIC_MAIN,
        "lib.vera": _MODULE_GENERIC_LIB,
    })
    assert got == 11, (
        f"expected parameter 1 (11); got {got}. 22 means the reindex was "
        f"computed against the importer's alias namespace, not lib's."
    )
    assert got == _run_files(
        tmp_path / "local", {"main.vera": _LOCAL_GENERIC})
