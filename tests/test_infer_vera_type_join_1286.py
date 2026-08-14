"""#1286: the Vera-level type namers must join over `if` / `match`, not read
one branch.

#1276 fixed the WAT result-type deciders (`_infer_expr_wasm_type`,
`_infer_block_result_type`, `_infer_match_result_type`) to take the FIRST
branch that yields a type.  Their Vera-level siblings — the two consultors that
name the type of an expression for array layout and for generic clone naming —
kept the one-branch read:

* `InferenceMixin._infer_vera_type` (vera/wasm/inference.py, the WASM
  call-rewrite side) read `then_branch` only, and `arms[0]` only;
* `Monomorphizer._infer_vera_type_name` (vera/monomorphize.py, the
  instantiation-discovery side) read `then_branch` only, and had no
  `MatchExpr` arm at all.

A branch whose every path `throw`s names no type.  Reading only that branch
answered `None` for the whole expression, and the two symptoms below both
arrived from check-green (and, where a contract is present, verify-green)
source:

* as an **array-literal element**, `None` raised `CodegenSkip` and the whole
  enclosing function was dropped with the loud [E602] note — a declared
  `public fn main` that is simply not in the exports;
* as a **generic argument**, `None` left the type variable unbound, so
  discovery fell to the phantom-var default and emitted `idg$Bool` for an
  `Int` argument: `Invalid input WebAssembly code ... type mismatch: expected
  i32, found i64` at load.

The `match`-argument case was broken in BOTH directions, which is why the fix
lands on both consultors together: with every arm completing, the rewrite named
`idg$Int` from arm 0 while discovery — having no arm for `MatchExpr` — named
the phantom default, and the caller was dropped on a dangling target.  The
clone-name agreement contract (#772) is what makes the pair, not the single
function, the unit of repair.

The join property under test is order-invariance: which branch is written first
must not change the answer.  Every witness below therefore comes with its
arm-swapped twin, and the pair must agree.
"""

from __future__ import annotations

import os
import tempfile

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.parser import parse_to_ast


# ---------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------

# The array-literal witness: the FIRST element is an `if` whose `then` branch
# throws.  `_infer_array_element_type` -> `_infer_vera_type` named nothing, and
# `_translate_array_lit` raised `CodegenSkip`.  `%s` selects which branch
# carries the throw, so the arm-swapped twin is the same program written the
# other way round.
_ARRAY_IF = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      0
    }
  } in {
    let @Array<Int> = [if %s then { throw(true) } else { 42 }, 7];
    @Array<Int>.0[1]
  }
}
"""

# The `match` spelling of the same element position: arm 0 throws.
_ARRAY_MATCH = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      0
    }
  } in {
    let @Array<Int> = [match Some(3) { %s }, 7];
    @Array<Int>.0[1]
  }
}
"""

# The pair-representation element (#841/#1045 width class): a `String` element
# is an i32 pair, so the drop is not specific to a scalar element width.
_ARRAY_STRING = """\
public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      "caught"
    }
  } in {
    let @Array<String> = [if %s then { throw(true) } else { "aa" }, "bb"];
    @Array<String>.0[1]
  }
}
"""

_GENERIC_PRELUDE = """\
private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

"""

# The instantiation witness: `T` is fixed by an argument whose `then` branch
# throws.  Discovery named the phantom-var default and the module failed to
# load.
_GENERIC_IF = _GENERIC_PRELUDE + """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      0
    }
  } in {
    idg(if %s then { throw(true) } else { 42 })
  }
}
"""

# The `match` twin of the instantiation witness.
_GENERIC_MATCH = _GENERIC_PRELUDE + """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      0
    }
  } in {
    idg(match Some(3) { %s })
  }
}
"""

# The consultor-agreement witness: EVERY arm completes, so nothing diverges —
# the failure was purely the missing discovery-side `MatchExpr` arm against the
# rewrite's arm-0 read.  Kept separate from the divergence witnesses because it
# fails for the other reason, and a fix to one consultor alone leaves it red.
_GENERIC_MATCH_TOTAL = _GENERIC_PRELUDE + """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  idg(match Some(3) { %s })
}
"""

# A constructor FIELD behind the same conditional: `_get_arg_type_info_wasm`
# reads the field through `_infer_vera_type`, so `Box<T>` bound nothing and the
# unboxing clone was named for the wrong `T`.
_CTOR_FIELD = """\
public data Box<T> {
  MkBox(T)
}

private forall<T> fn unbox(@Box<T> -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box<T>.0 {
    MkBox(@T) -> @T.0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      0
    }
  } in {
    unbox(MkBox(if %s then { throw(true) } else { 42 }))
  }
}
"""

# `%s` fillers.  For `if`, the condition selects the branch statically written
# first; the swapped twin negates it and exchanges the branch bodies, so the
# THROWING branch moves from `then` to `else`.  For `match`, the arms are
# reordered.  Either way the program means the same thing and must answer the
# same value.
_IF_DIVERGENT_FIRST = "false"
_IF_COMPLETING_FIRST = "true"

_MATCH_DIVERGENT_FIRST = "None -> throw(true), Some(@Int) -> @Int.0"
_MATCH_COMPLETING_FIRST = "Some(@Int) -> @Int.0, None -> throw(true)"

_MATCH_TOTAL_DIVERGENT_FIRST = "None -> 0, Some(@Int) -> @Int.0"
_MATCH_TOTAL_COMPLETING_FIRST = "Some(@Int) -> @Int.0, None -> 0"


def _if_swapped(template: str) -> str:
    """The `if` witness with the throwing branch moved to `else`.

    The bodies are exchanged along with the condition, so the same branch
    still runs — only its written position changes.
    """
    return (template % _IF_COMPLETING_FIRST).replace(
        "then { throw(true) } else { 42 }", "then { 42 } else { throw(true) }",
    ).replace(
        'then { throw(true) } else { "aa" }',
        'then { "aa" } else { throw(true) }',
    )


# (label, divergent-first source, arm-swapped source, expected value)
_WITNESSES: list[tuple[str, str, str, object]] = [
    (
        "array_lit_if",
        _ARRAY_IF % _IF_DIVERGENT_FIRST,
        _if_swapped(_ARRAY_IF),
        7,
    ),
    (
        "array_lit_match",
        _ARRAY_MATCH % _MATCH_DIVERGENT_FIRST,
        _ARRAY_MATCH % _MATCH_COMPLETING_FIRST,
        7,
    ),
    (
        "array_lit_string_element",
        _ARRAY_STRING % _IF_DIVERGENT_FIRST,
        _if_swapped(_ARRAY_STRING),
        "bb",
    ),
    (
        "generic_arg_if",
        _GENERIC_IF % _IF_DIVERGENT_FIRST,
        _if_swapped(_GENERIC_IF),
        42,
    ),
    (
        "generic_arg_match",
        _GENERIC_MATCH % _MATCH_DIVERGENT_FIRST,
        _GENERIC_MATCH % _MATCH_COMPLETING_FIRST,
        3,
    ),
    (
        "generic_arg_match_total",
        _GENERIC_MATCH_TOTAL % _MATCH_TOTAL_DIVERGENT_FIRST,
        _GENERIC_MATCH_TOTAL % _MATCH_TOTAL_COMPLETING_FIRST,
        3,
    ),
    (
        "constructor_field_if",
        _CTOR_FIELD % _IF_DIVERGENT_FIRST,
        _if_swapped(_CTOR_FIELD),
        42,
    ),
]


# ---------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------


def _compile(source: str) -> CompileResult:
    """Parse, typecheck, and compile — the `vera run` pipeline.

    Monomorphization consumes the checker's artifacts, so the plain
    parse-and-compile shortcut would not exercise the clone-naming path these
    witnesses turn on.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(
            program, source, file=path, collect_module_artifacts=True,
        )
        errors = [d.description for d in diags if d.severity == "error"]
        assert not errors, f"typecheck errors: {errors}"
        return codegen_compile(
            program, source=source, file=path,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
            module_artifacts=arts.module_artifacts,
        )
    finally:
        os.unlink(path)


def _run(source: str) -> object:
    """Compile and execute `main`, asserting it survived codegen.

    The drop symptom is quiet at the value level — a skipped function simply
    is not exported — so the export is asserted before the call, and the skip
    NOTE is asserted separately below.
    """
    result = _compile(source)
    assert "main" in result.exports, (
        "check-green source lost `main` from the compiled exports; notes: "
        + "; ".join(d.description for d in result.diagnostics)
    )
    return execute(result, fn_name="main").value


# ---------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------


@pytest.mark.parametrize(
    ("label", "source", "expected"),
    [
        pytest.param(lbl, src, exp, id=lbl)
        for lbl, src, _swapped, exp in _WITNESSES
    ],
)
def test_divergent_first_branch_still_names_the_type(
    label: str, source: str, expected: object,
) -> None:
    """The witness: a branch that names nothing must not decide the answer."""
    assert _run(source) == expected


@pytest.mark.parametrize(
    ("label", "source", "swapped", "expected"),
    [pytest.param(*row, id=row[0]) for row in _WITNESSES],
)
def test_the_answer_does_not_depend_on_branch_order(
    label: str, source: str, swapped: str, expected: object,
) -> None:
    """The join property: writing the branches the other way round is the same
    program, so the two spellings must compile to the same answer.

    This is the differential the fix is pinned by — it compares the two sides
    of the invariant rather than asserting one remembered value, so it stays
    meaningful if the expected value itself is ever renegotiated.
    """
    divergent_first = _run(source)
    completing_first = _run(swapped)
    assert divergent_first == completing_first, (
        f"{label}: branch order changed the answer "
        f"({divergent_first!r} vs {completing_first!r})"
    )
    assert completing_first == expected


def test_no_codegen_skip_note_on_the_array_witness() -> None:
    """The absence half: the drop announces itself as an [E602] note, and a
    value assertion alone cannot see it once the function is gone."""
    result = _compile(_ARRAY_IF % _IF_DIVERGENT_FIRST)
    skips = [
        d.description for d in result.diagnostics
        if "could not infer array literal element type" in d.description
    ]
    assert not skips, f"array literal skipped despite a typed branch: {skips}"


@pytest.mark.parametrize(
    ("label", "source"),
    [
        pytest.param("if", _GENERIC_IF % _IF_DIVERGENT_FIRST, id="if"),
        pytest.param(
            "match", _GENERIC_MATCH % _MATCH_DIVERGENT_FIRST, id="match",
        ),
        pytest.param(
            "match_total",
            _GENERIC_MATCH_TOTAL % _MATCH_TOTAL_DIVERGENT_FIRST,
            id="match_total",
        ),
    ],
)
def test_the_clone_is_named_for_the_real_instantiation(
    label: str, source: str,
) -> None:
    """The positional half: the value could be right for the wrong reason, so
    pin WHICH clone the module carries.

    `idg$Bool` is the phantom-var default — the name discovery falls to when
    the argument binds nothing — and it is an i32 clone reached with an i64
    argument.  Asserting its absence is what distinguishes "the type was
    inferred" from "the default happened to work".
    """
    wat = _compile(source).wat
    assert "$idg$Int" in wat, f"{label}: no Int clone in the module:\n{wat}"
    assert "$idg$Bool" not in wat, (
        f"{label}: the phantom-var default was instantiated instead of the "
        f"argument's real type:\n{wat}"
    )
