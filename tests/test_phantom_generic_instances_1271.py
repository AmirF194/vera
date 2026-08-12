"""#1271: discovery inside a still-generic scope must not instantiate a callee
at an ENCLOSING scope's type VARIABLE.

Inside ``forall<U> fn helper``, the call ``pick(@U.1, @U.0)`` binds ``pick``'s
type variable to the *name* ``U`` — a structural fact about the scope, not a
concrete type.  Discovery recorded that vector anyway, so codegen emitted a
``pick$U`` clone whose ``@U`` parameter has no WASM type and which the
compilability pass then skipped with a loud ``[E604]`` on every
generic-under-generic program.  The answer was always right; the noise is what
kept the #1223 regression shapes out of the conformance suite, since
``scripts/check_e602_clean.py`` rejects any conformance program that emits one.

The real instantiation is the one discovered once the enclosing scope is bound:
``parent$Int``'s helper clone is ``helper$Bool``, and ITS body yields
``pick$Bool``.  Filtering the phantom must leave that one untouched — so every
case below asserts the concrete clone is still emitted, not merely that the
phantom is gone.

Both sides drive the same walk (``Monomorphizer.collect_calls_in_node``), so the
filter lands once and the #732 differential in
``tests/test_monomorphize_differential.py`` holds by construction.
"""

from __future__ import annotations

import os
import tempfile

import pytest

from tests.test_generic_under_generic_callees_1223 import _CASES
from vera.ast import FnDecl
from vera.codegen import execute
from vera.codegen.api import CompileResult
from vera.codegen.core import CodeGenerator
from vera.codegen.monomorphize import MonomorphizationMixin
from vera.parser import parse_file
from vera.transform import transform

# A mutual-recursion shape: two sibling generic helpers under a generic parent,
# each calling the other's family, so the phantom appears at BOTH helpers'
# variables AND at the sibling helper itself (`leaf$U`, `leaf$V`,
# `parent$Int$where$b$U`).  Recorded during PR C1's review as a shape where the
# post-#1223 compiler emits MORE phantoms than base — the filter must collapse
# all of them in one pass.
_MUTUAL = """
private forall<W> fn leaf(@W, @W -> @W)
  requires(true)
  ensures(true)
  effects(pure)
{
  @W.0
}

private forall<T> fn parent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if a(true, false) then { 7 } else { 3 }
}
where {
  forall<U> fn a(@U, @U -> @U)
    requires(true)
    ensures(true)
    effects(pure)
  {
    b(leaf(@U.1, @U.0), @U.0)
  }
  forall<V> fn b(@V, @V -> @V)
    requires(true)
    ensures(true)
    effects(pure)
  {
    leaf(@V.1, @V.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(1)
}
"""

_ALL_CASES = [
    *[(label, src) for label, src, _ in _CASES],
    ("mutual_recursion", _MUTUAL),
]

# Which concrete clone each shape must STILL emit once the phantoms are gone.
_CONCRETE_REQUIRED = {
    "user_generic": "pick$Bool",
    "prelude_generic": "option_unwrap_or$Bool",
    "depth_two": "pick$Bool",
    "nongeneric_parent_control": "pick$Bool",
    "mutual_recursion": "leaf$Bool",
}


def _compile_spied(source: str) -> tuple[CompileResult, set[str]]:
    """``(compile result, emitted mono-clone names)``.

    The clone NAMES are what a phantom is visible as; the result carries what it
    costs.  Both come off ONE compile so they cannot disagree.
    """
    registered: set[str] = set()
    orig = MonomorphizationMixin._monomorphize

    def _spy(self: object, program: object) -> list[FnDecl]:
        out = orig(self, program)  # type: ignore[arg-type]
        registered.update(d.name for d in out)
        return out

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        gen = CodeGenerator(source=source, file=path)
        MonomorphizationMixin._monomorphize = _spy  # type: ignore[assignment,method-assign]
        try:
            result = gen.compile_program(program)  # type: ignore[arg-type]
        finally:
            MonomorphizationMixin._monomorphize = orig  # type: ignore[assignment,method-assign]
    finally:
        os.unlink(path)
    return result, registered


def _compile_result(source: str) -> CompileResult:
    return _compile_spied(source)[0]


def _compile_probe(source: str) -> tuple[set[str], list[tuple[str, str]]]:
    """``(emitted mono-clone names, [(code, description)] for E602/E604/E605)``."""
    result, registered = _compile_spied(source)
    skips = [
        (d.error_code or "?", d.description or "")
        for d in result.diagnostics
        if d.error_code in ("E602", "E604", "E605")
    ]
    return registered, skips


# Every type variable any of the shapes binds.  A clone name ending in one of
# these is a phantom by construction: no Vera type is named `U`.  `Q` is the
# primitive-binder control's variable — deliberately NOT a type name, which is
# what makes that control distinguish "subtract the primitives" from "never
# filter anything".
_TYPE_VARS = ("T", "U", "V", "W", "Q")


def _phantoms(names: set[str]) -> set[str]:
    return {
        n for n in names
        if n.rsplit("$", 1)[-1] in _TYPE_VARS
    }


# A `forall` binder may legally be SPELLED like a primitive.  `forall<Int> fn
# idg` makes `Int` a type variable in ITS signature and nowhere else, so a
# sibling generic instantiated at the real `Int` must still be cloned.  The
# type-variable test therefore subtracts the primitives too: a name that names
# a TYPE is a type here, whatever some other signature calls its variable.
def _primitive_binder(binder: str, literal: str, ret: str) -> str:
    """A `forall<binder>` template beside a sibling instantiated at the REAL
    type that binder is spelled like — the discriminating pair."""
    return f"""
private forall<{binder}> fn idg(@{binder} -> @{binder})
  requires(true)
  ensures(true)
  effects(pure)
{{
  @{binder}.0
}}

private forall<W> fn idw(@W -> @W)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @W.0
}}

public fn main(@Unit -> @{ret})
  requires(true)
  ensures(true)
  effects(pure)
{{
  idw({literal})
}}
"""


# (binder spelling, the sibling's argument, its type).  Each row's sibling
# instantiates at exactly the type its binder is spelled like, so a row is only
# green if THAT primitive survived the subtraction — a shared `idw(5)` would
# have made every row but `Int` pass for free.
_PRIMITIVE_BINDERS = [
    ("Int", "5", "Int"),
    ("Bool", "true", "Bool"),
    ("String", '"x"', "String"),
    ("Float64", "1.5", "Float64"),
]


class TestPrimitiveSpelledBinder:
    """The type-variable universe must not swallow the primitives.

    Subtracting only the ADTs and aliases left `Int`, `Bool`, `String`, … as
    "type variables" whenever ANY signature in the program bound one as a
    `forall` binder — so a sibling's genuine `idw<Int>` was filtered, no clone
    was emitted, and `main` was dropped with `[E602] call target 'idw$Int' not
    registered` from a program that ran fine before the filter existed.

    The direction of the fix errs toward "it is a real type": a `forall<Int>`
    binder that shadows the primitive keeps its own pre-existing `[E604]` noise
    (the phantom `idg$Int` clone), which is the failure mode that was already
    there, instead of silently costing every OTHER instantiation at that type.
    Whether the checker should reject a primitive-spelled binder outright is a
    language question, deliberately not decided here.
    """

    @pytest.mark.parametrize(
        ("binder", "literal", "ret"),
        [pytest.param(*row, id=row[0]) for row in _PRIMITIVE_BINDERS],
    )
    def test_sibling_instantiation_survives(
        self, binder: str, literal: str, ret: str,
    ) -> None:
        names, _ = _compile_probe(_primitive_binder(binder, literal, ret))
        assert f"idw${binder}" in names, (
            f"a `forall<{binder}>` binder must not filter the sibling's real "
            f"idw<{binder}> — emitted {sorted(names)}"
        )

    @pytest.mark.parametrize(
        ("binder", "literal", "ret"),
        [pytest.param(*row, id=row[0]) for row in _PRIMITIVE_BINDERS],
    )
    def test_program_still_runs(
        self, binder: str, literal: str, ret: str,
    ) -> None:
        """The observable, not just the clone set: `main` must survive to the
        exports and hand back its argument."""
        result = _compile_result(_primitive_binder(binder, literal, ret))
        errors = [
            d.description for d in result.diagnostics if d.severity == "error"
        ]
        assert not errors, f"forall<{binder}>: codegen errors {errors}"
        expected = {"Int": 5, "Bool": True, "String": "x", "Float64": 1.5}
        assert execute(result, fn_name="main").value == expected[binder]

    def test_non_primitive_binder_control(self) -> None:
        """The control: a binder spelled `Q` names no type, so `Q` IS a type
        variable — and a phantom at it is still filtered.  Without this the
        primitive subtraction could have been a blanket "never filter" and
        looked identical on the rows above.

        `idg` is never called in this fixture, so its own template-only
        `[E604]` is expected and pre-existing (an uninstantiated generic
        template draws one whatever its binder is spelled) — the assertion is
        about phantom CLONES, which is what this filter governs.
        """
        names, _ = _compile_probe(_primitive_binder("Q", "5", "Int"))
        assert "idw$Int" in names, f"the real clone must survive: {sorted(names)}"
        assert not _phantoms(names), (
            f"a `Q` binder is a genuine type variable — a phantom at it must "
            f"still be filtered, got {sorted(_phantoms(names))}"
        )


@pytest.mark.parametrize(
    ("label", "source"),
    [pytest.param(lbl, s, id=lbl) for lbl, s in _ALL_CASES],
)
def test_no_phantom_clone_is_emitted(label: str, source: str) -> None:
    """No clone is keyed by a type VARIABLE, and no E602/E604/E605 skip is
    emitted — while the genuinely concrete clone still is."""
    names, skips = _compile_probe(source)
    assert not _phantoms(names), (
        f"{label}: instantiations at an enclosing scope's type variable were "
        f"emitted as clones: {sorted(_phantoms(names))} (from {sorted(names)})"
    )
    assert not skips, (
        f"{label}: the compile is not skip-clean — {skips}"
    )
    required = _CONCRETE_REQUIRED[label]
    assert required in names, (
        f"{label}: the filter removed the REAL instantiation too — "
        f"{required} is missing from {sorted(names)}"
    )
