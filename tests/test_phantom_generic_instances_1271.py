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


def _compile_probe(source: str) -> tuple[set[str], list[tuple[str, str]]]:
    """``(emitted mono-clone names, [(code, description)] for E602/E604/E605)``.

    The clone NAMES are what a phantom is visible as; the skip warnings are what
    it costs.  Both are read off one compile so they cannot disagree.
    """
    registered: set[str] = set()
    orig = MonomorphizationMixin._monomorphize

    def _spy(self: object, program: object) -> object:
        out = orig(self, program)  # type: ignore[arg-type]
        registered.update(d.name for d in out)  # type: ignore[attr-defined]
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
    skips = [
        (d.error_code or "?", d.description or "")
        for d in result.diagnostics
        if d.error_code in ("E602", "E604", "E605")
    ]
    return registered, skips


# Every type variable any of the shapes binds.  A clone name ending in one of
# these is a phantom by construction: no Vera type is named `U`.
_TYPE_VARS = ("T", "U", "V", "W")


def _phantoms(names: set[str]) -> set[str]:
    return {
        n for n in names
        if n.rsplit("$", 1)[-1] in _TYPE_VARS
    }


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
