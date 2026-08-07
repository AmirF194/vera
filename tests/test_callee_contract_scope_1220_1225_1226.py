"""A callee's contract is READ in the callee's own module (#1220, #1225, #1226).

Three ways the toolchain read an imported callee's contract as though it had
been written in the importer's file:

* #1220 — the ``Precondition:`` line of an E501 quoted the IMPORTER's source
  buffer at the callee's span, so the message showed whatever text sat on that
  line here (a plausible-looking `requires` from another function, or nothing
  at all when the callee's file is the longer one);
* #1225 — a bare-name call *inside* the callee's contract resolved through the
  IMPORTER's function registry, so the callee's ``requires`` / ``ensures`` was
  interpreted against a same-named local function's contract: a false Tier 1
  whose runtime traps, and the mirror spurious E501;
* #1226 — the refined-RETURN binder was the predicate's bare head identifier,
  so a refinement over a PARAMETERISED base pushed ``Box`` where the
  predicate's reference resolves ``Box<Nat>``: the return fact was dropped and
  a valid program rejected.

Every direction is asserted against a runtime oracle wherever the two can
disagree — a wrong namespace's two failure modes (an obligation that vanishes
and one that fires for no reason) look identical from inside the verifier, and
only `vera run` says which one a verdict is.
"""
from __future__ import annotations

import os
import tempfile
from pathlib import Path

import pytest

from vera.checker import typecheck
from vera.codegen import compile, execute
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.transform import transform
from vera.verifier import VerifyResult, verify


# =====================================================================
# Helpers
# =====================================================================

def _resolved(path: tuple[str, ...], source: str) -> ResolvedModule:
    """A ``ResolvedModule`` from source text, via a real temp file.

    ``delete=False`` + explicit unlink is the Windows-safe pattern (an open
    ``NamedTemporaryFile`` cannot be reopened there).
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        return ResolvedModule(
            path=path, file_path=Path(fp),
            program=transform(parse_file(fp)), source=source,
        )
    finally:
        os.unlink(fp)


def _verify_mod(source: str, modules: list[ResolvedModule]) -> VerifyResult:
    """Type-check and verify *source* against *modules*, asserting check-clean.

    Check-clean is the premise of every test here: a fixture that fails to
    type-check would satisfy a "no errors" assertion trivially.
    """
    prog = parse_to_ast(source)
    diags = typecheck(prog, source, resolved_modules=modules)
    check_errors = [d for d in diags if d.severity == "error"]
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verify(prog, source, resolved_modules=modules)


def _codes(result: VerifyResult) -> set[str]:
    return {d.error_code for d in result.diagnostics if d.severity == "error"}


def _e501(result: VerifyResult) -> str:
    """The single E501 message, asserting there is exactly one."""
    messages = [
        d.description for d in result.diagnostics
        if d.error_code == "E501" and d.severity == "error"
    ]
    assert len(messages) == 1, [
        (d.error_code, d.description[:80]) for d in result.diagnostics
    ]
    return messages[0]


def _run_mod(source: str, modules: list[ResolvedModule]) -> object:
    """Compile *source* with *modules* and call ``main`` — the runtime oracle.

    Raises :class:`WasmTrapError` when the program violates a contract at run
    time, which is exactly what a false Tier 1 has to be caught by.  Compiled
    through a real temp file, the Windows-safe way ``_resolved`` is.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        result = compile(
            transform(parse_file(fp)), source=source, file=fp,
            resolved_modules=modules,
        )
    finally:
        os.unlink(fp)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"unexpected codegen errors: {errors}"
    return execute(result, fn_name="main")


# =====================================================================
# #1220 — the quoted clause comes from the file that declared it
# =====================================================================

# `requires` sits on LINE 4 of this module.
_QUOTE_LIB = """\
module qlib;

public fn need3(@Option<Int> -> @Int)
  requires(@Option<Int>.0 == Some(3))
  ensures(true)
  effects(pure)
{
  0
}
"""

# ... and line 4 HERE is a different, entirely plausible `requires`.  Quoted
# out of this buffer the message reads as a real clause, so a reader has no
# way to tell it is the wrong one.
_QUOTE_MAIN = """\
import qlib(need3);

public fn main(@Int -> @Int)
  requires(@Int.0 != 424242)
  ensures(true)
  effects(pure)
{
  need3(Some(9))
}
"""


class TestE501QuotesTheDeclaringFile:
    """The ``Precondition:`` line quotes the CALLEE's own source (#1220)."""

    def test_the_callees_actual_requires_clause_is_quoted(self) -> None:
        result = _verify_mod(_QUOTE_MAIN, [_resolved(("qlib",), _QUOTE_LIB)])
        assert "requires(@Option<Int>.0 == Some(3))" in _e501(result), (
            _e501(result)
        )

    def test_the_importers_text_at_that_line_is_not_quoted(self) -> None:
        """The misattribution, not just the absence of the right text.

        Both files have a ``requires`` on line 4, so the pre-fix rendering
        produced a well-formed clause belonging to another function — the
        failure mode a "contains the right text" assertion alone would still
        pass if the message quoted BOTH.
        """
        result = _verify_mod(_QUOTE_MAIN, [_resolved(("qlib",), _QUOTE_LIB)])
        assert "424242" not in _e501(result), _e501(result)

    def test_a_local_callee_still_quotes_this_program(self) -> None:
        """Control: a same-file callee's clause is quoted as it always was."""
        source = """\
private fn need_positive(@Int -> @Int)
  requires(@Int.0 > 424242)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need_positive(1)
}
"""
        result = _verify_mod(source, [])
        assert "requires(@Int.0 > 424242)" in _e501(result), _e501(result)

    def test_a_qualified_call_quotes_the_declaring_file_too(self) -> None:
        """``mod::fn`` reaches the same renderer by a different lookup."""
        qualified = _QUOTE_MAIN.replace(
            "import qlib(need3);", "import qlib;",
        ).replace("need3(Some(9))", "qlib::need3(Some(9))")
        result = _verify_mod(qualified, [_resolved(("qlib",), _QUOTE_LIB)])
        message = _e501(result)
        assert "requires(@Option<Int>.0 == Some(3))" in message, message
        assert "424242" not in message, message


# The helper's `requires` is on line 18 — past the end of the importer, so the
# pre-fix rendering had no line to quote and dropped the `Precondition:` line
# entirely.  An imported GENERIC's helper, so its clause is reached through a
# monomorphized clone rather than the harvested registry.
_HELPER_LIB = """\
module hlib;

type Cnt = Bool;

public forall<T> fn f(@Array<Bool>, @Array<Int>, @T -> @Nat)
  requires(array_length(@Array<Bool>.0) == 3)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  help(@Array<Bool>.0, @Array<Int>.0)
}
where {
  fn help(@Array<Cnt>, @Array<Int> -> @Nat)
    requires(array_length(@Array<Cnt>.0) == 2)
    ensures(@Nat.result >= 0)
    effects(pure)
  {
    array_length(@Array<Int>.0)
  }
}
"""

_HELPER_MAIN = """\
import hlib(f);

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([true, false, true], array_range(0, 2), 9)
}
"""


class TestImportedGenericHelperClauseIsQuoted:
    """A clone's clause is quoted from the module that declared the generic.

    The clone's contract nodes are fresh — the harvested-clause pin cannot see
    them — so this is the case that needs the DECLARING-module scope, not the
    per-clause one: while the clone verifies, the buffer its spans number is
    its own module's.
    """

    def test_the_helpers_own_precondition_text_is_quoted(self) -> None:
        result = _verify_mod(_HELPER_MAIN, [_resolved(("hlib",), _HELPER_LIB)])
        message = _e501(result)
        assert "requires(array_length(@Array<Cnt>.0) == 2)" in message, message

    def test_the_violation_is_real(self) -> None:
        """The oracle: this E501 is a caught violation, not a spurious one.

        ``help``'s two parameters are two stacks in ``hlib`` (``Cnt = Bool``),
        so ``@Array<Cnt>.0`` is the length-3 array and the precondition really
        does fail.  Without this the quoting test above could be pinning the
        text of a message that should not exist.
        """
        modules = [_resolved(("hlib",), _HELPER_LIB)]
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(_HELPER_MAIN, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind
