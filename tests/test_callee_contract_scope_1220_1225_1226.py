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
    return execute(result, fn_name="main").value


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


# =====================================================================
# #1225 — a bare name in the callee's contract resolves in ITS module
# =====================================================================

# `cap` is PRIVATE, so nothing the importer writes can be the same function —
# and `guarded`'s precondition is written entirely in terms of it.
_CAP_LIB = """\
module caplib;

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 100)
  effects(pure)
{
  100
}

public fn guarded(@Int -> @Int)
  requires(@Int.0 < cap(0))
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def _cap_main(local_cap: int, argument: int) -> str:
    """An importer declaring its OWN ``cap`` and calling ``guarded``."""
    return f"""\
import caplib(guarded);

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == {local_cap})
  effects(pure)
{{
  {local_cap}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  guarded({argument}) + cap(0)
}}
"""


class TestCalleeContractCallsResolveInItsModule:
    """The callee's ``requires`` is read against the callee's own ``cap``."""

    def test_the_false_tier1_is_reported_and_the_run_agrees(self) -> None:
        """`guarded(500)` violates `500 < 100`; the importer's cap is 1000.

        Read through the importer's registry the precondition is `500 < 1000`
        and verification reported all-Tier-1 clean on a program whose run traps
        — a false Tier 1, the direction that matters.
        """
        modules = [_resolved(("caplib",), _CAP_LIB)]
        source = _cap_main(local_cap=1000, argument=500)
        result = _verify_mod(source, modules)
        assert "E501" in _codes(result), (
            "the callee's precondition was proved against the IMPORTER's "
            f"`cap`: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(source, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_mirror_correct_program_is_accepted(self) -> None:
        """The other direction: `guarded(50)` satisfies `50 < 100`.

        The importer's cap is 0, so reading the precondition through its
        registry made it `50 < 0` and rejected a program that runs fine.  A fix
        that merely stopped checking imported preconditions would pass here and
        fail the test above, and vice versa.
        """
        modules = [_resolved(("caplib",), _CAP_LIB)]
        source = _cap_main(local_cap=0, argument=50)
        result = _verify_mod(source, modules)
        assert not _codes(result), (
            f"valid cross-module call spuriously rejected: {_codes(result)}"
        )
        assert _run_mod(source, modules) == 50

    def test_no_collision_control_discharges_and_violates_honestly(
        self,
    ) -> None:
        """Control: an importer with no ``cap`` of its own, both directions.

        The name is then absent from the importer's registry entirely, so the
        precondition did not translate at all and the obligation was a loud
        Tier-3 demotion (E532) — including for the call that violates it.  Both
        calls now get a static verdict, and each matches its runtime.
        """
        modules = [_resolved(("caplib",), _CAP_LIB)]
        template = """\
import caplib(guarded);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  guarded(%d)
}
"""
        satisfied = template % 50
        ok = _verify_mod(satisfied, modules)
        assert not _codes(ok), _codes(ok)
        assert not [
            d for d in ok.diagnostics if d.error_code == "E532"
        ], "the callee's precondition still is not translated"
        assert _run_mod(satisfied, modules) == 50

        violated = template % 500
        bad = _verify_mod(violated, modules)
        assert "E501" in _codes(bad), _codes(bad)
        with pytest.raises(WasmTrapError):
            _run_mod(violated, modules)


# The ENSURES path: `bounded`'s postcondition is written in terms of the same
# private `cap`, and the importer relies on it to prove its own.
_ENS_LIB = """\
module enslib;

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 1000)
  effects(pure)
{
  1000
}

public fn bounded(@Int -> @Int)
  requires(true)
  ensures(@Int.result < cap(0))
  effects(pure)
{
  700
}
"""

_ENS_MAIN = """\
import enslib(bounded);

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  5
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 5)
  effects(pure)
{
  bounded(0) + cap(0) - cap(0)
}
"""


class TestCalleeEnsuresIsReadInItsModuleToo:
    """The postcondition ASSUMED at a call site is the callee's own (#1225).

    Not a refined-return special case: the plain ``ensures`` path carries the
    same defect, and it fails the other way round — a postcondition read too
    STRONGLY proves the caller's own contract, so the caller is what traps.
    """

    def test_the_assumed_postcondition_cannot_prove_a_false_caller_contract(
        self,
    ) -> None:
        modules = [_resolved(("enslib",), _ENS_LIB)]
        result = _verify_mod(_ENS_MAIN, modules)
        assert "E500" in _codes(result), (
            "main's `ensures(@Int.result < 5)` was proved from the IMPORTER's "
            f"`cap`, which the callee's contract never names: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(_ENS_MAIN, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind


# Both dimensions of the scope in ONE contract: `both`'s precondition names an
# alias-typed parameter AND calls a private helper.  `Cnt` is `Bool` here, so
# the two parameters are two stacks and `@Array<Int>.0` is the FIRST.
_BOTH_LIB = """\
module bothlib;

type Cnt = Bool;

private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 3)
  effects(pure)
{
  3
}

public fn both(@Array<Int>, @Array<Cnt> -> @Nat)
  requires(array_length(@Array<Int>.0) < cap(0))
  ensures(@Nat.result >= 0)
  effects(pure)
{
  0
}
"""

_BOTH_ALIAS_CONFLICT = "type Cnt = Int;\n\n"

_BOTH_CAP_CONFLICT = """\
private fn cap(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 100)
  effects(pure)
{
  100
}

"""

# The call is made from a function whose OWN parameters are the arrays, with
# their lengths as its precondition: an array LITERAL argument does not
# translate, so a call site spelled `both([...], [...])` demotes to Tier 3
# before either half of the scope is consulted and would measure nothing.
_BOTH_MAIN = """\
import bothlib(both);

""" + _BOTH_ALIAS_CONFLICT + _BOTH_CAP_CONFLICT + """\
private fn go(@Array<Int>, @Array<Bool> -> @Nat)
  requires(array_length(@Array<Int>.0) == 5 && array_length(@Array<Bool>.0) == 2)
  ensures(true)
  effects(pure)
{
  both(@Array<Int>.0, @Array<Bool>.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  go(array_range(0, 5), [true, false])
}
"""


class TestBothHalvesOfTheScopeRideTogether:
    """The naming env and the function registry are ONE swap (#1208, #1225).

    ``both``'s precondition is ``array_length(@Array<Int>.0) < cap(0)``, and
    each half of the scope decides one side of that comparison:

    * the naming env decides WHICH argument ``@Array<Int>.0`` is — the
      length-5 ``Array<Int>`` in ``bothlib`` (``Cnt = Bool``, two stacks), the
      length-2 ``Array<Bool>`` under the importer's ``type Cnt = Int`` (one
      merged stack, so ``.0`` is the most recent);
    * the function registry decides what ``cap(0)`` is — 3 in ``bothlib``, 100
      in the importer.

    Only ``5 < 3`` is false.  Each of the other three combinations — either
    half read in the importer, or both — proves the precondition and returns a
    verify-clean verdict on a program that traps, so this one program's E501
    can only be produced by swapping both halves together.  The two isolating
    controls below then show each half is separately load-bearing, so the pair
    test cannot be passing on one of them alone.
    """

    def test_the_violation_needs_both_halves(self) -> None:
        modules = [_resolved(("bothlib",), _BOTH_LIB)]
        result = _verify_mod(_BOTH_MAIN, modules)
        assert "E501" in _codes(result), (
            "at least one half of the callee's scope was read in the "
            f"importer: {_codes(result)}"
        )
        with pytest.raises(WasmTrapError) as exc:
            _run_mod(_BOTH_MAIN, modules)
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_registry_half_alone_decides_a_verdict(self) -> None:
        """Drop the alias conflict: only ``cap`` still differs.

        ``@Array<Int>.0`` is the length-5 array under either env now, so the
        verdict turns purely on which ``cap`` the contract's call resolves to
        — 5 < 3 (violated) against 5 < 100 (clean).
        """
        source = _BOTH_MAIN.replace(_BOTH_ALIAS_CONFLICT, "")
        assert "type Cnt" not in source
        modules = [_resolved(("bothlib",), _BOTH_LIB)]
        result = _verify_mod(source, modules)
        assert "E501" in _codes(result), _codes(result)
        with pytest.raises(WasmTrapError):
            _run_mod(source, modules)

    def test_the_naming_half_alone_decides_a_verdict(self) -> None:
        """Drop the ``cap`` conflict: only the alias still differs.

        ``cap(0)`` is 3 either way now (the importer has no ``cap`` at all), so
        the verdict turns purely on which argument ``@Array<Int>.0`` names —
        5 < 3 (violated) against 2 < 3 (clean).
        """
        source = _BOTH_MAIN.replace(_BOTH_CAP_CONFLICT, "")
        assert "ensures(@Int.result == 100)" not in source
        modules = [_resolved(("bothlib",), _BOTH_LIB)]
        result = _verify_mod(source, modules)
        assert "E501" in _codes(result), _codes(result)
        with pytest.raises(WasmTrapError):
            _run_mod(source, modules)


# =====================================================================
# #1226 — the refined-return binder is the key its predicate looks up
# =====================================================================

# `Box` is a PARAMETERISED alias, so the binder renders `Box<Nat>` while its
# head identifier is `Box`.  The base resolves to `Nat`, which is a base the
# SMT layer models, so nothing but the binder key decides whether the return
# fact survives.
_PARAM_BINDER = """\
type Cnt = Nat;

type Box<T> = Nat;

type Grown = { @Box<Cnt> | @Box<Cnt>.0 >= 18 };

private fn mk(@Nat -> @Grown)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

private fn need18(@Nat -> @Nat)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  need18(mk(20))
}
"""


class TestParameterisedRefinedReturnBinder:
    """A refined return over a parameterised base keeps its fact (#1226).

    ``mk``'s result is a fresh variable constrained ONLY by the refinement
    predicate — its `ensures` is `true` and the literal `20` tells the caller
    nothing about it — so `need18(mk(20))` is provable exactly when the
    refined-return fact survives.  It did not: the value was pushed under the
    predicate's head identifier ``Box`` while ``@Box<Cnt>.0`` resolves
    ``Box<Nat>``, the predicate failed to translate, and the fact was dropped
    in silence.
    """

    def test_the_valid_program_is_accepted(self) -> None:
        result = _verify_mod(_PARAM_BINDER, [])
        assert not _codes(result), (
            "the refined-return fact was dropped and a valid program "
            f"rejected: {_codes(result)}"
        )

    def test_the_program_really_does_run(self) -> None:
        """The oracle: `vera run` returns 20, so the E501 was spurious."""
        assert _run_mod(_PARAM_BINDER, []) == 20

    def test_the_producer_discharges_at_tier_1(self) -> None:
        """The other side of the same key: ``mk``'s own return obligation.

        The producing function must PROVE its refined return, and that proof
        pushes the value under the same binder.  Missing, the predicate fell
        outside the fragment and the obligation demoted to a Tier-3 runtime
        guard (E506) — conservative rather than unsound, but a provable
        refinement that no longer proves.
        """
        result = _verify_mod(_PARAM_BINDER, [])
        assert not [
            d for d in result.diagnostics if d.error_code == "E506"
        ], [d.description[:90] for d in result.diagnostics]
        assert result.summary.tier3_runtime == 0, result.summary

    def test_the_bare_base_control_is_unchanged(self) -> None:
        """The same program with an UNPARAMETERISED binder, which always
        worked: head and key coincide when there are no type arguments."""
        control = _PARAM_BINDER.replace(
            "type Box<T> = Nat;\n\n", "",
        ).replace("@Box<Cnt>", "@Cnt")
        assert "Box" not in control
        result = _verify_mod(control, [])
        assert not _codes(result), _codes(result)
        assert result.summary.tier3_runtime == 0, result.summary


# The cross-module twin: `Cnt` is `Nat` in the module and `Int` in the
# importer, so the binder key differs BETWEEN the two namespaces —
# `Box<Nat>` against `Box<Int>`.
_BINDER_LIB = """\
module boxlib;

type Cnt = Nat;

type Box<T> = Nat;

public fn mk(@Nat -> @{ @Box<Cnt> | @Box<Cnt>.0 >= 18 })
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""

_BINDER_MAIN = """\
import boxlib(mk);

type Cnt = Int;

private fn need18(@Nat -> @Nat)
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  need18(mk(20))
}
"""


class TestRefinedReturnBinderIsKeyedInTheCalleeScope:
    """The binder is derived INSIDE the callee's scope (#1208, #1226).

    Now that the key renders its type arguments, it is env-dependent: the same
    predicate binds ``Box<Nat>`` in ``boxlib`` and ``Box<Int>`` under the
    importer's ``type Cnt = Int``.  The reference side has been translated in
    the callee's namespace since #1208, so a binder derived OUTSIDE that scope
    mints one key and looks up another — the exact miss this file's
    single-module case is about, arriving through provenance instead of
    through the head identifier.

    Moving the derivation out of the scope leaves the single-module case above
    green and turns this one red, which is what makes the wrap load-bearing
    rather than defensive: ``TestRefinedReturnTranslatesInTheCalleeNamespace``
    in the #1208 provenance suite recorded exactly that prediction while the
    bare-headed binder still masked it.
    """

    def test_the_imported_refined_return_fact_survives(self) -> None:
        modules = [_resolved(("boxlib",), _BINDER_LIB)]
        result = _verify_mod(_BINDER_MAIN, modules)
        assert not _codes(result), (
            "the callee's refined-return binder was keyed in the IMPORTER's "
            f"namespace: {_codes(result)}"
        )
        assert _run_mod(_BINDER_MAIN, modules) == 20

    def test_the_control_without_a_conflicting_alias_is_clean_too(
        self,
    ) -> None:
        """Control: the same import with the shadowing alias removed.

        The two envs then agree, so this case turns on the KEY alone and not
        on which env rendered it — it separates the two axes, and it is the
        case a fix that simply stopped assuming imported refined returns would
        also break.
        """
        control = _BINDER_MAIN.replace("type Cnt = Int;\n\n", "")
        assert "type Cnt" not in control
        result = _verify_mod(control, [_resolved(("boxlib",), _BINDER_LIB)])
        assert not _codes(result), _codes(result)
