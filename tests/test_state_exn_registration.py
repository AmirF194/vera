"""#1210: State/Exn host-import registration must cover the whole handler.

Codegen registers a `State<T>` host-cell import quadruple and an `Exn<E>`
WASM tag by walking each function for `handle` expressions.  The walk
descended a `HandleExpr`'s BODY only — not its clause bodies, not a clause's
`with` state-update expression, and not the handler's own state-init
expression.  A family reached only through one of those went unregistered
while the lowering happily emitted its calls, so a check-green, verify-clean
program died at whole-module WAT compilation with `unknown func
$vera.state_push_Nat` / `unknown tag $exn_Int`.

It also stopped at the function BODY, so a handler in a lowered CONTRACT —
a `requires` / `ensures` predicate, an `assert`, or a `decreases` measure —
was never registered while its calls were emitted.

The same walk skipped an `i32_pair` cell type in silence, where the
declared-effect path rejects it loudly (`E607`): `handle[State<String>]`
inside a `pure` function registered nothing and emitted the calls anyway.
Its Exn twin discarded the registration verdict outright, so
`handle[Exn<Unit>]` in a `pure` function compiled to a `throw` against an
undeclared tag where the declared-row spelling was a clean `E612`.

Two kinds of test here.  The shape tests pin each gap on a program whose
value is derived from the language rules, so a fix that registers the
family but lowers it wrongly still fails.  The differential is the
cross-component invariant itself — for every corpus program that compiles,
every `state_*` / `exn_*` symbol the emitted WAT REFERENCES has a matching
import or tag DECLARATION, **and the module validates** — which is the shape
of check this bug class needs: a green unit suite cannot see a desync
between the registration pass and the lowering pass, only running both and
comparing can.  The validation leg exists because the name comparison alone
is blind to a symbol declared at the WRONG TYPE, which is invalid WASM the
set difference reports as perfectly balanced.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest
import wasmtime

from tests.codegen_helpers import _compile, _run
from tests.checker_helpers import _check_ok
from tests.verifier_helpers import _verify_ok
from vera.errors import VeraError
from vera.parser import parse_file
from vera.transform import transform
from vera.codegen import compile as codegen_compile

_MAIN = """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(())
}
"""

# --- a nested handler inside a CLAUSE BODY ---------------------------
# `State<Bool>` is reached only from the Nat handler's get clause, so the
# walk never saw it: `unknown func $vera.state_push_Bool`.
#   get(()) -> Nat clause captures 8, the nested Bool cell reads true,
#              resume(8); outer Int cell is untouched at 111
# => 8 + 111 = 119.
_HANDLE_IN_CLAUSE_BODY = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 111) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    let @Nat = handle[State<Nat>](@Nat = 8) {
      get(@Unit) -> {
        let @Bool = handle[State<Bool>](@Bool = true) {
          get(@Unit) -> { resume(@Bool.0) },
          put(@Bool) -> { resume(()) }
        } in {
          get(())
        };
        resume(if @Bool.0 then { @Nat.0 } else { 0 })
      },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    };
    nat_to_int(@Nat.0) + get(())
  }
}
"""

# --- a nested handler inside the STATE INIT expression ----------------
# `State<Nat>` is reached only from the outer handler's init expression.
#   nested: init 4, get clause doubles it -> 8; outer init = 8 + 1 = 9
# => 9.
_HANDLE_IN_STATE_INIT = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = nat_to_int(handle[State<Nat>](@Nat = 4) {
    get(@Unit) -> { resume(@Nat.0 + @Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  }) + 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

# --- a nested handler inside a clause's `with` state update -----------
# `State<Nat>` is reached only from the put clause's `with` expression.
#   put(10)  -> stores 10, then `with` overrides with 10 + 5 = 15
# => 15.
_HANDLE_IN_WITH_EXPR = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.1 + nat_to_int(handle[State<Nat>](@Nat = 5) {
      get(@Unit) -> { resume(@Nat.0) },
      put(@Nat) -> { resume(()) }
    } in {
      get(())
    })
  } in {
    put(10);
    get(())
  }
}
"""

# --- an Exn handler inside a clause body ------------------------------
# The `$exn_Int` TAG is reached only from the State get clause's body:
# `unknown tag $exn_Int`.
#   get(()) -> captures state 5; the nested Exn handler catches throw(2)
#              and returns 42; resume(42 + 5)
# => 47.
_EXN_IN_CLAUSE_BODY = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> {
      let @Int = handle[Exn<Int>] {
        throw(@Int) -> { @Int.0 + 40 }
      } in {
        throw(2);
        999
      };
      resume(@Int.0 + @Int.1)
    },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

_SHAPES = [
    ("handle_in_clause_body", _HANDLE_IN_CLAUSE_BODY, 119),
    ("handle_in_state_init", _HANDLE_IN_STATE_INIT, 9),
    ("handle_in_with_expr", _HANDLE_IN_WITH_EXPR, 15),
    ("exn_in_clause_body", _EXN_IN_CLAUSE_BODY, 47),
]

# --- the i32_pair cell the walk skipped in silence --------------------
# The handler discharges the effect, so the declared-effect E607 gate never
# runs on `probe` — the body walk is the only thing that sees this cell, and
# it refused to register it without saying so while the lowering emitted
# `state_push_String`.  Must be the same loud diagnostic the declared path
# gives, not invalid WASM.
_STATE_STRING_IN_PURE_FN = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<String>](@String = "hi") {
    get(@Unit) -> { resume(@String.0) },
    put(@String) -> { resume(()) }
  } in {
    string_length(get(()))
  }
}
"""


@pytest.mark.parametrize(
    ("source", "expected"),
    [pytest.param(s, e, id=i) for i, s, e in _SHAPES],
)
def test_handler_family_reached_only_off_the_body_is_registered(
    source: str, expected: int,
) -> None:
    """Each scan gap: check-green and verify-clean must mean compilable.

    Pre-fix every one of these died at whole-module WAT compilation with an
    unknown func / unknown tag, which is the loudest possible way to say the
    registration pass and the lowering pass disagreed.
    """
    program = source + _MAIN
    _check_ok(program)
    _verify_ok(program)
    assert _run(program) == expected


def test_uncompilable_cell_type_in_a_handled_body_is_loud() -> None:
    """An `i32_pair` State cell reached only from a body is E607, not silence.

    The declared-effect path already rejects `State<String>` with E607; the
    body walk must agree rather than skipping registration and leaving the
    lowering to emit calls to imports that were never declared.
    """
    result = _compile(_STATE_STRING_IN_PURE_FN + _MAIN)
    codes = {d.error_code for d in result.diagnostics}
    assert "E607" in codes, (
        "expected the E607 unsupported-State-cell diagnostic, got: "
        f"{[(d.error_code, d.description[:80]) for d in result.diagnostics]}"
    )
    # And specifically NOT the symptom it used to produce.
    joined = " ".join(d.description for d in result.diagnostics)
    assert "state_push_String" not in joined, joined


# --- the Exn twin of the i32_pair cell --------------------------------
# `Exn<Unit>` has no WAT payload type, so the tag cannot be declared.  The
# DECLARED-row spelling has always been a clean E612 function drop; the
# handler-walk spelling registered nothing, DISCARDED the verdict, and let
# the function compile — `unknown tag $exn_Unit` at whole-module WAT.  The
# two paths must reach the same verdict on the same payload type.
_EXN_UNIT_IN_PURE_FN = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Unit>] {
    throw(@Unit) -> { 0 - 1 }
  } in {
    throw(());
    5
  }
}
"""

# Its declared-row twin: the same payload type reached by the gate instead.
_EXN_UNIT_DECLARED_ROW = """
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Unit>>)
{
  throw(());
  5
}
"""


@pytest.mark.parametrize(
    "source",
    [
        pytest.param(_EXN_UNIT_IN_PURE_FN, id="handler_walk"),
        pytest.param(_EXN_UNIT_DECLARED_ROW, id="declared_row"),
    ],
)
def test_uncompilable_exn_payload_is_the_same_verdict_either_way(
    source: str,
) -> None:
    """An unregistrable `Exn<E>` is E612 whichever path reaches it.

    The handler walk used to call the shared registration helper and throw
    the boolean away, so only the State arm could drop a function — the Exn
    arm registered nothing and compiled the calls anyway.
    """
    result = _compile(source + _MAIN)
    codes = {d.error_code for d in result.diagnostics}
    assert "E612" in codes, (
        "expected the E612 unsupported-Exn-payload diagnostic, got: "
        f"{[(d.error_code, d.description[:80]) for d in result.diagnostics]}"
    )
    # The tag is never declared, so it must never be referenced either.
    assert "$exn_Unit" not in (result.wat or "")


# --- handlers in CONTRACT predicates ----------------------------------
# A contract is lowered code: `requires`/`ensures` become runtime checks and
# `decreases` becomes the termination guard's measure.  A handler written in
# one is emitted like any other, but the registration walk saw `decl.body`
# alone, so the module called `$vera.state_push_Nat` against no import.
_HANDLER_IN_REQUIRES = """
private fn probe(@Int -> @Int)
  requires(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  } > 0)
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
  probe(5)
}
"""

_HANDLER_IN_ENSURES = """
private fn probe(@Int -> @Int)
  requires(true)
  ensures(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  } > 0)
  effects(pure)
{
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(5)
}
"""

# `assert` sits in the BODY, but the walker's case split declared a contract
# predicate structurally handler-free ("no handle in pred") and refused to
# descend — so this one was missed by the body walk itself.
_HANDLER_IN_ASSERT = """
private fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assert(handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  } > 0);
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  probe(5)
}
"""

# `decreases` carries `exprs`, not `expr` — the attribute-name shortcut the
# IO scan used skipped it entirely, so it needs its own case.
_HANDLER_IN_DECREASES = """
private fn countdown(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0 + handle[State<Nat>](@Nat = 0) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    get(())
  })
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    countdown(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(countdown(3))
}
"""

_CONTRACT_SHAPES = [
    ("requires", _HANDLER_IN_REQUIRES, 5),
    ("ensures", _HANDLER_IN_ENSURES, 5),
    ("assert", _HANDLER_IN_ASSERT, 5),
    ("decreases", _HANDLER_IN_DECREASES, 0),
]


@pytest.mark.parametrize(
    ("source", "expected"),
    [pytest.param(s, e, id=i) for i, s, e in _CONTRACT_SHAPES],
)
def test_handler_in_a_contract_predicate_is_registered(
    source: str, expected: int,
) -> None:
    """A handler in a contract predicate is lowered, so it must be declared.

    All four were check-green and verify-clean and died at whole-module WAT
    compilation with `unknown func $vera.state_push_Nat`.
    """
    _check_ok(source)
    _verify_ok(source)
    assert _run(source) == expected


# =====================================================================
# Registration-completeness differential
# =====================================================================

_CORPUS_DIRS = ("examples", "tests/conformance")

# `call $vera.state_get_Int`, `call $vera.state_push_Option$LT$Int$GT$`, …
_STATE_REF = re.compile(r"call\s+(\$vera\.state_(?:get|put|push|pop)_[^\s)]+)")
# `(import "vera" "state_push_Int" (func $vera.state_push_Int))` — the
# zero-argument push/pop imports close immediately after the name, so the
# terminator is whitespace OR the closing paren.
_STATE_DECL = re.compile(
    r"\(import\s+\"vera\"\s+\"state_[^\"]+\"\s+\(func\s+"
    r"(\$vera\.state_[^\s)]+)")
# `catch $exn_Int $hc_0` / `throw $exn_Int`
_EXN_REF = re.compile(r"(?:catch|throw)\s+(\$exn_[^\s)]+)")
# `(tag $exn_Int (param i64))`
_EXN_DECL = re.compile(r"\(tag\s+(\$exn_[^\s)]+)")


def _corpus_programs() -> list[Path]:
    root = Path(__file__).parent.parent
    files: list[Path] = []
    for d in _CORPUS_DIRS:
        files.extend(sorted((root / d).glob("*.vera")))
    return files


def test_every_referenced_state_exn_symbol_is_declared() -> None:
    """The cross-component invariant: registration ⊇ lowering, and TYPED.

    Codegen decides which host-cell imports and exception tags a module
    declares in one pass (`_scan_body_for_state_handlers` /
    `_check_state_type`) and which ones it CALLS in another (the handler
    lowering).  A unit test on either pass cannot see them drift apart; only
    running both over real programs and comparing can, which is exactly what
    #1210 was — a family emitted but never declared.

    Two legs, because the name comparison alone is not the invariant.  The
    symbol-set leg catches an UNDECLARED symbol.  The validation leg —
    handing each swept module to `wasmtime.Module`, which type-checks the
    whole thing — catches a symbol declared at the WRONG TYPE, which the
    name comparison reports as perfectly balanced: the #1231 shape declared
    `state_get_Bool` (i32) for a call the checker had typed `Int` (i64), and
    a Byte-literal-into-an-`Int`-cell shape declared the right names with
    mismatched value types.  Both passed a name-only differential while
    being invalid WASM.

    Anchored, not exploratory: this sweeps `examples/` and
    `tests/conformance/`, so it holds the invariant over the programs the
    suite deliberately PLANTS there (including this PR's three
    `ch07_*` handler programs).  It is a regression guard on a corpus we
    curate, not an independent search for new violations.  Programs that do
    not compile are counted, not asserted on: the conformance suite's
    negatives are supposed to fail.
    """
    programs = _corpus_programs()
    assert programs, "corpus is empty — the sweep would pass vacuously"

    engine = wasmtime.Engine()
    swept = 0
    validated = 0
    symbol_refs = 0
    distinct_symbols: set[str] = set()
    failures: list[str] = []
    invalid: list[str] = []
    for path in programs:
        source = path.read_text(encoding="utf-8")
        # DECLARED failures only.  `parse_file` raises `ParseError` and
        # `transform` raises `TransformError` — both `VeraError` — for the
        # conformance suite's deliberate negatives, and those are not this
        # test's subject.  Anything else (a `TypeError`, an `AttributeError`,
        # a `RecursionError` out of codegen) is a real fault and PROPAGATES:
        # a broad `except Exception` here would silently drop the program
        # from the sweep and shrink the differential's coverage in exactly
        # the situation that most deserves a failure.
        try:
            program = transform(parse_file(str(path)))
        except VeraError:
            continue
        result = codegen_compile(program, source=source, file=str(path))
        wat = result.wat
        if not wat:
            continue
        swept += 1
        declared = set(_STATE_DECL.findall(wat)) | set(_EXN_DECL.findall(wat))
        referenced = set(_STATE_REF.findall(wat)) | set(_EXN_REF.findall(wat))
        symbol_refs += len(referenced)
        distinct_symbols |= referenced
        missing = referenced - declared
        if missing:
            failures.append(f"{path.name}: {sorted(missing)}")
        if not referenced:
            continue
        validated += 1
        try:
            wasmtime.Module(engine, wat)
        except Exception as exc:  # noqa: BLE001 — any validation failure is the finding
            invalid.append(f"{path.name}: {exc}")

    assert not failures, (
        "emitted WAT references State/Exn symbols the module never "
        "declares:\n" + "\n".join(failures)
    )
    assert not invalid, (
        "emitted WAT declares its State/Exn symbols but does not "
        "validate — a declared-at-the-wrong-type import the name "
        "comparison cannot see:\n" + "\n".join(invalid)
    )
    # Floors, so corpus decay or a silent emptying of the regexes cannot
    # turn this into a vacuous pass.  `symbol_refs` SUMS the per-program
    # reference counts (a program using one family in three functions
    # contributes once per distinct symbol, per program); the number of
    # globally distinct symbols across the corpus is much smaller, and both
    # are floored so neither reading can be quietly gamed.
    assert swept >= 150, f"only {swept} programs compiled — sweep too small"
    assert symbol_refs >= 50, (
        f"only {symbol_refs} state/exn symbol references summed across "
        "programs — the extraction regexes are probably no longer matching "
        "the emitted WAT"
    )
    assert len(distinct_symbols) >= 15, (
        f"only {len(distinct_symbols)} globally distinct state/exn symbols "
        "— the corpus has stopped covering the families"
    )
    assert validated >= 20, (
        f"only {validated} handler-bearing modules validated — the "
        "wrong-type leg is nearly vacuous"
    )


@pytest.mark.parametrize(
    ("source", "ref_re", "decl_re", "strip_prefix"),
    [
        pytest.param(
            _HANDLE_IN_STATE_INIT, _STATE_REF, _STATE_DECL,
            '(import "vera" "state_', id="state",
        ),
        pytest.param(
            _EXN_IN_CLAUSE_BODY, _EXN_REF, _EXN_DECL, "(tag $exn_", id="exn",
        ),
    ],
)
def test_the_differential_can_go_red(
    source: str, ref_re: re.Pattern[str], decl_re: re.Pattern[str],
    strip_prefix: str,
) -> None:
    """Prove the extraction actually distinguishes declared from referenced.

    Without this, a regex that silently stopped matching would leave the
    sweep above green forever.  A handler program's WAT with its declaration
    lines stripped must be reported as missing exactly those symbols — run
    for BOTH halves, because the `state_*` imports and the `exn_*` tags are
    extracted by different regexes and either could rot alone.
    """
    result = _compile(source + _MAIN)
    wat = result.wat
    assert wat, "fixture produced no WAT"
    referenced = set(ref_re.findall(wat))
    assert referenced, "fixture references no symbols of this kind"
    assert referenced <= set(decl_re.findall(wat)), "fixture is unbalanced"
    stripped = "\n".join(
        line for line in wat.splitlines()
        if not line.lstrip().startswith(strip_prefix)
    )
    assert set(ref_re.findall(stripped)) - set(decl_re.findall(stripped)) == referenced


def test_the_validation_leg_can_go_red() -> None:
    """Prove the `wasmtime.Module` leg catches a WRONG-TYPE declaration.

    The symbol-set comparison sees only names, so a module that declares
    every symbol it calls — but declares one of them with the wrong value
    type — is reported as balanced.  Retyping one `state_get_*` import from
    i64 to i32 in an otherwise-good module must fail the new leg while the
    name comparison stays green.
    """
    result = _compile(_HANDLE_IN_STATE_INIT + _MAIN)
    wat = result.wat
    assert wat, "fixture produced no WAT"
    engine = wasmtime.Engine()
    wasmtime.Module(engine, wat)  # the unmutated fixture validates

    mutated = wat.replace(
        '(import "vera" "state_get_Int" (func $vera.state_get_Int '
        '(result i64)))',
        '(import "vera" "state_get_Int" (func $vera.state_get_Int '
        '(result i32)))',
    )
    assert mutated != wat, (
        "the planted mutation did not apply — the import spelling changed"
    )
    # The NAME comparison still sees a perfectly balanced module …
    referenced = set(_STATE_REF.findall(mutated))
    declared = set(_STATE_DECL.findall(mutated))
    assert referenced and not (referenced - declared)
    # … while the module is not valid WASM.
    with pytest.raises(wasmtime.WasmtimeError):
        wasmtime.Module(engine, mutated)
