"""#1210: State/Exn host-import registration must cover the whole handler.

Codegen registers a `State<T>` host-cell import quadruple and an `Exn<E>`
WASM tag by walking each function for `handle` expressions.  The walk
descended a `HandleExpr`'s BODY only — not its clause bodies, not a clause's
`with` state-update expression, and not the handler's own state-init
expression.  A family reached only through one of those went unregistered
while the lowering happily emitted its calls, so a check-green, verify-clean
program died at whole-module WAT compilation with `unknown func
$vera.state_push_Nat` / `unknown tag $exn_Int`.

The same walk also skipped an `i32_pair` cell type in silence, where the
declared-effect path rejects it loudly (`E607`): `handle[State<String>]`
inside a `pure` function registered nothing and emitted the calls anyway.

Two kinds of test here.  The shape tests pin each gap on a program whose
value is derived from the language rules, so a fix that registers the
family but lowers it wrongly still fails.  The differential is the
cross-component invariant itself — for every corpus program that compiles,
every `state_*` / `exn_*` symbol the emitted WAT REFERENCES has a matching
import or tag DECLARATION — which is the shape of check this bug class
needs: a green unit suite cannot see a desync between the registration pass
and the lowering pass, only running both and comparing can.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from tests.codegen_helpers import _compile, _run
from tests.checker_helpers import _check_ok
from tests.verifier_helpers import _verify_ok
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
    """The cross-component invariant: registration ⊇ lowering.

    Codegen decides which host-cell imports and exception tags a module
    declares in one pass (`_scan_body_for_state_handlers` /
    `_check_state_type`) and which ones it CALLS in another (the handler
    lowering).  A unit test on either pass cannot see them drift apart; only
    running both over real programs and comparing the two symbol sets can,
    which is exactly what #1210 was — a family emitted but never declared.

    Swept over every `examples/` and `tests/conformance/` program that
    compiles.  Programs that do not compile are counted, not asserted on:
    the conformance suite's negatives are supposed to fail.
    """
    programs = _corpus_programs()
    assert programs, "corpus is empty — the sweep would pass vacuously"

    swept = 0
    symbols_checked = 0
    failures: list[str] = []
    for path in programs:
        source = path.read_text(encoding="utf-8")
        try:
            program = transform(parse_file(str(path)))
            result = codegen_compile(program, source=source, file=str(path))
        except Exception:  # noqa: BLE001 — a parse/transform failure is not this test's subject
            continue
        wat = result.wat
        if not wat:
            continue
        swept += 1
        declared = set(_STATE_DECL.findall(wat)) | set(_EXN_DECL.findall(wat))
        referenced = set(_STATE_REF.findall(wat)) | set(_EXN_REF.findall(wat))
        symbols_checked += len(referenced)
        missing = referenced - declared
        if missing:
            failures.append(f"{path.name}: {sorted(missing)}")

    assert not failures, (
        "emitted WAT references State/Exn symbols the module never "
        "declares:\n" + "\n".join(failures)
    )
    # Floors, so corpus decay or a silent emptying of the regexes cannot
    # turn this into a vacuous pass.
    assert swept >= 150, f"only {swept} programs compiled — sweep too small"
    assert symbols_checked >= 50, (
        f"only {symbols_checked} state/exn symbol references found — the "
        "extraction regexes are probably no longer matching the emitted WAT"
    )


def test_the_differential_can_go_red() -> None:
    """Prove the extraction actually distinguishes declared from referenced.

    Without this, a regex that silently stopped matching would leave the
    sweep above green forever.  A handler program's WAT with its import
    lines stripped must be reported as missing exactly those symbols.
    """
    result = _compile(_HANDLE_IN_STATE_INIT + _MAIN)
    wat = result.wat
    assert wat, "fixture produced no WAT"
    referenced = set(_STATE_REF.findall(wat))
    assert referenced, "fixture references no state symbols"
    assert referenced <= set(_STATE_DECL.findall(wat)), (
        "fixture is itself unbalanced"
    )
    stripped = "\n".join(
        line for line in wat.splitlines()
        if not line.lstrip().startswith('(import "vera" "state_')
    )
    assert set(_STATE_REF.findall(stripped)) - set(_STATE_DECL.findall(stripped)) == referenced
