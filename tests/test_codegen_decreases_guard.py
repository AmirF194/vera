"""Tests for vera.codegen — the runtime `decreases` termination guard (#1172).

`E525` (a Tier-3 `decreases` obligation) promises the termination metric
"will be checked at runtime".  These tests pin that promise: a measure
that fails to decrease (or leaves the well-founded floor) traps through
the contract-violation channel instead of hanging, while terminating
programs — Tier-1-proved and Tier-3-guarded alike — run to completion
with the guard emitted but silent.

Guard semantics (the runtime mirror of `_verify_decreases`,
vera/verifier.py): on each re-entry of a guarded function, the measure
must be strictly less than the previous activation's and non-negative —
scalars by value, ADT measures by structural size, lexicographic tuples
componentwise.  Tail recursion keeps TCO for the self-recursive case:
a self-recursive `return_call` is prefixed with a call-site check —
arguments captured, the measure evaluated over them against the live
chain globals, the activation's guard state closed out before the
transfer — so guarded iteration runs at constant stack depth (#517's
1M-depth tests pin this) while every hop stays checked.  Only a
mutual-tail call between two guarded functions falls back to a plain
call, where the entry check covers the hop.

The non-terminating fixtures run through the CLI in a subprocess with a
timeout: pre-fix they hang (the test fails on `TimeoutExpired` — the RED
shape), post-fix they trap promptly.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest
import wasmtime

from vera.codegen import CompileResult, compile, execute
from vera.parser import parse_file
from vera.transform import transform


# =====================================================================
# Helpers
# =====================================================================


def _compile(source: str) -> CompileResult:
    """Compile a Vera source string to WASM."""
    import tempfile

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    ) as f:
        f.write(source)
        f.flush()
        path = f.name

    tree = parse_file(path)
    prog = transform(tree)
    return compile(prog, source=source, file=path)


def _compile_ok(source: str) -> CompileResult:
    result = _compile(source)
    errors = [d for d in result.diagnostics if d.severity == "error"]
    assert not errors, f"Unexpected errors: {[e.description for e in errors]}"
    return result


def _run(source: str, fn: str | None = None, args: list[int] | None = None) -> int:
    result = _compile_ok(source)
    exec_result = execute(result, fn_name=fn, args=args)
    assert exec_result.value is not None, "Expected a return value"
    return exec_result.value


def _run_trap_message(
    source: str, fn: str | None = None, args: list[int] | None = None,
) -> str:
    """Compile, execute, assert a trap, and return its message text."""
    result = _compile_ok(source)
    with pytest.raises((wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError)) as exc:
        execute(result, fn_name=fn, args=args)
    return str(exc.value)


def _run_cli(tmp_path: Path, source: str, timeout: int = 30):
    """Run a program via the CLI in a subprocess (for non-terminating shapes).

    Pre-fix the non-terminating fixtures spin forever — `TimeoutExpired`
    propagates and fails the test, which is the documented RED reason.
    Post-fix the guard traps promptly and the process exits on its own.
    """
    src = tmp_path / "prog.vera"
    src.write_text(source, encoding="utf-8")
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", "run", src.as_posix()],
        capture_output=True,
        text=True,
        encoding="utf-8",
        timeout=timeout,
        check=False,
    )


def _assert_termination_trap(proc) -> None:
    """The CLI run ended in the termination-guard trap, not a hang/crash."""
    combined = (proc.stdout + proc.stderr).lower()
    assert proc.returncode != 0, (
        f"expected a failing exit, got {proc.returncode}:\n{combined}"
    )
    assert "decrease" in combined, (
        f"expected the termination-measure message, got:\n{combined}"
    )


# =====================================================================
# Non-terminating programs trap instead of hanging
# =====================================================================


# The #1172 repro: an ADT measure on a program that permutes its
# arguments forever.  `check` passes, `verify` records the decreases
# obligation as tier3 (E525), and pre-fix `run` never returned.
SPIN_ADT = """\
private data List {
  Nil,
  Cons(Int, List)
}

private fn spin(@List, @List -> @List)
  requires(true)
  ensures(true)
  decreases(@List.1)
  effects(pure)
{
  spin(@List.1, @List.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @List = spin(Cons(1, Nil), Nil);
  match @List.0 {
    Nil -> 0,
    Cons(@Int, @List) -> @Int.0
  }
}
"""


class TestNonTerminatingTraps:
    def test_adt_measure_spin_traps(self, tmp_path: Path) -> None:
        """The issue's repro: a structurally non-decreasing ADT measure.

        The recursive call passes its arguments straight through, so no
        measure decreases under any reading.  The guard compares
        structural size ranks and traps on the first re-entry whose rank
        fails ``rank_new < rank_old && rank_new >= 0``."""
        _assert_termination_trap(_run_cli(tmp_path, SPIN_ADT))

    def test_constant_int_measure_tail_call_traps(self, tmp_path: Path) -> None:
        """A constant measure on a TAIL-recursive call.

        Tail position lowers to ``return_call`` (TCO, #517/#549), which
        the guard KEEPS for self-recursion — the prepended call-site
        check captures the arguments, evaluates the measure over them,
        and traps against the live chain state before the frame is
        elided."""
        _assert_termination_trap(_run_cli(tmp_path, """\
private fn loopy(@Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  loopy(@Int.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  loopy(7)
}
"""))

    def test_growing_measure_traps(self, tmp_path: Path) -> None:
        """A measure that grows violates strict decrease immediately."""
        _assert_termination_trap(_run_cli(tmp_path, """\
private fn upward(@Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  upward(@Int.0 + 1)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  upward(1)
}
"""))

    def test_negative_measure_floor_traps(self, tmp_path: Path) -> None:
        """Strictly decreasing forever is not well-founded: the ``>= 0``
        floor leg traps once the measure goes negative, even though every
        step satisfies ``new < old``."""
        _assert_termination_trap(_run_cli(tmp_path, """\
private fn downward(@Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  downward(@Int.0 - 1)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  downward(3)
}
"""))

    def test_lexicographic_violation_traps(self, tmp_path: Path) -> None:
        """A two-component measure violated lexicographically: the first
        component holds while the second grows."""
        _assert_termination_trap(_run_cli(tmp_path, """\
private fn lexy(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.1, @Int.0)
  effects(pure)
{
  lexy(@Int.1, @Int.0 + 1)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  lexy(5, 5)
}
"""))

    def test_mutual_recursion_where_traps(self, tmp_path: Path) -> None:
        """Spec §5.6.2 mutual recursion via a `where` block: each member
        carries its own clause; a chain that never shrinks traps on a
        re-entry of a guarded member."""
        _assert_termination_trap(_run_cli(tmp_path, """\
public fn ping(@Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  pong(@Int.0)
}
where {
  fn pong(@Int -> @Int)
    requires(true)
    ensures(true)
    decreases(@Int.0)
    effects(pure)
  {
    ping(@Int.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  ping(9)
}
"""))


# =====================================================================
# Terminating programs stay clean (guard present, silent)
# =====================================================================


class TestTerminatingStaysClean:
    def test_tier1_proved_countdown_runs_and_carries_guard(self) -> None:
        """A provable Nat countdown still runs — and the guard is emitted
        anyway (contracts compile unconditionally; emission must not
        depend on whether the verifier ran)."""
        source = """\
private fn total(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    @Nat.0 + total(@Nat.0 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(total(4))
}
"""
        assert _run(source, fn="main") == 10
        result = _compile_ok(source)
        assert "$dec_active_total" in result.wat, (
            "the termination guard must be emitted for every decreases fn"
        )

    def test_lexicographic_ackermann_runs(self) -> None:
        """Spec §5.6.1's lexicographic example (argument order corrected).

        As previously printed the spec's recursive calls permuted
        Ackermann's arguments (``A(1, m-1)`` where the classical
        definition needs ``A(m-1, 1)``), producing an ``A(1,1) →
        A(2,0) → A(1,1)`` cycle — a non-terminating program whose
        Tier-3 measure was never checked.  This is the classical
        definition, which the lex measure ``(m, n)`` genuinely bounds;
        the spec text is fixed in lockstep."""
        source = """\
private fn ackermann(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.1, @Nat.0)
  effects(pure)
{
  if @Nat.1 == 0 then {
    @Nat.0 + 1
  } else {
    if @Nat.0 == 0 then {
      ackermann(@Nat.1 - 1, 1)
    } else {
      ackermann(@Nat.1 - 1, ackermann(@Nat.1, @Nat.0 - 1))
    }
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(ackermann(2, 2))
}
"""
        assert _run(source, fn="main") == 7
        result = _compile_ok(source)
        assert "$dec_active_ackermann" in result.wat

    def test_sequential_sibling_calls_state_restored(self) -> None:
        """Two sequential calls with a LARGER second measure must both
        succeed: the guard's chain state is per-activation (saved at
        entry, restored at every exit), so a finished call leaves no
        residue that would spuriously trap its sibling."""
        source = """\
private fn burn(@Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.0)
  effects(pure)
{
  if @Int.0 <= 0 then {
    0
  } else {
    1 + burn(@Int.0 - 1)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = burn(3);
  let @Int = burn(5);
  @Int.0 + @Int.1
}
"""
        assert _run(source, fn="main") == 8

    def test_adt_measure_terminating_runs(self) -> None:
        """A structurally shrinking ADT measure runs clean — the rank
        helper orders by structural size and every hop genuinely
        shrinks."""
        source = """\
private data List {
  Nil,
  Cons(Int, List)
}

private fn total(@List -> @Int)
  requires(true)
  ensures(true)
  decreases(@List.0)
  effects(pure)
{
  match @List.0 {
    Nil -> 0,
    Cons(@Int, @List) -> @Int.0 + total(@List.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  total(Cons(30, Cons(12, Nil)))
}
"""
        assert _run(source, fn="main") == 42


# =====================================================================
# Tier-3 obligation ⇒ emitted guard (the correspondence the E525
# wording promises)
# =====================================================================


class TestTier3GuardCorrespondence:
    def test_tier3_decreases_obligation_has_emitted_guard(self) -> None:
        """The differential the #1172 class demands: when the verifier
        records a `decreases` obligation as tier3 (E525 — "checked at
        runtime"), the emitted module must actually contain that
        function's guard.  A future Tier-3-capable diagnostic without an
        emission cannot ride in silently through this shape."""
        from vera.verifier import verify

        import tempfile

        source = SPIN_ADT
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8"
        ) as f:
            f.write(source)
            f.flush()
            path = f.name
        tree = parse_file(path)
        prog = transform(tree)
        vr = verify(prog, source=source, file=path)
        tier3_decreases = [
            ob for ob in vr.obligations
            if ob.kind == "decreases" and ob.status == "tier3"
        ]
        assert tier3_decreases, (
            "fixture must exercise a tier3 decreases obligation "
            f"(got obligations: {[(o.kind, o.status) for o in vr.obligations]})"
        )
        result = _compile_ok(source)
        assert "$dec_active_spin" in result.wat, (
            "tier3 decreases obligation with no emitted runtime guard — "
            "the E525 promise would be empty (#1172)"
        )


# =====================================================================
# E127 — non-well-founded measure types rejected at check time
# =====================================================================


class TestNonWellFoundedMeasureRejected:
    """#1172: spec §5.6.1(3) is normative — a measure without a
    well-founded ordering (Float64, String, Bool, a function type) was
    previously accepted silently, making the clause decorative: neither
    the prover nor any runtime guard can enforce an order that does not
    exist.  The checker now rejects it with E127."""

    @staticmethod
    def _errors(source: str):
        from tests.checker_helpers import _errors as checker_errors

        return checker_errors(source)

    def _assert_e127(self, measure: str, param: str) -> None:
        errs = self._errors(f"""\
private fn f(@{param} -> @Int)
  requires(true)
  ensures(true)
  decreases({measure})
  effects(pure)
{{
  42
}}
""")
        assert any(e.error_code == "E127" for e in errs), (
            f"expected E127 for measure {measure!r}, got: "
            f"{[(e.error_code, e.description) for e in errs]}"
        )

    def test_float_measure_rejected(self) -> None:
        self._assert_e127("@Float64.0", "Float64")

    def test_string_measure_rejected(self) -> None:
        self._assert_e127("@String.0", "String")

    def test_bool_measure_rejected(self) -> None:
        self._assert_e127("@Bool.0", "Bool")

    def test_second_lex_component_rejected_too(self) -> None:
        """Every component of a lexicographic tuple is validated."""
        errs = self._errors("""\
private fn f(@Int, @Float64 -> @Int)
  requires(true)
  ensures(true)
  decreases(@Int.0, @Float64.0)
  effects(pure)
{
  42
}
""")
        assert any(e.error_code == "E127" for e in errs)

    def test_int_nat_adt_and_derived_measures_accepted(self) -> None:
        """The well-founded family stays accepted: Nat, Int, a data
        type, and an Int-valued derived measure over a collection."""
        errs = self._errors("""\
private data List {
  Nil,
  Cons(Int, List)
}

private fn a(@Nat -> @Int)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{ 1 }

private fn b(@Int -> @Int)
  requires(true) ensures(true) decreases(@Int.0) effects(pure)
{ 1 }

private fn c(@List -> @Int)
  requires(true) ensures(true) decreases(@List.0) effects(pure)
{ 1 }

private fn d(@Array<Int> -> @Int)
  requires(true) ensures(true) decreases(array_length(@Array<Int>.0)) effects(pure)
{ 1 }
""")
        assert not errs, f"unexpected errors: {[e.description for e in errs]}"


class TestGenericAdtMeasure:
    def test_generic_adt_measure_runs_unguarded(self) -> None:
        """A GENERIC ADT measure (``List<Int>``) runs without a false trap
        — by NOT being guarded.

        Regression pin for the two wrong ways this failed first: the
        parameterized name missing the layout key froze the rank at 1
        (a false trap on every genuinely shrinking hop —
        ``ch02_adt_recursive``), and base-name stripping walked the
        GENERIC layout's offsets, which concrete construction does not
        use (an i64 payload pushes the tail), reading a payload as a
        pointer (a wild trap).  Ranking a parameterized measure needs
        per-instantiation helpers (the ``$eq_<type>`` pattern) — until
        then such a measure gets no guard, and the emitted module must
        contain none."""
        source = """\
private data List<T> {
  Nil,
  Cons(T, List<T>)
}

private fn length(@List<Int> -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@List<Int>.0)
  effects(pure)
{
  match @List<Int>.0 {
    Nil -> 0,
    Cons(@Int, @List<Int>) -> 1 + length(@List<Int>.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(length(Cons(1, Cons(2, Cons(3, Nil)))))
}
"""
        assert _run(source, fn="main") == 3
        result = _compile_ok(source)
        assert "$dec_active_length" not in result.wat, (
            "a parameterized ADT measure must not be guarded until "
            "per-instantiation rank helpers exist"
        )
