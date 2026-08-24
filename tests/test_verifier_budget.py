"""The configurable Z3 budget (#1350).

Before this knob the per-query budget was hardcoded at 10 s, which made the
TIER of a borderline obligation a property of the host rather than of the
program: `examples/ephemeris.vera`'s `julian_century` refine_bind proves in
roughly 9-11 s, so it discharged at Tier 1 on a cold fast run and fell to
Tier 3 on a slower or warmer one.  The corpus-wide pin in
`test_verifier_adt_decreases.py` measured 413 T1 cold and 412 T1 after a
single prior verification in the same process.

Two things are pinned here.  The resolution ORDER — explicit argument, then
`VERA_Z3_TIMEOUT_MS`, then the default — with malformed values raising rather
than silently reverting, because a budget that quietly falls back is
indistinguishable from the host-sensitivity the knob exists to remove.  And
the REGRESSION itself: at a generous budget the boundary obligation proves
whether the process is cold or warm.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from vera.checker.core import typecheck, typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.smt import (
    DEFAULT_Z3_TIMEOUT_MS,
    Z3_TIMEOUT_ENV,
    Z3BudgetError,
    resolve_timeout_ms,
)
from vera.verifier import ContractVerifier, verify

ROOT = Path(__file__).parent.parent
EXAMPLES = ROOT / "examples"
EPHEMERIS = EXAMPLES / "ephemeris.vera"

# Comfortably above the ~9-11 s the boundary obligation needs, so the
# measurement is of the program rather than of the machine.
GENEROUS_MS = 60_000


class TestBudgetResolution:
    """Explicit argument > environment > default."""

    def test_default_when_nothing_set(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.delenv(Z3_TIMEOUT_ENV, raising=False)
        assert resolve_timeout_ms() == DEFAULT_Z3_TIMEOUT_MS

    def test_environment_is_honoured(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "45000")
        assert resolve_timeout_ms() == 45_000

    def test_explicit_argument_beats_environment(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "45000")
        assert resolve_timeout_ms(7_000) == 7_000

    def test_blank_environment_falls_back(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """An empty value is "unset", not "malformed"."""
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "   ")
        assert resolve_timeout_ms() == DEFAULT_Z3_TIMEOUT_MS

    @pytest.mark.parametrize("bad", ["abc", "0", "-5", "1.5"])
    def test_malformed_environment_raises(
        self, monkeypatch: pytest.MonkeyPatch, bad: str
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, bad)
        with pytest.raises(Z3BudgetError, match=Z3_TIMEOUT_ENV):
            resolve_timeout_ms()

    @pytest.mark.parametrize("bad", [0, -1])
    def test_non_positive_explicit_raises(self, bad: int) -> None:
        with pytest.raises(Z3BudgetError):
            resolve_timeout_ms(bad)


class TestBudgetReachesTheVerifier:
    """The seams that construct a solver consult the same resolution."""

    def test_verifier_reads_the_environment(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "31000")
        assert ContractVerifier().timeout_ms == 31_000

    def test_explicit_argument_beats_environment_at_the_seam(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        monkeypatch.setenv(Z3_TIMEOUT_ENV, "31000")
        assert ContractVerifier(timeout_ms=9_000).timeout_ms == 9_000


class TestCliFlag:
    """`vera verify --timeout-ms` — the measurement surface."""

    def _run(self, args: list[str], env_extra: dict[str, str] | None = None):
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        env.pop(Z3_TIMEOUT_ENV, None)
        env.update(env_extra or {})
        return subprocess.run(
            [sys.executable, "-m", "vera.cli", *args],
            capture_output=True, text=True, encoding="utf-8",
            cwd=str(ROOT), env=env, timeout=180, check=False,
        )

    def test_json_reports_the_effective_budget(self) -> None:
        r = self._run(["verify", "--json", "--timeout-ms", "60000",
                       str(EXAMPLES / "factorial.vera")])
        assert r.returncode == 0, r.stderr
        assert json.loads(r.stdout)["verification"]["timeout_ms"] == 60_000

    def test_json_reports_the_default_when_unset(self) -> None:
        r = self._run(["verify", "--json", str(EXAMPLES / "factorial.vera")])
        assert r.returncode == 0, r.stderr
        got = json.loads(r.stdout)["verification"]["timeout_ms"]
        assert got == DEFAULT_Z3_TIMEOUT_MS

    def test_flag_beats_environment(self) -> None:
        r = self._run(["verify", "--json", "--timeout-ms", "12345",
                       str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "60000"})
        assert r.returncode == 0, r.stderr
        assert json.loads(r.stdout)["verification"]["timeout_ms"] == 12_345

    def test_environment_reaches_verify_without_a_flag(self) -> None:
        r = self._run(["verify", "--json", str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "60000"})
        assert r.returncode == 0, r.stderr
        assert json.loads(r.stdout)["verification"]["timeout_ms"] == 60_000

    @pytest.mark.parametrize("bad", ["abc", "0", "-5"])
    def test_malformed_flag_is_a_loud_error(self, bad: str) -> None:
        r = self._run(["verify", "--timeout-ms", bad,
                       str(EXAMPLES / "factorial.vera")])
        assert r.returncode == 1
        assert "--timeout-ms" in (r.stderr + r.stdout)

    def test_malformed_environment_is_a_loud_error(self) -> None:
        """Not a traceback out of the solver's construction seam."""
        r = self._run(["verify", str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "abc"})
        assert r.returncode == 1
        out = r.stderr + r.stdout
        assert Z3_TIMEOUT_ENV in out
        assert "Traceback" not in out

    def test_a_stray_environment_value_does_not_break_compile(self) -> None:
        """`compile` never builds a solver, so it must be unaffected."""
        r = self._run(["compile", "--wat", str(EXAMPLES / "factorial.vera")],
                      {Z3_TIMEOUT_ENV: "abc"})
        assert r.returncode == 0, r.stderr


def _verify_ephemeris(timeout_ms: int):
    text = EPHEMERIS.read_text(encoding="utf-8")
    prog = parse_to_ast(text)
    resolved = ModuleResolver(_root=EPHEMERIS.parent).resolve_imports(
        prog, EPHEMERIS
    )
    _diags, art = typecheck_with_artifacts(
        prog, text, file=str(EPHEMERIS), resolved_modules=resolved,
    )
    return verify(prog, text, file=str(EPHEMERIS), resolved_modules=resolved,
                  expr_types=art.expr_semantic_types,
                  expr_target_types=art.expr_target_types,
                  timeout_ms=timeout_ms)


class TestBoundaryObligationRegression:
    """The defect that motivated the knob, pinned at a generous budget.

    `julian_century`'s refine_bind is the obligation that straddled the
    default.  Warming the process is what tipped it before: a single prior
    verification was enough to move the corpus count by one.
    """

    def _julian_century_status(self, result) -> list[str]:
        return [
            o.status for o in result.obligations
            if o.fn_name == "julian_century" and o.kind == "refine_bind"
        ]

    def test_proves_cold_at_a_generous_budget(self) -> None:
        statuses = self._julian_century_status(_verify_ephemeris(GENEROUS_MS))
        assert statuses == ["verified"], statuses

    def test_proves_warm_at_a_generous_budget(self) -> None:
        """The warming step is the one that used to flip it."""
        list_ops = EXAMPLES / "list_ops.vera"
        text = list_ops.read_text(encoding="utf-8")
        prog = parse_to_ast(text)
        typecheck(prog, text)
        verify(prog, text, file=str(list_ops))

        statuses = self._julian_century_status(_verify_ephemeris(GENEROUS_MS))
        assert statuses == ["verified"], statuses

    def test_the_two_opaque_contracts_stay_tier_3_at_any_budget(self) -> None:
        """More time cannot help a claim behind `sqrt` / `asin`.

        This is the control: it separates "needed more time" from "the
        solver cannot see through the builtin at all", which is what the
        example's header claims about these two and not about the third.
        """
        result = _verify_ephemeris(GENEROUS_MS)
        opaque = {
            o.fn_name: o.status for o in result.obligations
            if o.fn_name in ("vec_norm", "declination") and o.kind == "ensures"
        }
        assert opaque == {"vec_norm": "tier3", "declination": "tier3"}, opaque
