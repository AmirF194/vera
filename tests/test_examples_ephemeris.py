"""Pins for `examples/ephemeris.vera` — the tree's only floating-point program.

`scripts/check_examples_run.py` registers this example as a bare `RunSpec()`, so
the gate asserts a trap-free exit and *some* output.  That is deliberately weak:
per the CHANGELOG, output pinning "stays in the dedicated tests that already do
it, so the gate does not go red on a cosmetic edit to an example", and `expect=`
sentinels are reserved for the three examples that reach outside the process.

But a bare `RunSpec()` leaves this particular example under-covered in the one
way that matters.  A float codegen regression could perturb `sin` in the last
bits, move the right ascension by an arcsecond, and the gate would stay green —
on the single example whose entire purpose is floating-point correctness.  So the
numbers are pinned here instead, following the `examples/effect_handler.vera`
pattern in `test_codegen_effects.py`.

Three jobs, deliberately separated:

  - `test_output_pinned` is the exact-string pin.  It fails on ANY drift,
    including bit-level float differences, and it is the tripwire.
  - `test_agrees_with_erfa` re-derives the angles from that output and checks
    them against an INDEPENDENT reference (ERFA's analytic model, via astropy).
    It is redundant while the pin holds, and that is the point: if someone
    legitimately changes the algorithm and updates the pinned string, this test
    independently establishes that the new string is still astronomically
    correct.  Do not delete it as duplicated coverage.
  - `test_wrap_deg_proves_at_tier_1` pins the example's headline claim.

Note what is pinned and what is not.  The example agrees with ERFA only to ~19
arcsec, because the JPL low-precision element set is an arcminute-accurate model;
the *arithmetic*, however, is deterministic to the last digit.  The exact-string
pin therefore asserts REPRODUCIBILITY of the computation, not ACCURACY of the
model.  If a better ephemeris ever motivates changing these digits, that is a
change to the model and the pin should be updated with the reference values
recomputed — not "fixed" toward some more precise source while leaving the
element set alone.
"""

from __future__ import annotations

import re
from math import acos, cos, radians, sin
from pathlib import Path

import pytest

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.verifier import verify

from tests.codegen_helpers import _compile, _run_io

EXAMPLE = Path(__file__).parent.parent / "examples" / "ephemeris.vera"

# Independent reference: ERFA's analytic model at JD 2461456.5 TT, obtained via
# astropy's `get_sun` / `get_body` on the offline 'builtin' ephemeris.  Degrees.
ERFA_REFERENCE = {
    "Sun": (332.783333, -11.214167),
    "Mars": (153.957083, +15.553333),
}

# The element set is documented as arcminute-accurate over 1800-2050, so 30
# arcsec is a tight-but-honest bound on agreement rather than a rounding fudge.
AGREEMENT_TOLERANCE_ARCSEC = 30.0


@pytest.fixture(scope="module")
def source() -> str:
    return EXAMPLE.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def obligations(source: str) -> list:
    """Verify once and share the obligation stream.

    Verifying this example is a full Z3 pass over 450 lines with float theory in
    play, so it is module-scoped rather than repeated per test.
    """
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(ast, source)
    result = verify(
        ast,
        source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    return list(result.obligations)


def _angular_separation_arcsec(
    ra1: float, dec1: float, ra2: float, dec2: float
) -> float:
    """Great-circle separation between two equatorial positions, in arcsec."""
    r1, d1, r2, d2 = (radians(v) for v in (ra1, dec1, ra2, dec2))
    cos_sep = sin(d1) * sin(d2) + cos(d1) * cos(d2) * cos(r1 - r2)
    return acos(min(1.0, max(-1.0, cos_sep))) * 206264.806247


def _parse_row(line: str) -> tuple[str, float, float]:
    """Recover (body, RA degrees, Dec degrees) from one output row.

    Deliberately parses the *rendered* text rather than calling the example's
    internals, so a formatting bug that produces a well-formed but wrong string
    is caught here rather than silently passing.
    """
    m = re.match(
        r"\s*(\w+)\s+RA\s+(\d{2})h(\d{2})m([\d.]+)s"
        r"\s+Dec\s+([+-])(\d{2})d(\d{2})m(\d{2})s",
        line,
    )
    assert m is not None, f"unparseable output row: {line!r}"
    body, rh, rm, rs, sign, dd, dm, ds = m.groups()
    ra = (int(rh) + int(rm) / 60.0 + float(rs) / 3600.0) * 15.0
    dec = int(dd) + int(dm) / 60.0 + int(ds) / 3600.0
    return body, ra, (-dec if sign == "-" else dec)


class TestEphemerisExample:
    """`examples/ephemeris.vera` compiles, runs, and holds its numbers."""

    def test_compiles(self, source: str) -> None:
        """The example compiles without errors."""
        assert _compile(source).ok

    def test_output_pinned(self, source: str) -> None:
        """Exact stdout.  Any drift — including in the last float bit — fails.

        Cross-checked against `test_agrees_with_erfa`; see the module docstring
        before updating these digits.
        """
        assert _run_io(source, fn="main") == (
            "Geocentric positions for JD 2461456.5 (2027 February 20.0 TT)\n"
            "\n"
            "  Sun    RA 22h11m09.2s   Dec -11d12m43s   0.988616 AU\n"
            "  Mars   RA 10h15m49.5s   Dec +15d33m16s   0.677839 AU\n"
        )

    def test_agrees_with_erfa(self, source: str) -> None:
        """Rendered positions match an independent model to within 30 arcsec.

        Independent of `test_output_pinned` by design: this establishes that the
        numbers are astronomically right, not merely unchanged.
        """
        rows = [
            ln for ln in _run_io(source, fn="main").splitlines()
            if "RA" in ln and "Dec" in ln
        ]
        assert len(rows) == len(ERFA_REFERENCE), f"expected two rows, got {rows}"

        for line in rows:
            body, ra, dec = _parse_row(line)
            assert body in ERFA_REFERENCE, f"unexpected body {body!r}"
            ref_ra, ref_dec = ERFA_REFERENCE[body]
            sep = _angular_separation_arcsec(ra, dec, ref_ra, ref_dec)
            assert sep < AGREEMENT_TOLERANCE_ARCSEC, (
                f"{body}: {sep:.1f} arcsec from the ERFA reference "
                f"(limit {AGREEMENT_TOLERANCE_ARCSEC}); computed "
                f"RA={ra:.6f} Dec={dec:+.6f}, reference "
                f"RA={ref_ra:.6f} Dec={ref_dec:+.6f}"
            )

    def test_distances_pinned(self, source: str) -> None:
        """Geocentric distances, to the printed precision.

        Note what this does NOT catch: reversing the operand order in `vec_sub`
        leaves both distances bit-identical, because a vector and its negation
        have the same magnitude.  Verified by perturbation — that bug moves the
        Sun 648,000 arcsec and does not budge either distance.  It is caught by
        `test_output_pinned` and `test_agrees_with_erfa`, not here.

        What this does catch is a wrong *pairing* — subtracting the wrong body's
        position, or dropping the geocentric step entirely.  Mars is near
        opposition at this epoch, so the Earth-Mars distance is close to its
        minimum; dropping the geocentric step makes Mars print Earth's own
        0.988616 AU (verified by perturbation) instead of 0.677839.
        """
        out = _run_io(source, fn="main")
        assert "0.988616 AU" in out, "Sun distance changed"
        assert "0.677839 AU" in out, "Mars distance changed"


class TestEphemerisVerification:
    """The example's contracts land in the tiers its header claims."""

    def test_wrap_deg_proves_at_tier_1(self, obligations: list) -> None:
        """`wrap_deg`'s [0, 360) range is PROVED, not runtime-checked.

        This is the example's headline claim and the reason it is worth having:
        a static proof that an angle-wrap bug cannot occur for any input.  If a
        verifier change silently demotes it to Tier 3 the example still runs and
        still prints the right answer, but its header becomes false — so the
        claim is pinned rather than left to prose.

        Note this asserts the STATUS of one named function's contracts, not a
        corpus-wide tier count.  Obligation totals move legitimately as the
        soundness work adds obligations (see the #779/#985 CHANGELOG entry), so
        pinning 48/3 here would be brittle noise.  This is the load-bearing bit.
        """
        wrap = [
            o for o in obligations
            if o.fn_name == "wrap_deg" and o.kind == "ensures"
        ]
        assert wrap, "no ensures obligation recorded for wrap_deg"
        assert all(o.status == "verified" for o in wrap), [
            (o.kind, o.status, o.expr_text) for o in wrap
        ]

    def test_transcendental_contracts_are_tier_3(self, obligations: list) -> None:
        """`declination` does NOT prove, and that asymmetry is the point.

        `right_ascension` and `declination` assert the same shape of range claim
        on an angle.  The first proves because its value returns through
        `wrap_deg`; the second cannot, because `asin` sits between the claim and
        the evidence.  Float builtins are opaque to the solver by design (#797
        maps `@Float64` to `z3.FPSort(11, 53)`), so if this ever starts proving,
        something has changed about that boundary and the example's discussion of
        it needs revisiting.
        """
        dec = [
            o for o in obligations
            if o.fn_name == "declination" and o.kind == "ensures"
        ]
        assert dec, "no ensures obligation recorded for declination"
        assert all(o.status != "verified" for o in dec), [
            (o.kind, o.status) for o in dec
        ]

        ra = [
            o for o in obligations
            if o.fn_name == "right_ascension" and o.kind == "ensures"
        ]
        assert ra, "no ensures obligation recorded for right_ascension"
        assert all(o.status == "verified" for o in ra), [
            (o.kind, o.status) for o in ra
        ]

    def test_kepler_solve_termination_proves(self, obligations: list) -> None:
        """The `decreases` metric on the Newton-Raphson loop is discharged.

        The solver's termination does not depend on numerical convergence — the
        fuel counter is what bounds it, and that bound is proved.
        """
        dec = [
            o for o in obligations
            if o.fn_name == "kepler_solve" and o.kind == "decreases"
        ]
        assert dec, "no decreases obligation recorded for kepler_solve"
        assert all(o.status == "verified" for o in dec), [
            (o.kind, o.status) for o in dec
        ]
