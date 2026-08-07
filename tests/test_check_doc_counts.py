"""Tests for the pure per-document checks in scripts/check_doc_counts.py.

Each of these is a function of text (plus, for one, the filesystem), so it
is testable without a pytest collection run:

- ``check_refactoring_counts`` — KNOWN_ISSUES.md "Refactoring needed"
  line counts must stay within ±10% of the measured file sizes.
- ``check_history_row_format`` — HISTORY.md version rows carry at most
  one issue link and no " — " separator.
- ``check_tests_breakdown`` — TESTING.md's passed/stress/skipped parts
  must sum to the collected total.
- ``check_vera_readme_test_counts`` — the four counts in vera/README.md's
  Test Suite paragraph.

The last two share a failure mode with every other check here and it is
tested for both: a reworded sentence must be an ERROR, not a silent skip,
or rewording switches the gate off.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Any

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_doc_counts.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_doc_counts", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


def _refactoring_doc(rel: str, cited: int) -> str:
    return (
        "## Refactoring needed\n\n"
        "| File | Lines | Refactoring | Issue |\n"
        "|------|-------|-------------|-------|\n"
        f"| `{rel}` | {cited:,} | Split it. Soon. |"
        " [#1](https://github.com/aallan/vera/issues/1) |\n"
        "\n## Next section\n"
    )


def _write_lines(path: Path, n: int) -> None:
    path.write_text("x\n" * n, encoding="utf-8")


class TestRefactoringCounts:
    def test_exact_match_passes(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 1000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1000), tmp_path
        )
        assert errors == []

    def test_within_tolerance_passes(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 1000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 950), tmp_path
        )
        assert errors == []

    def test_drift_beyond_tolerance_fails(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 2000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1000), tmp_path
        )
        assert len(errors) == 1
        assert ">10% drift" in errors[0]
        assert "big.py" in errors[0]

    def test_exact_tolerance_boundary_passes(self, tmp_path: Path) -> None:
        _write_lines(tmp_path / "big.py", 1000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1100), tmp_path
        )
        assert errors == []

    def test_empty_file_with_nonzero_citation_fails(
        self, tmp_path: Path
    ) -> None:
        (tmp_path / "big.py").write_text("", encoding="utf-8")
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("big.py", 1000), tmp_path
        )
        assert len(errors) == 1
        assert "measured 0" in errors[0]

    def test_hyphenated_path_matched(self, tmp_path: Path) -> None:
        (tmp_path / "spec").mkdir()
        _write_lines(tmp_path / "spec" / "09-standard-library.md", 2000)
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("spec/09-standard-library.md", 1000), tmp_path
        )
        assert len(errors) == 1
        assert ">10% drift" in errors[0]

    def test_empty_section_with_sentinel_passes(self, tmp_path: Path) -> None:
        """The #419 empty-state convention: once the last oversized file is
        split, the table is replaced by this exact sentence and the gate
        accepts the rowless section."""
        doc = (
            "## Refactoring needed\n\n"
            "No files currently need decomposition.\n"
            "\n## Next section\n"
        )
        assert _MOD.check_refactoring_counts(doc, tmp_path) == []

    def test_empty_section_without_sentinel_fails(self, tmp_path: Path) -> None:
        """The sentinel carve-out must not mask a malformed table: a rowless
        section with any OTHER wording (e.g. a reworded sentence, or a table
        whose rows no longer parse) still trips the gate."""
        doc = (
            "## Refactoring needed\n\n"
            "Nothing needs decomposing right now.\n"
            "\n## Next section\n"
        )
        errors = _MOD.check_refactoring_counts(doc, tmp_path)
        assert len(errors) == 1
        assert "no `file` | count rows" in errors[0]

    def test_missing_file_fails(self, tmp_path: Path) -> None:
        errors = _MOD.check_refactoring_counts(
            _refactoring_doc("gone.py", 1000), tmp_path
        )
        assert len(errors) == 1
        assert "does not exist" in errors[0]

    def test_missing_section_fails(self, tmp_path: Path) -> None:
        errors = _MOD.check_refactoring_counts("# No tables here\n", tmp_path)
        assert errors and "Refactoring needed" in errors[0]

    def test_empty_table_fails(self, tmp_path: Path) -> None:
        text = "## Refactoring needed\n\nNothing tabulated.\n\n## Next\n"
        errors = _MOD.check_refactoring_counts(text, tmp_path)
        assert errors and "no" in errors[0]


_LINK = "[#100](https://github.com/aallan/vera/issues/100)"
_LINK2 = "[#200](https://github.com/aallan/vera/issues/200)"


class TestHistoryRowFormat:
    def test_clean_row_passes(self) -> None:
        text = f"| v0.0.5 | 1 Mar | One sentence with one link ({_LINK}). |\n"
        assert _MOD.check_history_row_format(text) == []

    def test_two_links_fail(self) -> None:
        text = f"| v0.0.5 | 1 Mar | Two fixes ({_LINK}, {_LINK2}). |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "2 issue links" in errors[0]

    def test_single_lead_in_dash_passes(self) -> None:
        # The v0.1.x-era template: **bold lead-in** — clauses (one dash).
        text = "| v0.1.5 | 1 Mar | **Feature** — detail clause. |\n"
        assert _MOD.check_history_row_format(text) == []

    def test_second_em_dash_fails(self) -> None:
        text = "| v0.0.5 | 1 Mar | Feature — detail — second clause. |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "separator" in errors[0]

    def test_v01_rows_are_inspected(self) -> None:
        # The pre-#972 regex was pinned to v0.0.x; v0.1.x rows went
        # uninspected entirely.
        text = f"| v0.1.5 | 1 Mar | Two fixes ({_LINK}, {_LINK2}). |\n"
        errors = _MOD.check_history_row_format(text)
        assert len(errors) == 1
        assert "2 issue links" in errors[0]

    def test_dateless_rows_exempt(self) -> None:
        text = f"| — | 1 Mar | Tooling row — with links {_LINK} {_LINK2}. |\n"
        assert _MOD.check_history_row_format(text) == []

    def test_prose_and_headers_exempt(self) -> None:
        text = (
            "Prose with — dashes and links to issues/1 issues/2.\n"
            "| Version | Date | What shipped |\n"
            "|---------|------|-------------|\n"
        )
        assert _MOD.check_history_row_format(text) == []

    def test_reports_line_numbers(self) -> None:
        text = "line one\n| v0.0.9 | 2 Mar | Bad — row — twice. |\n"
        errors = _MOD.check_history_row_format(text)
        assert "line 2" in errors[0]


def _overview(passed: int, stress: int, skipped: int, total: int) -> str:
    return (
        "| Metric | Value |\n"
        "|--------|-------|\n"
        f"| **Tests** | {total:,} across 143 files (~108,000 lines of test"
        f" code; {passed:,} passed + {stress} stress, {skipped} skipped) |\n"
    )


class TestTestsBreakdown:
    def test_parts_summing_to_the_total_pass(self) -> None:
        text = _overview(9235, 26, 121, 9382)
        assert _MOD.check_tests_breakdown(text, 9382) == []

    def test_parts_not_summing_to_the_total_fail(self) -> None:
        # The shape that motivated the check: the total is refreshed at
        # release time because a gate reads it, the parts are not.
        text = _overview(9230, 26, 121, 9382)
        errors = _MOD.check_tests_breakdown(text, 9382)
        assert len(errors) == 1
        assert "9,377" in errors[0]
        assert "9,382" in errors[0]

    def test_a_right_total_with_wrong_parts_still_fails(self) -> None:
        # The row's own total is NOT what the parts are checked against —
        # the collected count is — so a self-consistent but stale row is
        # caught by the existing total check, and an inconsistent one here.
        text = _overview(9000, 26, 121, 9147)
        errors = _MOD.check_tests_breakdown(text, 9382)
        assert len(errors) == 1

    def test_reworded_row_is_an_error_not_a_skip(self) -> None:
        text = (
            "| **Tests** | 9,382 across 143 files (~108,000 lines of test"
            " code; 9,235 green, 26 stress and 121 skipped) |\n"
        )
        errors = _MOD.check_tests_breakdown(text, 9382)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]


def _test_suite_para(
    tests: int, files: int, conformance: int, examples: int
) -> str:
    return (
        "## Test Suite\n\n"
        f"Testing spans a **pytest suite** of {tests:,} tests across {files}"
        " files — compiler-internals unit tests plus a **conformance suite**"
        f" ({conformance} programs in `tests/conformance/` validating every"
        " language feature against the spec) and **example programs**"
        f" ({examples} end-to-end demos).\n"
    )


class TestVeraReadmeTestCounts:
    def test_matching_counts_pass(self) -> None:
        text = _test_suite_para(9382, 143, 196, 42)
        assert _MOD.check_vera_readme_test_counts(
            text, 9382, 143, 196, 42
        ) == []

    def test_every_count_is_checked_independently(self) -> None:
        text = _test_suite_para(1, 2, 3, 4)
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        # Four separate citations, four separate errors — a single
        # aggregate would let three stay wrong after one is fixed.
        assert len(errors) == 4
        joined = " ".join(errors)
        for label in (
            "total tests",
            "test file count",
            "conformance programs",
            "example programs",
        ):
            assert label in joined

    def test_stale_example_count_alone_fails(self) -> None:
        text = _test_suite_para(9382, 143, 196, 37)
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "example programs" in errors[0]

    def test_reworded_paragraph_is_an_error_not_a_skip(self) -> None:
        text = (
            "## Test Suite\n\nTesting spans 9,382 tests in 143 modules,"
            " 196 conformance programs and 42 demos.\n"
        )
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]
