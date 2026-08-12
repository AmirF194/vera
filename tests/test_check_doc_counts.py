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
- ``check_release_count`` — README.md's and HISTORY.md's release counts,
  against each other AND against the repository's tags.

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

    def test_thousands_separators_are_read_in_every_count(self) -> None:
        # The prose writes counts with thousands separators once they cross
        # a thousand.  A digits-only group for any of the four would stop
        # matching at that point and report the paragraph as ungated —
        # switching the check off exactly when the number it guards grows.
        text = (
            "## Test Suite\n\n"
            "Testing spans a **pytest suite** of 12,345 tests across 1,143"
            " files — compiler-internals unit tests plus a **conformance"
            " suite** (1,196 programs in `tests/conformance/` validating"
            " every language feature against the spec) and **example"
            " programs** (1,042 end-to-end demos).\n"
        )
        assert _MOD.check_vera_readme_test_counts(
            text, 12345, 1143, 1196, 1042
        ) == []

    def test_counts_are_read_from_the_test_suite_section_only(self) -> None:
        # The pattern spans several sentences, so it matches with DOTALL.
        # Run against the whole file that lets the paragraph's head pair
        # with digits from any LATER section: the Test Suite paragraph can
        # be reworded — no longer stating the counts at all — and the gate
        # still greens off a decoy elsewhere.  That is the silent skip this
        # check exists to prevent, so it must fail loud instead.
        text = (
            "## Test Suite\n\n"
            "Testing spans a **pytest suite** of 9,382 tests across 143"
            " files — unit tests, 196 conformance programs and 42"
            " examples.\n\n"
            "## Current Limitations\n\n"
            "Historic note: the suite once shipped (196 programs in"
            " `tests/conformance/` validating every feature) and (42"
            " end-to-end demos).\n"
        )
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]

    def test_missing_test_suite_heading_is_an_error_not_a_skip(self) -> None:
        # Renaming the heading moves the paragraph out of the slice; the
        # counts must stop being "checked" loudly, not quietly.
        text = _test_suite_para(9382, 143, 196, 42).replace(
            "## Test Suite", "## Testing"
        )
        errors = _MOD.check_vera_readme_test_counts(text, 9382, 143, 196, 42)
        assert len(errors) == 1
        assert "no longer gated" in errors[0]


def _readme(n: int) -> str:
    return f"Vera is in **active development** at v0.1.10: {n} releases, x.\n"


def _history(n: int) -> str:
    return f"Total: **2,000+ commits, {n} tagged releases, 103 days.**\n"


_TAGS = [f"v0.1.{i}" for i in range(10)]  # ten tags, v0.1.9 the newest


class TestReleaseCount:
    """The release count against the tags, not just against itself.

    README's status line and HISTORY's "By the numbers" total are one
    hand-maintained number in two places.  Cross-checking them against
    EACH OTHER catches a half-applied bump and nothing else: from
    v0.1.8 both read 206 while the repository held 207 tags, agreeing
    with each other the whole way down.  Two documents can be
    consistently wrong, so the tags are the oracle.

    The fixture is ten tags, `v0.1.0`..`v0.1.9`, so "10" is the count
    once the newest is tagged and "11" the count while an eleventh
    release is being cut.
    """

    def test_counts_matching_the_tags_pass(self) -> None:
        assert _MOD.check_release_count(
            _readme(10), _history(10), _TAGS, "0.1.9",
        ) == []

    def test_a_release_cut_counts_its_own_pending_tag(self) -> None:
        # The convention: the PR that bumps the version to an UNTAGGED
        # release also bumps the count, because the release workflow
        # creates that tag only after the merge.  Requiring equality
        # with `git tag` would fail exactly those PRs.
        assert _MOD.check_release_count(
            _readme(11), _history(11), _TAGS, "0.1.10",
        ) == []

    def test_the_pending_tag_is_the_only_slack(self) -> None:
        # Once the version IS tagged, +1 is drift, not a pending release.
        errors = _MOD.check_release_count(
            _readme(11), _history(11), _TAGS, "0.1.9",
        )
        assert len(errors) == 2, errors
        assert "README.md" in errors[0] and "HISTORY.md" in errors[1]

    def test_the_drift_that_shipped_is_caught(self) -> None:
        # v0.1.10's actual state: both documents two behind the tags.
        errors = _MOD.check_release_count(
            _readme(8), _history(8), _TAGS, "0.1.10",
        )
        assert len(errors) == 2, errors
        for err in errors:
            assert "11" in err, err

    def test_each_document_is_reported_separately(self) -> None:
        # One aggregate error would let the second document stay wrong
        # after the first is fixed.
        errors = _MOD.check_release_count(
            _readme(11), _history(8), _TAGS, "0.1.10",
        )
        joined = " ".join(errors)
        assert "HISTORY.md" in joined
        assert any("mismatch" in e for e in errors), errors

    def test_readme_and_history_must_still_agree(self) -> None:
        errors = _MOD.check_release_count(
            _readme(10), _history(9), _TAGS, "0.1.9",
        )
        assert any("mismatch" in e for e in errors), errors

    def test_no_tags_skips_the_oracle_but_not_the_cross_check(self) -> None:
        # A clone without tags (a shallow CI checkout) yields None, which
        # means "no evidence", not "zero releases".  The tag comparison
        # stands down; the two documents must still agree.
        assert _MOD.check_release_count(
            _readme(999), _history(999), None, "0.1.10",
        ) == []
        errors = _MOD.check_release_count(
            _readme(999), _history(998), None, "0.1.10",
        )
        assert any("mismatch" in e for e in errors), errors

    def test_a_reworded_line_is_an_error_not_a_skip(self) -> None:
        # Rewording either sentence must switch the gate OFF loudly.
        errors = _MOD.check_release_count(
            "Vera is at v0.1.10 with lots of releases.\n",
            _history(11), _TAGS, "0.1.10",
        )
        assert any("README.md" in e and "not found" in e for e in errors), (
            errors
        )
        errors = _MOD.check_release_count(
            _readme(11), "Total: 2,000+ commits.\n", _TAGS, "0.1.10",
        )
        assert any("HISTORY.md" in e and "not found" in e for e in errors), (
            errors
        )


def _git_repo(path: Path, tags: tuple[str, ...]) -> Path:
    import subprocess

    # Same sanitised environment the reader uses, taken from the module
    # rather than copied, so the two cannot fall out of step.  Under
    # pre-commit `GIT_DIR`/`GIT_INDEX_FILE` are set, and every command
    # below would then act on the repository being committed to instead
    # of this one — a `git init` under an inherited `GIT_DIR`
    # reinitialises THAT repository, which is not a failure mode to
    # discover twice.  The check is made before any git runs, because
    # `init` is itself the damaging step: a guard after it would fire
    # too late to prevent anything.
    env = _MOD.git_env()
    leaked = set(_MOD.GIT_REPO_ENV_VARS) & set(env)
    assert not leaked, leaked

    def run(*args: str) -> None:
        subprocess.run(
            ["git", "-C", str(path), *args],
            check=True, capture_output=True, text=True, encoding="utf-8",
            env=env,
        )

    path.mkdir(parents=True, exist_ok=True)
    run("init", "-q")
    run("-c", "user.email=t@e.invalid", "-c", "user.name=T",
        "commit", "-q", "--allow-empty", "-m", "seed")
    for tag in tags:
        run("tag", tag)
    return path


class TestReleaseTags:
    """The reader that decides whether the oracle runs at all.

    `check_release_count` stands down when handed ``None``, so a reader
    that answered ``None`` everywhere would switch the gate off in
    silence — the failure mode every other check in this script is
    written against.  These pin both answers on real repositories.
    """

    def test_release_tags_are_read(self, tmp_path: Path) -> None:
        repo = _git_repo(tmp_path / "r", ("v0.1.9", "v0.1.10", "v0.0.24.1"))
        assert sorted(_MOD.release_tags(repo)) == [
            "v0.0.24.1", "v0.1.10", "v0.1.9",
        ]

    def test_non_release_tags_are_not_counted(self, tmp_path: Path) -> None:
        # A `nightly` or `v1.0.0-rc1` is not a release; counting one
        # would push the expected count past every document at once.
        repo = _git_repo(tmp_path / "r", ("v0.1.9", "nightly", "v1.0.0-rc1"))
        assert _MOD.release_tags(repo) == ["v0.1.9"]

    def test_a_checkout_without_tags_is_no_evidence(
        self, tmp_path: Path,
    ) -> None:
        # None, not [] — an empty list would read as "zero releases" and
        # make every documented count wrong.
        repo = _git_repo(tmp_path / "r", ())
        assert _MOD.release_tags(repo) is None

    def test_a_directory_that_is_not_a_repository_is_no_evidence(
        self, tmp_path: Path,
    ) -> None:
        plain = tmp_path / "plain"
        plain.mkdir()
        assert _MOD.release_tags(plain) is None
