"""Tests for scripts/check_examples_run.py — the harness gate that RUNS
the examples.

The gate's design has three separable parts, and each is tested here:

- **The coverage rule** (`check_coverage`) — every ``examples/*.vera`` on
  disk is either in ``RUN_SPECS`` or in ``SKIPS``.  An unclassified
  example is an ERROR, so adding an example forces classifying it; a
  table key with no file on disk is an ERROR too, so a deleted example
  cannot leave a suppression behind.
- **The documentation cross-check** (`check_testing_md`) — TESTING.md's
  execution-model table must agree with the script's own classification,
  the `check_doc_counts.py` model: the codebase is the oracle and the doc
  must match it.
- **The runner** (`run_corpus`) — a seeded corpus proves the gate goes red
  on a program that traps at runtime and green on one that does not.

Two conventions are inherited from ``tests/test_check_doc_counts.py`` and
asserted throughout: a regex or glob that matches nothing must be an
ERROR rather than a silent pass (otherwise a rewording switches the gate
off), and each check is exercised in both directions — a passing case
alongside the failing one it is supposed to catch, so a check that can
only ever return ``[]`` cannot masquerade as green.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Any

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_examples_run.py"
_ROOT = Path(__file__).parent.parent


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_examples_run", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


# ---------------------------------------------------------------------------
# Synthetic corpora
# ---------------------------------------------------------------------------

# A program that returns a value and exits cleanly.
_CLEAN_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1 + 1
}
"""

# A program that type-checks and compiles but traps at runtime: the index
# is out of bounds, so the emitted bounds guard fires.  This is the shape
# the gate exists to catch — `vera check` and `vera verify` both accept a
# program whose runtime behaviour is broken.
_TRAPPING_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[10]
}
"""


def _corpus(tmp_path: Path, programs: dict[str, str]) -> Path:
    d = tmp_path / "examples"
    d.mkdir(exist_ok=True)
    for name, src in programs.items():
        (d / f"{name}.vera").write_text(src, encoding="utf-8")
    return d


# ---------------------------------------------------------------------------
# The coverage rule
# ---------------------------------------------------------------------------


class TestCoverageRule:
    """Every example is classified; nothing is classified that isn't there."""

    def test_real_corpus_is_fully_classified(self) -> None:
        """The shipped tables cover the shipped corpus — no unclassified
        example, no stale key.  This is the assertion that goes red when
        somebody adds `examples/new_thing.vera` without deciding whether
        the harness can run it."""
        names = _MOD.example_names(_ROOT / "examples")
        assert _MOD.check_coverage(names, _MOD.RUN_SPECS, _MOD.SKIPS) == []

    def test_every_example_on_disk_appears_in_exactly_one_table(self) -> None:
        names = set(_MOD.example_names(_ROOT / "examples"))
        assert names == set(_MOD.RUN_SPECS) | set(_MOD.SKIPS)
        assert not (set(_MOD.RUN_SPECS) & set(_MOD.SKIPS))

    def test_unclassified_example_is_an_error(self) -> None:
        """The heart of the anti-rot rule: an example on disk that neither
        table names fails the gate."""
        errors = _MOD.check_coverage(
            ["known", "brand_new"], {"known": _MOD.RunSpec()}, {}
        )
        assert len(errors) == 1
        assert "brand_new" in errors[0]
        assert "unclassified" in errors[0].lower()

    def test_stale_run_spec_is_an_error(self) -> None:
        """A RUN_SPECS key whose file was deleted or renamed is an error —
        otherwise the entry silently stops covering anything."""
        errors = _MOD.check_coverage(
            ["known"],
            {"known": _MOD.RunSpec(), "deleted": _MOD.RunSpec()},
            {},
        )
        assert len(errors) == 1
        assert "deleted" in errors[0]

    def test_stale_skip_is_an_error(self) -> None:
        """The same for a skip: a suppression outliving its example would
        quietly mask a re-added example with the same name."""
        errors = _MOD.check_coverage(
            ["known"], {"known": _MOD.RunSpec()}, {"gone": "network"}
        )
        assert len(errors) == 1
        assert "gone" in errors[0]

    def test_example_in_both_tables_is_an_error(self) -> None:
        """Ambiguous classification: which one wins is not a question the
        gate should have to answer."""
        errors = _MOD.check_coverage(
            ["both"], {"both": _MOD.RunSpec()}, {"both": "network"}
        )
        assert any("both" in e and "both tables" in e for e in errors)

    def test_unknown_skip_property_is_an_error(self) -> None:
        """A skip must cite a property from the documented set, so every
        suppression carries a stated reason the report can print."""
        errors = _MOD.check_coverage(["x"], {}, {"x": "because-i-said-so"})
        assert len(errors) == 1
        assert "because-i-said-so" in errors[0]
        assert "SKIP_PROPERTIES" in errors[0]

    def test_empty_corpus_is_an_error(self) -> None:
        """A glob that matches nothing is an ERROR, not a vacuous pass.
        Without this the gate reports success the moment its glob stops
        matching — the failure mode the whole check exists to rule out."""
        errors = _MOD.check_coverage([], {}, {})
        assert len(errors) == 1
        assert "no examples" in errors[0].lower()

    def test_example_names_reads_from_disk(self, tmp_path: Path) -> None:
        d = _corpus(tmp_path, {"b": _CLEAN_SRC, "a": _CLEAN_SRC})
        assert _MOD.example_names(d) == ["a", "b"]

    def test_example_names_ignores_nested_module_libraries(
        self, tmp_path: Path
    ) -> None:
        """`examples/vera/` holds the modules `modules.vera` imports.  They
        are not standalone programs and the corpus glob must not treat them
        as unclassified examples."""
        d = _corpus(tmp_path, {"top": _CLEAN_SRC})
        nested = d / "vera"
        nested.mkdir()
        (nested / "lib.vera").write_text(_CLEAN_SRC, encoding="utf-8")
        assert _MOD.example_names(d) == ["top"]


class TestRunSpecsAreWellFormed:
    """The specs must name entry points that exist, or the gate would be
    measuring `vera run`'s argument handling rather than the examples."""

    def test_every_named_fn_is_public_in_its_example(self) -> None:
        bad = []
        for name, spec in _MOD.RUN_SPECS.items():
            if spec.fn is None:
                continue
            src = (_ROOT / "examples" / f"{name}.vera").read_text(
                encoding="utf-8"
            )
            if f"public fn {spec.fn}(" not in src:
                bad.append(f"{name}: no `public fn {spec.fn}`")
        assert bad == []

    def test_examples_without_main_carry_an_explicit_entry_point(self) -> None:
        """`vera run` with no `--fn` falls back to the first export, which
        for a no-main example is an arbitrary function that usually needs
        arguments.  Every runnable no-main example must therefore pin its
        entry point."""
        bad = []
        for name, spec in _MOD.RUN_SPECS.items():
            src = (_ROOT / "examples" / f"{name}.vera").read_text(
                encoding="utf-8"
            )
            if "public fn main(" not in src and spec.fn is None:
                bad.append(name)
        assert bad == []

    def test_every_skip_property_is_documented(self) -> None:
        for name, prop in _MOD.SKIPS.items():
            assert prop in _MOD.SKIP_PROPERTIES, name
            assert _MOD.SKIP_PROPERTIES[prop].strip(), prop

    def test_no_unused_skip_property(self) -> None:
        """A property nothing cites is dead documentation that would drift."""
        assert set(_MOD.SKIP_PROPERTIES) == set(_MOD.SKIPS.values())


class TestBuildCommand:
    def test_main_entry_point_passes_no_fn_flag(self) -> None:
        cmd = _MOD.build_command("py", Path("/x/a.vera"), _MOD.RunSpec())
        assert "--fn" not in cmd
        assert cmd[:4] == ["py", "-m", "vera.cli", "run"]

    def test_named_entry_point_and_args(self) -> None:
        cmd = _MOD.build_command(
            "py", Path("/x/a.vera"), _MOD.RunSpec(fn="f", args=("1", "-2"))
        )
        assert cmd[-5:] == ["--fn", "f", "--", "1", "-2"]

    def test_db_fixture_env_points_at_the_committed_sqlite(self) -> None:
        env = _MOD.spec_env(
            _MOD.RunSpec(needs_db_fixture=True), _ROOT / "examples"
        )
        assert env["VERA_DB_URL"].startswith("sqlite:///")
        assert env["VERA_DB_URL"].endswith("examples/sqlitedb.sqlite")

    def test_no_db_fixture_adds_no_env(self) -> None:
        assert _MOD.spec_env(_MOD.RunSpec(), _ROOT / "examples") == {}


class TestHermeticEnvironment:
    """The gate must measure the examples, not the developer's shell.

    `database.vera` and `sqlitedb.vera` both read `VERA_DB_URL`, and the
    inference examples read six provider keys.  An ambient value would
    change what the gate exercises — at worst pointing a run at somebody's
    real database — so the runner strips them and puts back only what a
    spec explicitly asks for.
    """

    def test_ambient_db_url_is_stripped(self) -> None:
        env = _MOD.build_env(
            _MOD.RunSpec(), _ROOT / "examples",
            {"VERA_DB_URL": "postgres://prod/live", "PATH": "/bin"},
        )
        assert "VERA_DB_URL" not in env
        assert env["PATH"] == "/bin"

    def test_ambient_provider_keys_are_stripped(self) -> None:
        base = {f"VERA_{p}_API_KEY": "sk-real" for p in
                ("ANTHROPIC", "OPENAI", "MOONSHOT", "MISTRAL", "XAI",
                 "DEEPSEEK")}
        env = _MOD.build_env(_MOD.RunSpec(), _ROOT / "examples", base)
        assert [k for k in env if k.endswith("_API_KEY")] == []

    def test_fixture_spec_puts_its_own_db_url_back(self) -> None:
        env = _MOD.build_env(
            _MOD.RunSpec(needs_db_fixture=True), _ROOT / "examples",
            {"VERA_DB_URL": "postgres://prod/live"},
        )
        assert env["VERA_DB_URL"].startswith("sqlite:///")
        assert "prod" not in env["VERA_DB_URL"]

    def test_every_neutralised_name_is_actually_read_by_an_example(
        self,
    ) -> None:
        """Neutralising a variable nothing reads is dead configuration.
        Each name must appear in the runtime that backs the effect the
        examples use, so the list shrinks when a provider goes away."""
        runtime = (_ROOT / "vera" / "runtime").rglob("*.py")
        blob = "\n".join(p.read_text(encoding="utf-8") for p in runtime)
        for name in _MOD.NEUTRALISED_ENV:
            assert name in blob, name


# ---------------------------------------------------------------------------
# The runner
# ---------------------------------------------------------------------------


class TestRunnerGoesRedOnRuntimeFailure:
    """The proving test: a seeded corpus whose program traps must fail the
    gate.  A runner that never reports a failure would pass every other
    test in this file."""

    def test_trapping_example_fails_the_gate(self, tmp_path: Path) -> None:
        d = _corpus(tmp_path, {"boom": _TRAPPING_SRC})
        failures = _MOD.run_corpus(d, {"boom": _MOD.RunSpec()}, tmp_path)
        assert len(failures) == 1
        assert "boom" in failures[0]

    def test_clean_example_passes_the_gate(self, tmp_path: Path) -> None:
        d = _corpus(tmp_path, {"fine": _CLEAN_SRC})
        assert _MOD.run_corpus(d, {"fine": _MOD.RunSpec()}, tmp_path) == []

    def test_mixed_corpus_reports_only_the_broken_one(
        self, tmp_path: Path
    ) -> None:
        """Chosen so a runner that reported every program, or none, is
        distinguishable from one that reports the right one."""
        d = _corpus(tmp_path, {"fine": _CLEAN_SRC, "boom": _TRAPPING_SRC})
        failures = _MOD.run_corpus(
            d, {"fine": _MOD.RunSpec(), "boom": _MOD.RunSpec()}, tmp_path
        )
        assert len(failures) == 1
        assert "boom" in failures[0]
        assert "fine" not in failures[0]

    def test_named_entry_point_is_actually_invoked(
        self, tmp_path: Path
    ) -> None:
        """A runner that ignored ``spec.fn`` would call the first export and
        pass.  Here the first export is clean and the named one traps, so
        only a runner that honours the spec goes red."""
        src = """\
public fn first(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn second(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1];
  @Array<Int>.0[9]
}
"""
        d = _corpus(tmp_path, {"pick": src})
        assert _MOD.run_corpus(d, {"pick": _MOD.RunSpec()}, tmp_path) == []
        failures = _MOD.run_corpus(
            d, {"pick": _MOD.RunSpec(fn="second")}, tmp_path
        )
        assert len(failures) == 1

    def test_runner_does_not_write_into_the_corpus(
        self, tmp_path: Path
    ) -> None:
        """`file_io.vera` writes `hello.txt` relative to the process CWD.
        The runner must give each example a scratch working directory so a
        gate run leaves no artefact beside the examples."""
        src = """\
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.write_file("side_effect.txt", "x") {
    Ok(_) -> (),
    Err(@String) -> IO.print(@String.0)
  };

  ()
}
"""
        d = _corpus(tmp_path, {"writer": src})
        before = sorted(p.name for p in d.iterdir())
        assert _MOD.run_corpus(d, {"writer": _MOD.RunSpec()}, tmp_path) == []
        assert sorted(p.name for p in d.iterdir()) == before

    def test_missing_file_for_a_spec_is_a_failure(
        self, tmp_path: Path
    ) -> None:
        """Belt-and-braces against the runner silently skipping what it
        cannot find; `check_coverage` catches this earlier, but the runner
        must not turn a missing file into a pass on its own."""
        d = _corpus(tmp_path, {"present": _CLEAN_SRC})
        failures = _MOD.run_corpus(
            d, {"present": _MOD.RunSpec(), "absent": _MOD.RunSpec()}, tmp_path
        )
        assert len(failures) == 1
        assert "absent" in failures[0]
        # The specific wording, not merely *a* failure: `vera run` on a path
        # that isn't there exits non-zero of its own accord, so the generic
        # exit-code arm reports this case even with the guard removed.  What
        # the guard adds is the diagnosis — that a RUN_SPECS entry covers
        # nothing — and only asserting that makes the test able to tell the
        # two apart.
        assert "covers nothing" in failures[0]


# ---------------------------------------------------------------------------
# The TESTING.md cross-check
# ---------------------------------------------------------------------------


def _table(rows: list[tuple[str, str]]) -> str:
    body = "\n".join(
        f"| `{name}.vera` | some prose | {gate} |" for name, gate in rows
    )
    return (
        "### Example execution coverage\n\n"
        "| Example | Executed by | Harness gate |\n"
        "|---------|-------------|--------------|\n"
        f"{body}\n\n"
        "## Next section\n"
    )


class TestTestingMdCrossCheck:
    """docs must match the codebase — the `check_doc_counts.py` model."""

    def test_shipped_testing_md_matches_the_shipped_tables(self) -> None:
        text = (_ROOT / "TESTING.md").read_text(encoding="utf-8")
        assert _MOD.check_testing_md(text, _MOD.RUN_SPECS, _MOD.SKIPS) == []

    def test_matching_table_passes(self) -> None:
        doc = _table([("a", "runs"), ("b", "skip: network")])
        errors = _MOD.check_testing_md(
            doc, {"a": _MOD.RunSpec()}, {"b": "network"}
        )
        assert errors == []

    def test_missing_row_is_an_error(self) -> None:
        doc = _table([("a", "runs")])
        errors = _MOD.check_testing_md(
            doc, {"a": _MOD.RunSpec()}, {"b": "network"}
        )
        assert len(errors) == 1
        assert "b.vera" in errors[0]

    def test_extra_row_is_an_error(self) -> None:
        doc = _table([("a", "runs"), ("ghost", "runs")])
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        assert "ghost" in errors[0]

    def test_renamed_example_is_an_error_naming_both_sides(self) -> None:
        """The rename case: the doc still cites the old name and the script
        the new one, so the reader is told which is which rather than just
        that a count is off."""
        doc = _table([("old_name", "runs")])
        errors = _MOD.check_testing_md(doc, {"new_name": _MOD.RunSpec()}, {})
        joined = " ".join(errors)
        assert "old_name" in joined
        assert "new_name" in joined

    def test_wrong_gate_disposition_is_an_error(self) -> None:
        doc = _table([("a", "skip: network")])
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        assert "a.vera" in errors[0]

    def test_wrong_skip_property_is_an_error(self) -> None:
        """Same disposition, different property: documenting `http.vera` as
        skipped for the wrong reason is a lie the gate must catch."""
        doc = _table([("a", "skip: stdin")])
        errors = _MOD.check_testing_md(doc, {}, {"a": "network"})
        assert len(errors) == 1
        assert "network" in errors[0]

    def test_reworded_heading_is_an_error_not_a_silent_pass(self) -> None:
        """The convention this whole file turns on: if the anchor the check
        keys off is reworded away, the check must fail loudly rather than
        find nothing to compare and report success."""
        doc = (
            "### Some other heading entirely\n\n"
            "| Example | Executed by | Harness gate |\n"
            "|---------|-------------|--------------|\n"
            "| `a.vera` | prose | runs |\n"
        )
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        # The *missing-heading* diagnosis specifically.  Both this branch and
        # the empty-table one below name the heading, so asserting the
        # heading alone passes whichever fires — the coinciding-message trap.
        # `parse_testing_table` returns None here and an empty dict there,
        # and `None` is falsy, so a missing-heading case that fell through
        # would be reported as an empty table and read as a pass.
        assert "no heading containing" in errors[0]
        assert "Example execution coverage" in errors[0]

    def test_heading_present_but_table_empty_is_an_error(self) -> None:
        doc = (
            "### Example execution coverage\n\n"
            "The table went away in a refactor.\n\n"
            "## Next section\n"
        )
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        assert "no rows" in errors[0].lower()

    def test_table_parse_stops_at_the_next_heading(self) -> None:
        """A row-shaped line in a later section must not be swept in as an
        example row — the parse is scoped to the subsection."""
        doc = _table([("a", "runs")]).replace(
            "## Next section\n",
            "## Next section\n\n| `ghost.vera` | x | runs |\n",
        )
        assert _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {}) == []
