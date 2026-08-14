#!/usr/bin/env python
"""Pre-commit / CI gate: every `examples/*.vera` program either RUNS
trap-free under the native runtime, or is matched to a documented
property that excludes it from harness execution.

`scripts/check_examples.py` type-checks and verifies all 42 examples and
`scripts/check_e602_clean.py` compiles them, so an example that fails to
parse, type-check, verify or compile is caught before this gate.  What
none of them does is *run* one.  A program can pass every static stage
and still trap the moment it executes — an out-of-bounds index behind a
Tier-3 obligation, a monomorphized clone that resolves to a missing
symbol, a host import nobody bound.  Until this gate, the only examples
protected against that were the ones some test happened to execute; the
rest could rot silently between releases.

The design's load-bearing part is the **coverage rule**, not the runs.
The script enumerates `examples/*.vera` from disk and requires every name
to appear in exactly one of two tables:

- ``RUN_SPECS`` — how to invoke it (entry point, arguments, fixtures).
- ``SKIPS`` — the property that excludes it, drawn from
  ``SKIP_PROPERTIES`` so every suppression carries a stated reason that
  the report prints.

An example in neither is an ERROR, so adding an example forces the author
to decide which it is; a table key with no file on disk is an ERROR too,
so a deleted example cannot leave a suppression behind to mask a later
re-add.  The classification is then cross-checked against the table in
TESTING.md (`check_testing_md`), on the `check_doc_counts.py` model: the
codebase is the oracle and the documentation must match it, so the
execution model stops living in maintainers' heads.

What this gate asserts is *runs green*, deliberately not *prints what it
used to*.  Output pinning belongs in the dedicated tests that already do
it — ``tests/test_db_runtime.py::TestDbOnDiskExample229`` pins
`sqlitedb.vera`'s rendered city table,
``tests/test_codegen_host_effects.py`` pins `inference_json.vera`'s
score line against a mocked provider, and ``tests/test_browser.py`` pins
21 examples against the browser runtime.  A gate that re-pinned stdout
would duplicate those and go red on every cosmetic edit to an example.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import NamedTuple


# ---------------------------------------------------------------------------
# Classification tables
# ---------------------------------------------------------------------------


class RunSpec(NamedTuple):
    """How to invoke one example under `vera run`.

    ``fn`` is ``None`` for a program with `main`.  For a no-main example
    `vera run` falls back to the *first export*, which is generally an
    arbitrary function that needs arguments, so those must pin an entry
    point explicitly.

    A ``NamedTuple`` rather than a frozen dataclass so the module can be
    loaded by the bare ``spec_from_file_location`` / ``exec_module``
    recipe the sibling script tests use: ``@dataclass`` resolves its
    annotations through ``sys.modules[cls.__module__]``, which that
    recipe leaves unregistered.
    """

    fn: str | None = None
    args: tuple[str, ...] = ()
    needs_db_fixture: bool = False


# Every skip property, with the reason it excludes harness execution.
# Printed verbatim in the report, so a reader of a gate run sees what is
# not covered and why without opening this file.
SKIP_PROPERTIES: dict[str, str] = {
    "network": (
        "makes live outbound HTTP calls, so a gate run would depend on "
        "network reachability and on a third party's uptime"
    ),
    "api-key": (
        "calls an inference provider; with a key configured in the "
        "environment the gate would issue a real, billed API request, and "
        "without one it would only ever exercise the not-configured arm"
    ),
    "stdin": (
        "reads interactive input, so what it exercises is a property of "
        "the invoking terminal rather than of the program"
    ),
    "non-scalar-entry": (
        "exports no `main` and its only entry point takes an ADT "
        "parameter, which `vera run` cannot construct from CLI arguments"
    ),
    "long-running": (
        "its only entry point is a wall-clock animation loop whose "
        "duration is fixed by deliberate `IO.sleep` calls"
    ),
}


# The 34 examples the harness runs.  Entry points and arguments follow
# the invocations documented in `examples/README.md`, which
# `scripts/check_examples_readme.py` independently holds to naming
# functions that exist.
RUN_SPECS: dict[str, RunSpec] = {
    "absolute_value": RunSpec(fn="absolute_value", args=("-5",)),
    "array_utilities": RunSpec(),
    "async_futures": RunSpec(),
    "base64": RunSpec(),
    "closures": RunSpec(fn="test_closure"),
    "collections": RunSpec(),
    "database": RunSpec(),
    "effect_handler": RunSpec(),
    "factorial": RunSpec(fn="factorial", args=("10",)),
    "file_io": RunSpec(),
    "fizzbuzz": RunSpec(),
    "gc_pressure": RunSpec(),
    "generics": RunSpec(fn="test_generics"),
    "hello_world": RunSpec(),
    "html": RunSpec(),
    "increment": RunSpec(fn="increment"),
    "json": RunSpec(),
    "list_ops": RunSpec(fn="test_list"),
    "markdown": RunSpec(),
    "maximum_syntax": RunSpec(),
    "modules": RunSpec(fn="clamp_to_range", args=("100", "0", "42")),
    "mutual_recursion": RunSpec(fn="is_even", args=("4",)),
    "nested_closures": RunSpec(fn="grid_sum"),
    "pattern_matching": RunSpec(fn="test_match"),
    "quantifiers": RunSpec(fn="test_process"),
    "refinement_types": RunSpec(fn="test_refine"),
    "regex": RunSpec(),
    "safe_divide": RunSpec(fn="safe_divide", args=("3", "10")),
    "scoreboard": RunSpec(),
    # The committed on-disk fixture, threaded the way
    # `tests/test_db_runtime.py::TestDbOnDiskExample229` threads it — without
    # it the example takes its graceful in-memory `Err` arm and the on-disk
    # read, which is the whole point of the example, never executes.
    "sqlitedb": RunSpec(needs_db_fixture=True),
    "string_ops": RunSpec(),
    "string_utilities": RunSpec(fn="padded_id"),
    "url_encoding": RunSpec(),
    "url_parsing": RunSpec(),
}


# The 8 examples excluded by property.  Each is still type-checked,
# verified and compiled by the other gates; only execution is out of
# reach here.
SKIPS: dict[str, str] = {
    "async_http_fanout": "network",
    "http": "network",
    "inference": "api-key",
    "inference_json": "api-key",
    "io_operations": "stdin",
    "read_char": "stdin",
    "http_server": "non-scalar-entry",
    "life": "long-running",
}


# Environment variables that change what an example *does*.  The runner
# strips them from the inherited environment so a gate run measures the
# examples rather than the developer's shell — an ambient `VERA_DB_URL`
# would otherwise point `database.vera` at a real database, and an
# ambient provider key would turn a run into a billed API call.  A spec
# that needs one puts its own value back.
NEUTRALISED_ENV: tuple[str, ...] = (
    "VERA_DB_URL",
    "VERA_ANTHROPIC_API_KEY",
    "VERA_OPENAI_API_KEY",
    "VERA_MOONSHOT_API_KEY",
    "VERA_MISTRAL_API_KEY",
    "VERA_XAI_API_KEY",
    "VERA_DEEPSEEK_API_KEY",
)


# Per-example wall-clock budget.  Generous: the whole 34-program set runs
# in a few seconds, so this only ever fires on a genuine hang, which is
# reported as a failure rather than blocking the hook indefinitely.
TIMEOUT_SECONDS = 300


# ---------------------------------------------------------------------------
# The coverage rule
# ---------------------------------------------------------------------------


def example_names(examples_dir: Path) -> list[str]:
    """Every standalone example program, by stem.

    Non-recursive by design: `examples/vera/` holds the modules
    `modules.vera` imports, which are libraries rather than programs and
    have no entry point of their own.
    """
    return sorted(p.stem for p in examples_dir.glob("*.vera"))


def check_coverage(
    names: list[str],
    run_specs: dict[str, RunSpec],
    skips: dict[str, str],
) -> list[str]:
    """Every name classified exactly once, every classification real.

    An empty corpus is an error rather than a vacuous pass: a glob that
    stops matching would otherwise switch the whole gate off silently,
    which is the failure this script is built to make impossible.
    """
    errors: list[str] = []
    if not names:
        errors.append(
            "no examples found — the corpus glob matched nothing.  This is "
            "an error rather than a pass: a gate with nothing to run "
            "reports success while covering zero programs."
        )
        return errors

    on_disk = set(names)
    classified = set(run_specs) | set(skips)

    for name in sorted(on_disk - classified):
        errors.append(
            f"{name}.vera is unclassified — add it to RUN_SPECS with an "
            f"entry point, or to SKIPS with a property from "
            f"SKIP_PROPERTIES explaining why the harness cannot run it."
        )

    for name in sorted(classified - on_disk):
        table = "RUN_SPECS" if name in run_specs else "SKIPS"
        errors.append(
            f"{name!r} is listed in {table} but no examples/{name}.vera "
            f"exists — remove the stale entry (a suppression outliving its "
            f"example would mask a later program of the same name)."
        )

    for name in sorted(set(run_specs) & set(skips)):
        errors.append(
            f"{name}.vera appears in both tables — an example is either "
            f"run or skipped, never both."
        )

    for name, prop in sorted(skips.items()):
        if prop not in SKIP_PROPERTIES:
            errors.append(
                f"{name}.vera is skipped for {prop!r}, which is not in "
                f"SKIP_PROPERTIES — every suppression must cite a "
                f"documented property so the report can state the reason."
            )

    return errors


# ---------------------------------------------------------------------------
# Invocation
# ---------------------------------------------------------------------------


def build_command(python: str, vera_file: Path, spec: RunSpec) -> list[str]:
    """The `vera run` argv for one example."""
    cmd = [python, "-m", "vera.cli", "run", str(vera_file)]
    if spec.fn is not None:
        cmd += ["--fn", spec.fn]
    if spec.args:
        cmd += ["--", *spec.args]
    return cmd


def spec_env(spec: RunSpec, examples_dir: Path) -> dict[str, str]:
    """The environment a spec adds on top of the inherited one."""
    if not spec.needs_db_fixture:
        return {}
    fixture = (examples_dir / "sqlitedb.sqlite").resolve()
    # POSIX form so the URL is portable on Windows, matching
    # `tests/test_db_runtime.py`; `_open_connection` strips the prefix
    # back to the filesystem path.
    return {"VERA_DB_URL": f"sqlite:///{fixture.as_posix()}"}


def build_env(
    spec: RunSpec,
    examples_dir: Path,
    base: dict[str, str] | None = None,
) -> dict[str, str]:
    """The full environment for one run: inherited, minus the variables
    that would change the example's behaviour, plus the spec's own."""
    env = dict(os.environ if base is None else base)
    for name in NEUTRALISED_ENV:
        env.pop(name, None)
    env.update(spec_env(spec, examples_dir))
    return env


def run_corpus(
    examples_dir: Path,
    run_specs: dict[str, RunSpec],
    workdir_root: Path,
) -> list[str]:
    """Run every spec; return one formatted line per failure.

    Each example gets its own scratch working directory.  `file_io.vera`
    writes `hello.txt` relative to the process CWD, so running in place
    would drop artefacts beside the examples on every gate run.
    """
    failures: list[str] = []
    for name in sorted(run_specs):
        spec = run_specs[name]
        vera_file = examples_dir / f"{name}.vera"
        if not vera_file.is_file():
            failures.append(
                f"{name}: examples/{name}.vera does not exist, so the "
                f"RUN_SPECS entry covers nothing"
            )
            continue

        workdir = workdir_root / f"run-{name}"
        workdir.mkdir(parents=True, exist_ok=True)
        try:
            result = subprocess.run(
                build_command(sys.executable, vera_file, spec),
                capture_output=True,
                text=True,
                encoding="utf-8",
                cwd=str(workdir),
                # Nothing may consume the invoking terminal's stdin: an
                # example that read it would hang the hook, and the ones
                # that do are skipped for exactly that reason.
                stdin=subprocess.DEVNULL,
                env=build_env(spec, examples_dir),
                timeout=TIMEOUT_SECONDS,
                check=False,
            )
        except subprocess.TimeoutExpired:
            failures.append(
                f"{name}: exceeded the {TIMEOUT_SECONDS}s budget — the "
                f"program hung rather than terminating"
            )
            continue

        if result.returncode != 0:
            detail = (result.stderr.strip() or result.stdout.strip()
                      or "no output")
            failures.append(
                f"{name}: `vera run` exited {result.returncode}: "
                f"{detail[:300]}"
            )
    return failures


# ---------------------------------------------------------------------------
# The TESTING.md cross-check
# ---------------------------------------------------------------------------


_TABLE_HEADING = "Example execution coverage"
_ROW_RE = re.compile(r"^\|\s*`([A-Za-z0-9_]+)\.vera`\s*\|[^|]*\|\s*([^|]+?)\s*\|")


def parse_testing_table(text: str) -> dict[str, str] | None:
    """The example → harness-disposition map from TESTING.md's table.

    ``None`` when the heading is absent — distinct from an empty dict
    (heading present, no rows), because the two need different messages
    and neither may be reported as a pass.
    """
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if line.startswith("#") and _TABLE_HEADING in line:
            start = i
            break
    if start is None:
        return None

    rows: dict[str, str] = {}
    for line in lines[start + 1:]:
        if line.startswith("#"):  # the next heading ends the subsection
            break
        m = _ROW_RE.match(line)
        if m:
            rows[m.group(1)] = m.group(2).strip()
    return rows


def check_testing_md(
    text: str,
    run_specs: dict[str, RunSpec],
    skips: dict[str, str],
) -> list[str]:
    """TESTING.md's table must agree with this script's classification."""
    rows = parse_testing_table(text)
    if rows is None:
        return [
            f"TESTING.md: no heading containing {_TABLE_HEADING!r} — the "
            f"execution-model table is the documented form of this "
            f"script's classification, and a reworded heading must fail "
            f"the gate rather than leave nothing to compare."
        ]
    if not rows:
        return [
            f"TESTING.md: the {_TABLE_HEADING!r} section has no rows the "
            f"gate can read — expected one `| `<name>.vera` | ... | "
            f"<disposition> |` row per example."
        ]

    expected = {name: "runs" for name in run_specs}
    expected.update({name: f"skip: {prop}" for name, prop in skips.items()})

    errors: list[str] = []
    for name in sorted(set(expected) - set(rows)):
        errors.append(
            f"TESTING.md: no row for {name}.vera, which this script "
            f"classifies as {expected[name]!r}"
        )
    for name in sorted(set(rows) - set(expected)):
        errors.append(
            f"TESTING.md: row for {name}.vera, which this script does not "
            f"classify — the example was renamed or removed, or the row "
            f"was never real"
        )
    for name in sorted(set(rows) & set(expected)):
        if rows[name] != expected[name]:
            errors.append(
                f"TESTING.md: {name}.vera is documented as "
                f"{rows[name]!r} but this script classifies it as "
                f"{expected[name]!r}"
            )
    return errors


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent
    examples_dir = repo_root / "examples"

    names = example_names(examples_dir)
    coverage_errors = check_coverage(names, RUN_SPECS, SKIPS)

    testing_md = repo_root / "TESTING.md"
    if testing_md.is_file():
        doc_errors = check_testing_md(
            testing_md.read_text(encoding="utf-8"), RUN_SPECS, SKIPS
        )
    else:
        doc_errors = [f"TESTING.md not found at {testing_md}"]

    # The coverage rule gates the run: with the tables out of sync with
    # disk, a green run would be reporting on the wrong set of programs.
    if coverage_errors:
        print(
            f"COVERAGE ERRORS ({len(coverage_errors)}):", file=sys.stderr
        )
        for e in coverage_errors:
            print(f"  {e}", file=sys.stderr)
        for e in doc_errors:
            print(f"  {e}", file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="vera-examples-run-") as td:
        failures = run_corpus(examples_dir, RUN_SPECS, Path(td))

    print(
        f"Ran {len(RUN_SPECS)} of {len(names)} examples under the native "
        f"runtime ({len(SKIPS)} skipped by property)."
    )
    for prop in sorted(SKIP_PROPERTIES):
        skipped = sorted(n for n, p in SKIPS.items() if p == prop)
        if skipped:
            print(f"  skip [{prop}]: {', '.join(skipped)}")
            print(f"    {SKIP_PROPERTIES[prop]}")

    if doc_errors:
        print(
            f"\nDOCUMENTATION MISMATCH ({len(doc_errors)}):", file=sys.stderr
        )
        for e in doc_errors:
            print(f"  {e}", file=sys.stderr)
        print(
            "\nTESTING.md's execution-model table is the documented form "
            "of the classification in this script.  Update the table to "
            "match, so the model stays readable without reading the "
            "source.",
            file=sys.stderr,
        )

    if failures:
        print(
            f"\nRUNTIME FAILURES ({len(failures)} example(s) that pass "
            f"check, verify and compile but do not run):",
            file=sys.stderr,
        )
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        print(
            "\nAn example that no longer runs is a bug in the compiler or "
            "in the example, not something to suppress: SKIPS is for "
            "programs the harness structurally cannot drive, not for ones "
            "that are broken.",
            file=sys.stderr,
        )

    if doc_errors or failures:
        return 1

    print("\nAll runnable examples execute trap-free.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
