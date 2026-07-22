#!/usr/bin/env python
"""Verify every corpus program is in canonical form (#1124).

`examples/` and `tests/conformance/` are the corpus the language is
documented and tested by, but nothing ran `vera fmt --check` over them.
That gap is how #1112 and #1123 stayed invisible: a regression that
deleted every inline comment in the language passed the whole gate,
because the corpus carried no inline comments to lose and no check
compared it against canonical form.

A comment-count sweep is not a substitute.  Counting cannot see a
comment that *moved*, and formatting reaches a fixed point either way,
so both of those invariants stay green while a comment drifts out of
the construct it documents (#1136).  Comparing each file against its
own canonical form is the assertion that catches position.

Runs `vera fmt` in-process rather than shelling out per file: a
subprocess per corpus program costs seconds, one import costs
milliseconds.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Import from the working tree, not whatever `vera` is on PATH — a
# pre-commit hook's interpreter is not the venv's (see CLAUDE.md).
_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_ROOT))

from vera.formatter import format_source  # noqa: E402

_CORPUS_DIRS = ("examples", "tests/conformance")


def _corpus_files() -> list[Path]:
    """Every Vera source under the corpus roots, at any depth.

    `glob` rather than `rglob` checked only direct children, so the six
    imported modules under `examples/vera/` and
    `tests/conformance/vera/` were skipped -- and one of them was in
    fact non-canonical while this script reported the corpus clean.
    `examples/modules.vera` imports it, so a corpus program was built
    from source the corpus gate never looked at.  The sweep must reach
    everything `vera check` can reach.
    """
    files: list[Path] = []
    for d in _CORPUS_DIRS:
        files.extend(sorted((_ROOT / d).rglob("*.vera")))
    return files


def main() -> int:
    files = _corpus_files()
    if not files:
        print(
            "ERROR: no corpus files found — the glob or the layout moved,"
            " and an empty sweep would pass vacuously.",
            file=sys.stderr,
        )
        return 1

    stale: list[Path] = []
    broken: list[tuple[Path, str]] = []
    crlf: list[Path] = []

    for path in files:
        try:
            # Bytes, not read_text: universal-newline translation
            # erases every `\r` before the comparison, which certified
            # a CRLF (or bare-CR) file — a second byte representation
            # of the same program — as canonical.  The read sits
            # inside the try so an unreadable file (invalid UTF-8, a
            # dangling symlink) joins the report instead of aborting
            # the sweep with a traceback and hiding every file after
            # it.
            raw = path.read_bytes()
            if b"\r" in raw:
                crlf.append(path)
                continue
            source = raw.decode("utf-8")
            formatted = format_source(source, file=str(path))
        except Exception as exc:  # noqa: BLE001 - reported, not swallowed
            broken.append((path, f"{type(exc).__name__}: {exc}"))
            continue
        if formatted != source:
            stale.append(path)

    if crlf:
        print(
            f"ERROR: {len(crlf)} corpus file(s) contain CR bytes;"
            " canonical form uses LF line endings only:",
            file=sys.stderr,
        )
        for path in crlf:
            print(f"  {path.relative_to(_ROOT)}", file=sys.stderr)

    if broken:
        print(
            f"ERROR: {len(broken)} corpus file(s) could not be formatted:",
            file=sys.stderr,
        )
        for path, why in broken:
            print(f"  {path.relative_to(_ROOT)}: {why}", file=sys.stderr)

    if stale:
        print(
            f"ERROR: {len(stale)} corpus file(s) are not in canonical form:",
            file=sys.stderr,
        )
        for path in stale:
            print(f"  {path.relative_to(_ROOT)}", file=sys.stderr)
        print(
            "\nRun `vera fmt --write` on each, then re-check that"
            " `vera check` and `vera verify` still pass.",
            file=sys.stderr,
        )

    if broken or stale or crlf:
        return 1

    print(f"All {len(files)} corpus programs are in canonical form.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
