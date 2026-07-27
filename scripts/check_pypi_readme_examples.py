#!/usr/bin/env python
"""Extract Vera code blocks from PYPI_README.md and gate them end to end.

The PyPI project page is the first Vera a ``pip install veralang`` user
reads, so its ```vera blocks are held to the strongest level the content
supports: parse + check + verify (the Try-it program carries contracts the
verifier discharges).  Non-vera fences (the bash install steps) are ignored.

Intentionally failing blocks would carry the inline
``<!-- vera:skip-<stage> category="..." reason="..." -->`` annotation on the
line before the fence (#538); the exempted stage still runs, and a block
that passes it is a STALE annotation and fails the gate.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_html_examples import try_check, try_verify
from doc_annotations import evaluate_block, scan_markdown


def try_parse(content: str) -> str | None:
    """Try to parse content as a Vera program. Returns error message or None."""
    from vera.parser import parse

    try:
        parse(content, file="<pypi-readme>")
        return None
    except Exception as exc:  # noqa: BLE001 — a failing doc example is reported, not raised
        return str(exc).split("\n")[0][:200]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    doc = root / "PYPI_README.md"
    if not doc.is_file():
        print("ERROR: PYPI_README.md not found.", file=sys.stderr)
        return 1

    blocks, problems = scan_markdown(doc)
    failures: list[str] = list(problems)
    vera_blocks = 0

    for block in blocks:
        if block.lang.lower() != "vera":
            if block.annotations:
                failures.append(
                    f"line {block.line}: vera:skip annotation on a "
                    f"non-vera block (language {block.lang!r}) — remove it"
                )
            continue
        vera_blocks += 1
        outcomes = evaluate_block(block, [
            ("parse", try_parse),
            ("check", lambda content: try_check(content, root)),
            ("verify", lambda content: try_verify(content, root)),
        ])
        for outcome in outcomes:
            if outcome.status == "failed":
                failures.append(
                    f"line {block.line}: {outcome.stage} failed: {outcome.error}"
                )
            elif outcome.status == "stale":
                failures.append(
                    f"line {block.line}: stale vera:skip-{outcome.stage} "
                    f"annotation — the block passes this stage; remove it"
                )

    if failures:
        print(f"ERROR: {len(failures)} problem(s) in PYPI_README.md:")
        for failure in failures:
            print(f"  {failure}")
        return 1
    print(
        f"All {vera_blocks} PYPI_README.md Vera code blocks pass "
        f"(parse + check + verify)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
