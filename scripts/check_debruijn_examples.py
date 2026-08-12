#!/usr/bin/env python
"""Extract code blocks from DE_BRUIJN.md and verify parseable ones still parse.

Thin wrapper over the shared parse-only doc gate in scripts/doc_annotations.py
(one gate, five documents: SKILL.md, FAQ.md, README.md, EXAMPLES.md,
DE_BRUIJN.md).

DE_BRUIJN.md is the canonical explainer for `@T.n`, so its examples are read
as models to copy; two of them — §5.6's closures — wrote a function type
inline in return position and had never parsed.  Nothing was watching, which
is the gap this closes rather than the two examples.

Intentionally unparseable blocks carry an inline
`<!-- vera:skip-parse category="..." reason="..." -->` annotation on the
line before the fence (#538).  Annotated blocks are still parsed: one that
parses fine is a STALE annotation and fails the gate.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from doc_annotations import (
    run_parse_only_gate,
)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    return run_parse_only_gate(
        root / "DE_BRUIJN.md",
        "DE_BRUIJN.md",
        parse_label="<de-bruijn>",
        hint_category="SNIPPET",
    )


if __name__ == "__main__":
    sys.exit(main())
