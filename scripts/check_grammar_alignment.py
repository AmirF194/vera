#!/usr/bin/env python3
"""Fail if a grammar rule name exists in the spec EBNF but not in the Lark
grammar, or the other way round.

Background (#683): ``spec/10-grammar.md`` and ``vera/grammar.lark`` describe one
language, and nothing held their rule names together.  They drifted — the spec
called the contract-only assertion forms ``assert_stmt``/``assume_stmt`` while
the implementation had long since made them expressions
(``assert_expr``/``assume_expr``), and the Lark rules ``pure_effect``,
``effect_set`` and ``with_clause`` appeared in no EBNF block at all (the spec
inlined the first two into ``effect_row`` and omitted the third entirely, so
the ``with`` form of a handler clause was undocumented).  Neither is a compiler
bug; both mislead a reader who takes Chapter 10 as the map of the parse tree.

What this compares is **rule headers only**: a line of the form ``name:`` at the
start of a production, in either file.  It is a name-level cross-check, not a
grammar equivalence check — two files can agree on every rule name and still
accept different languages.  Rule *bodies* are not compared, so a drifted
right-hand side passes here.

It is deliberately blind to Lark's ``-> alias`` names.  An alias renames the
tree node an alternative produces; it is not a rule header, and the same name
can be an ordinary header in the spec.  Collecting aliases makes the two sides
formally incomparable — most of Lark's ~46 aliases label inline alternatives the
spec has no separate production for — so the symmetric difference fills with
noise and the allowlist has to absorb it.  Four of the six allowlisted names
below are exactly this case, held by name instead.

It also normalises away Lark's leading-underscore marker, so a Lark ``_foo``
and a spec ``foo`` count as agreeing.  Strictly they do not: ``_foo`` is inlined
and produces no tree node, which is the very thing Chapter 10 is supposed to
map.  No ``_``-prefixed rule exists in the grammar today, so this is latent; it
would need a side-aware rule (spec header, no Lark node) rather than a silent
match if one is ever added.

``ALLOWLIST`` names the pairs that are known, intentional, and not drift.  Each
entry records the *side* its name lives on and, where the reason rests on a Lark
``-> alias``, the alias itself — so the stated reason is checked, not merely
asserted.  That makes three distinct failures distinguishable: the name now
appears on both sides (the waiver is spent, delete it), the name vanished from
the side it was expected on or its alias is gone (the waiver's premise broke,
restore the production), and unwaived drift.  The allowlist is meant to stay
small.  If it needs to grow past a handful of entries, the header-only
comparison has stopped being the right model and should be rethought, not
padded.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import NamedTuple

LARK = "vera/grammar.lark"
SPEC = "spec/10-grammar.md"

# Rule-header line: optional Lark inline/keep markers, a lowercase name, its
# optional template parameters (`{a, b}`) and priority (`.2`) in Lark's order, a
# colon.  Missing either suffix drops the rule from the Lark set entirely — it
# then escapes the gate, or gets reported as spec-only drift the reader is told
# to fix by adding a production the file already has.
# The (?!:) guards Lark's "::" string literal in `module_path`.
_HEADER = re.compile(r"^[?!]?(_?)([a-z][a-z0-9_]*)(?:\{[^}]*\})?(?:\.\d+)?[ \t]*:(?!:)")


class Waiver(NamedTuple):
    """Why one name is allowed to appear on a single side only."""

    side: str  # "lark" or "spec" — the file this name is a rule header in
    reason: str
    lark_alias: str | None = None  # the `-> alias` the reason rests on


# Names that appear on one side only, on purpose.  Not drift; do not "fix".
ALLOWLIST = {
    "start": Waiver(
        "lark", "Lark's entry point; the spec calls the same production `program`."
    ),
    "program": Waiver(
        "spec", "the spec's entry point; Lark calls the same production `start`."
    ),
    "qualified_call": Waiver(
        "spec",
        "spec header; Lark expresses it as the `-> qualified_call` alias on `fn_call`.",
        "qualified_call",
    ),
    "module_call": Waiver(
        "spec",
        "spec header; Lark expresses it as the `-> module_call` alias on `fn_call`.",
        "module_call",
    ),
    "tuple_literal": Waiver(
        "spec",
        "spec header; Lark folds it into `fn_call`'s `-> constructor_call` "
        "alternative. Only the alias's existence is checked — that the two "
        "bodies still describe the same construct is a body-level fact this "
        "header-only gate cannot see.",
        "constructor_call",
    ),
    "tuple_type": Waiver(
        "spec",
        "spec header; Lark folds it into `type_expr`'s `-> named_type` "
        "alternative. Only the alias's existence is checked — that the two "
        "bodies still describe the same construct is a body-level fact this "
        "header-only gate cannot see.",
        "named_type",
    ),
}


def extract_lark_rules(path: Path) -> set[str]:
    """Rule-header names in a Lark grammar (aliases and terminals excluded)."""
    names = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = _HEADER.match(line.split("//")[0])
        if match:
            names.add(match.group(2))
    return names


def extract_spec_rules(path: Path) -> set[str]:
    """Rule-header names inside the ```ebnf fences of a spec chapter."""
    names = set()
    in_fence = False
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.lstrip().startswith("```"):
            in_fence = line.lstrip().startswith("```ebnf")
            continue
        if not in_fence:
            continue
        match = _HEADER.match(line.split("//")[0])
        if match:
            names.add(match.group(2))
    return names


def drift(
    lark: set[str], spec: set[str], lark_text: str
) -> tuple[list[str], list[str], list[tuple[str, str]]]:
    """``(actionable, stale, unsound)``.

    ``actionable`` — names on one side only that no waiver covers: real drift.

    ``stale`` — waived names that now appear on both sides, so the waiver is
    spent and should be deleted.

    ``unsound`` — ``(name, problem)`` for waivers whose premise stopped holding:
    the name is gone from the side it was expected on, or the Lark alias the
    reason rests on is gone.  Kept apart from ``stale`` because the fix is the
    opposite one — restore the production, not delete the waiver.  Reporting
    "the sides now agree" here would point the reader at the deletion that makes
    the gate green with the construct documented nowhere.
    """
    actionable = sorted((lark ^ spec) - set(ALLOWLIST))
    stale: list[str] = []
    unsound: list[tuple[str, str]] = []
    for name, waiver in sorted(ALLOWLIST.items()):
        own, other = (lark, spec) if waiver.side == "lark" else (spec, lark)
        other_file = SPEC if waiver.side == "lark" else LARK
        if name not in own:
            found = f"only in {other_file}" if name in other else "in neither file"
            problem = f"expected a rule header in the {waiver.side} file, found {found}"
            unsound.append((name, problem))
        elif name in other:
            stale.append(name)
        if waiver.lark_alias and not re.search(
            rf"->\s*{re.escape(waiver.lark_alias)}\b", lark_text
        ):
            unsound.append((name, f"no `-> {waiver.lark_alias}` alias left in {LARK}"))
    return actionable, stale, unsound


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    lark = extract_lark_rules(root / LARK)
    spec = extract_spec_rules(root / SPEC)

    differing = lark ^ spec
    actionable, stale, unsound = drift(
        lark, spec, (root / LARK).read_text(encoding="utf-8")
    )

    print(f"  {len(lark)} rule headers in {LARK}")
    print(f"  {len(spec)} rule headers in {SPEC}")
    print(f"  {len(differing)} differ, {len(ALLOWLIST)} allowlisted")

    if actionable:
        print("\nERROR: grammar rule names have drifted:", file=sys.stderr)
        for name in actionable:
            side = LARK if name in lark else SPEC
            print(f"  {name} — only in {side}", file=sys.stderr)
        print(
            f"\nRename the rule so both files agree, or add the missing "
            f"production. If the two sides deliberately use different names "
            f"for the same construct, add it to ALLOWLIST in {Path(__file__).name} "
            f"with the reason.",
            file=sys.stderr,
        )
    if stale:
        print(
            "\nERROR: spent ALLOWLIST entries (both files now have them):",
            file=sys.stderr,
        )
        for name in stale:
            print(f"  {name} — {ALLOWLIST[name].reason}", file=sys.stderr)
        print(
            f"\nRemove them from ALLOWLIST in {Path(__file__).name}.",
            file=sys.stderr,
        )
    if unsound:
        print(
            "\nERROR: ALLOWLIST entries whose premise no longer holds:",
            file=sys.stderr,
        )
        for name, problem in unsound:
            print(f"  {name} — {problem}", file=sys.stderr)
            print(f"    waiver: {ALLOWLIST[name].reason}", file=sys.stderr)
        print(
            "\nThe entry waives a difference on the strength of a fact that has "
            "since changed. Restore the production or alias it names, or — if the "
            "construct is genuinely gone from the language — remove it from both "
            "files and delete the entry.",
            file=sys.stderr,
        )
    if actionable or stale or unsound:
        return 1

    print(f"OK: {LARK} and {SPEC} agree on every rule name.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
