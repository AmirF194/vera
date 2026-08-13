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

The two compared *sets* are deliberately blind to Lark's ``-> alias`` names.  An
alias renames the tree node an alternative produces; it is not a rule header,
and the same name can be an ordinary header in the spec.  Collecting aliases
into the sets makes the two sides formally incomparable — most of Lark's ~46
aliases label inline alternatives the spec has no separate production for — so
the symmetric difference fills with noise and the allowlist has to absorb it.
Four of the six allowlisted names below are exactly this case, held by name
instead.  Aliases are read for one narrower purpose only: checking that a
waiver's stated reason still holds, below.

It also normalises away Lark's leading-underscore marker, so a Lark ``_foo``
and a spec ``foo`` count as agreeing.  No ``_``-prefixed rule exists in the
grammar today, so nothing reaches that branch — but the property the marker
carries, an inlined rule contributing no tree node of its own, is not a latent
worry here.  It is already true of every one of the sixteen ``?``-prefixed
rules: none can appear as a node under its own name, because each alternative is
either a single symbol (so Lark inlines it) or carries a ``-> alias`` that
renames it — ``?effect_row`` and ``?handler_body`` are the plainest cases, with
no alias anywhere.  The gate matches all sixteen by name, silently, and that is
the intended behaviour: Chapter 10 documents the productions a reader derives
with, not the node set the parser happens to build.  A side-aware rule that made
``_foo`` special would have to make those sixteen special too.

``ALLOWLIST`` names the pairs that are known, intentional, and not drift.  Each
entry records the *side* its name lives on and, where the reason rests on a Lark
``-> alias``, both that alias and the production it must be an alternative of.
Those two facts are checked rather than asserted, against comment-stripped text
so a ``-> name`` surviving in ``//`` prose cannot hold a waiver up.  That makes
three distinct failures distinguishable: the name now appears on both sides (the
waiver is spent, delete it), the name vanished from the side it was expected on
or its alternative is gone from the rule named (the waiver's premise broke,
restore the production), and unwaived drift.  Each name yields at most one of
them, so the report never asks for two opposite edits at once.

What the alias premise does *not* establish is that the Lark alternative still
spells the same construct as the spec production — that is a body-level fact
this header-only gate cannot see.  It is worth being concrete about the weakest
two: ``tuple_literal`` and ``tuple_type`` rest on ``constructor_call`` and
``named_type``, general forms that would outlive tuples leaving the language
altogether.  For those the premise catches the alternative being renamed or
moved to another rule, and nothing more.

The allowlist is meant to stay small.  If it needs to grow past a handful of
entries, the header-only comparison has stopped being the right model and should
be rethought, not padded.
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

# An `-> alias` at the end of a Lark alternative.  Lark's own `"->"` string
# literal is always quoted, so the `[a-z]` after the arrow cannot match it.
_ALIAS = re.compile(r"->[ \t]*([a-z][a-z0-9_]*)")

# A continuation of the production above: Lark spells further alternatives `| …`.
_CONTINUATION = re.compile(r"^[ \t]*\|")


class Waiver(NamedTuple):
    """Why one name is allowed to appear on a single side only."""

    side: str  # "lark" or "spec" — the file this name is a rule header in
    reason: str
    # The `-> alias` the reason rests on, and the rule it must be an
    # alternative of.  Set both or neither: an alias with no rule matches
    # nothing, which fails the gate loudly rather than waiving silently.
    lark_rule: str | None = None
    lark_alias: str | None = None


def strip_comment(line: str) -> str:
    """One line of Lark or EBNF with any ``//`` comment removed.

    The single definition of what a comment is, shared by every scan of either
    file — a rule header, an alias, or anything added later.  Commented-out
    grammar is deleted grammar; it must not satisfy a check.
    """
    return line.split("//")[0]


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
        lark_rule="fn_call",
        lark_alias="qualified_call",
    ),
    "module_call": Waiver(
        "spec",
        "spec header; Lark expresses it as the `-> module_call` alias on `fn_call`.",
        lark_rule="fn_call",
        lark_alias="module_call",
    ),
    "tuple_literal": Waiver(
        "spec",
        "spec header; Lark folds it into `fn_call`'s `-> constructor_call` "
        "alternative. What is checked is that `fn_call` still carries that "
        "alternative — `constructor_call` is the general constructor form and "
        "would outlive tuples leaving the language, so nothing here ties it to "
        "tuples. That the two bodies still describe one construct is a "
        "body-level fact this header-only gate cannot see.",
        lark_rule="fn_call",
        lark_alias="constructor_call",
    ),
    "tuple_type": Waiver(
        "spec",
        "spec header; Lark folds it into `type_expr`'s `-> named_type` "
        "alternative. What is checked is that `type_expr` still carries that "
        "alternative — `named_type` is the general named-type form and would "
        "outlive tuples leaving the language, so nothing here ties it to "
        "tuples. That the two bodies still describe one construct is a "
        "body-level fact this header-only gate cannot see.",
        lark_rule="type_expr",
        lark_alias="named_type",
    ),
}


def extract_lark_rules(path: Path) -> set[str]:
    """Rule-header names in a Lark grammar (aliases and terminals excluded)."""
    names = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = _HEADER.match(strip_comment(line))
        if match:
            names.add(match.group(2))
    return names


def extract_lark_aliases(text: str) -> set[tuple[str, str]]:
    """``(rule, alias)`` for every ``-> alias`` in a Lark grammar.

    An alias belongs to the production it is an alternative *of*, which in Lark
    spans a header line and the ``| …`` continuations under it.  Attributing it
    that way is what makes a waiver's premise fail when the alternative moves to
    another rule; a bare file-wide search for the alias name would not notice.
    """
    pairs: set[tuple[str, str]] = set()
    owner: str | None = None
    for raw in text.splitlines():
        line = strip_comment(raw)
        header = _HEADER.match(line)
        if header:
            owner = header.group(2)
        elif not _CONTINUATION.match(line):
            # Neither a header nor another alternative: whatever production was
            # open has ended (a blank line, a terminal, a `%` directive).
            owner = None
        if owner is not None:
            pairs.update((owner, alias) for alias in _ALIAS.findall(line))
    return pairs


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
        match = _HEADER.match(strip_comment(line))
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
    the name is gone from the side it was expected on, or the alternative the
    reason rests on is gone from the rule it names.  Kept apart from ``stale``
    because the fix is the opposite one — restore the production, not delete the
    waiver.  Reporting "the sides now agree" here would point the reader at the
    deletion that makes the gate green with the construct documented nowhere.

    A name lands in at most one bucket.  Two reports for one name are two
    instructions, and the pair that used to fire together — "the waiver is
    spent, delete it" and "its premise broke, restore what it names" — cannot
    both be the next edit.
    """
    actionable = sorted((lark ^ spec) - set(ALLOWLIST))
    stale: list[str] = []
    unsound: list[tuple[str, str]] = []
    aliases = extract_lark_aliases(lark_text)
    for name, waiver in sorted(ALLOWLIST.items()):
        own, other = (lark, spec) if waiver.side == "lark" else (spec, lark)
        other_file = SPEC if waiver.side == "lark" else LARK
        if name not in own:
            found = f"only in {other_file}" if name in other else "in neither file"
            problem = f"expected a rule header in the {waiver.side} file, found {found}"
            unsound.append((name, problem))
        elif name in other:
            stale.append(name)
        elif waiver.lark_alias and (waiver.lark_rule, waiver.lark_alias) not in aliases:
            unsound.append(
                (
                    name,
                    f"no `-> {waiver.lark_alias}` alternative on "
                    f"`{waiver.lark_rule}` left in {LARK}",
                )
            )
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
