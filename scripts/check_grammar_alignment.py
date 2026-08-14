#!/usr/bin/env python3
"""Fail when ``spec/10-grammar.md`` and ``vera/grammar.lark`` stop describing
the same language: a rule name, a terminal, or a production body on one side
only.

Background (#683): ``spec/10-grammar.md`` and ``vera/grammar.lark`` describe one
language, and nothing held their rule names together.  They drifted — the spec
called the contract-only assertion forms ``assert_stmt``/``assume_stmt`` while
the implementation had long since made them expressions
(``assert_expr``/``assume_expr``), and the Lark rules ``pure_effect``,
``effect_set`` and ``with_clause`` appeared in no EBNF block at all (the spec
inlined the first two into ``effect_row`` and omitted the third entirely, so
the ``with`` form of a handler clause was undocumented).  Neither is a compiler
bug; both mislead a reader who takes Chapter 10 as the map of the parse tree.

The first comparison is **rule headers**: a line of the form ``name:`` at the
start of a production, in either file.  That was the whole gate as #683 shipped
it, and it is not a grammar equivalence check — two files can agree on every
rule name and still accept different languages.  Three further comparisons,
added for #1290, close the classes it could not see: terminals declared against
terminals referenced, within each file and in both directions; the pattern of
every regex-bodied terminal, across the two files; and the symbols each shared
production's right-hand side refers to.  They live under their own banner
further down, with their own reasoning.  What remains uncompared is the *shape*
of a right-hand side — alternation, grouping and repetition — so two
productions naming the same symbols in a different arrangement still pass.

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
spells the same construct as the spec production.  It is worth being concrete
about the weakest two: ``tuple_literal`` and ``tuple_type`` rest on
``constructor_call`` and ``named_type``, general forms that would outlive
tuples leaving the language altogether.  For those the premise catches the
alternative being renamed or moved to another rule, and nothing more.  The body
comparison narrows that gap without closing it: a waiver naming ``lark_rule``
is read there as "Lark inlines this production into that rule", so the symbols
the spec's production refers to are checked against the ones Lark's inlining
rule refers to.

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

    A ``//`` inside a quoted literal or a ``/…/`` regex body is not a comment.
    A plain ``line.split("//")[0]`` truncated the annotation-comment terminal in
    both files mid-pattern — ``%ignore /\\/\\*…\\*\\//`` ends in ``\\//`` — which
    was harmless while only rule headers were scanned and silently wrong the
    moment terminal bodies were (#1290).
    """
    index = 0
    length = len(line)
    while index < length:
        char = line[index]
        if char == "/" and line.startswith("//", index):
            return line[:index]
        if char in '"/':
            end = _span_end(line, index, char)
            if end is not None:
                index = end
                continue
        index += 1
    return line


def _span_end(line: str, start: int, quote: str) -> int | None:
    """Index just past the literal or regex opened at ``start``, or ``None``."""
    index = start + 1
    while index < len(line):
        if line[index] == "\\":
            index += 2
            continue
        if line[index] == quote:
            return index + 1
        index += 1
    return None


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


# ---------------------------------------------------------------------------
# Terminals and production bodies (#1290)
#
# The header comparison above is blind to three drift classes, each of which
# was demonstrated on a live file: a fabricated terminal added to §10.2 (the
# header pattern requires a lowercase lead, so no terminal is seen at all); a
# rule reference restored to a right-hand side; and a production body edited on
# one side only — the class most grammar edits actually fall into.  The checks
# below close all three, and found two chapter defects beyond the two the issue
# named: `slot_ref`/`result_ref` admitting an arbitrary `type_expr` where the
# parser accepts only `UPPER_IDENT type_args?`, and a redundant `effect_list`
# alternative ambiguous with the one beside it.
# ---------------------------------------------------------------------------

# A terminal declaration at the start of a line: an uppercase name, Lark's
# optional priority suffix, a colon, a body.
_TERMINAL_DECL = re.compile(r"^([A-Z][A-Z0-9_]*)(?:\.-?\d+)?[ \t]*:[ \t]*(\S.*?)[ \t]*$")
_TERMINAL_REF = re.compile(r"\b([A-Z][A-Z0-9_]*)\b")
_IGNORE_DECL = re.compile(r"^%ignore[ \t]+(\S.*?)[ \t]*$")
_QUOTED = re.compile(r'"((?:[^"\\]|\\.)*)"')
_BARE_REGEX = re.compile(r"^/(.+)/$")
_BARE_STRING = re.compile(r'^"((?:[^"\\]|\\.)*)"$')

# The §10.2 sub-heading whose terminals the lexer throws away.  Those are the
# only spec terminals allowed to go unreferenced by any production; the group
# is located by this marker rather than by a hand-list of names, so a renamed
# heading fails the gate instead of quietly widening it.
_SKIPPED_GROUP = "skipped"


def ebnf_fence_lines(text: str) -> list[str]:
    """Every line inside a spec chapter's ```ebnf fences, fences excluded."""
    lines: list[str] = []
    in_fence = False
    for line in text.splitlines():
        if line.lstrip().startswith("```"):
            in_fence = line.lstrip().startswith("```ebnf")
            continue
        if in_fence:
            lines.append(line)
    return lines


def rule_bodies(lines: list[str]) -> dict[str, list[str]]:
    """Map each rule header to its body lines, comments and aliases removed.

    A production spans its header line and the ``| …`` continuations under it,
    exactly as ``extract_lark_aliases`` reads them.  ``-> alias`` suffixes are
    dropped: an alias names a tree node, never a symbol the production refers
    to, and leaving them in makes every aliased alternative read as a reference
    to a rule that does not exist.
    """
    bodies: dict[str, list[str]] = {}
    owner: str | None = None
    for raw in lines:
        line = strip_comment(raw)
        header = _HEADER.match(line)
        if header:
            owner = header.group(2)
            bodies.setdefault(owner, []).append(_ALIAS.sub("", line[header.end() :]))
            continue
        if owner is not None and _CONTINUATION.match(line):
            bodies[owner].append(_ALIAS.sub("", line))
            continue
        owner = None
    return bodies


def terminal_declarations(lines: list[str]) -> dict[str, str]:
    """Map each declared terminal name to its body."""
    declared: dict[str, str] = {}
    for raw in lines:
        match = _TERMINAL_DECL.match(strip_comment(raw))
        if match:
            declared[match.group(1)] = match.group(2)
    return declared


def ignore_patterns(lines: list[str]) -> list[str]:
    """Bodies of Lark's ``%ignore`` directives — anonymous terminals."""
    return [
        match.group(1)
        for match in (_IGNORE_DECL.match(strip_comment(raw)) for raw in lines)
        if match
    ]


def skipped_terminals(lines: list[str]) -> set[str]:
    """Spec terminals declared under the ``(skipped)`` group heading.

    A *group* heading is a comment that opens a block — the first line of a
    fence, or one following a blank line.  A comment sitting between two
    declarations is a note about the one below it, not a new group; reading
    every comment as a heading ended the skipped group at the first such note
    and reported two terminals the lexer discards as unused.
    """
    names: set[str] = set()
    in_group = False
    at_block_start = True
    for raw in lines:
        stripped = raw.strip()
        if not stripped:
            at_block_start = True
            continue
        if stripped.startswith("//"):
            if at_block_start:
                in_group = _SKIPPED_GROUP in stripped.lower()
                at_block_start = False
            continue
        at_block_start = False
        match = _TERMINAL_DECL.match(strip_comment(raw))
        if match and in_group:
            names.add(match.group(1))
    return names


def normalise_pattern(body: str) -> str:
    """A regex body with Lark's delimiter and quote escapes removed.

    ``\\/`` and ``\\"`` mean exactly ``/`` and ``"`` to a regex engine; the two
    files escape them differently and nothing else, so this is the whole of the
    difference between ``STRING_LIT`` and ``ANNOTATION_COMMENT`` as the two
    files spell them.  ``\\\\`` is copied through, so an escaped backslash is
    never mistaken for an escape of the character after it.
    """
    out: list[str] = []
    index = 0
    while index < len(body):
        if body[index] == "\\" and index + 1 < len(body):
            following = body[index + 1]
            out.append(following if following in '/"' else body[index : index + 2])
            index += 2
            continue
        out.append(body[index])
        index += 1
    return "".join(out)


def _referenced_terminals(bodies: dict[str, list[str]]) -> set[str]:
    return {
        name
        for lines in bodies.values()
        for line in lines
        for name in _TERMINAL_REF.findall(_QUOTED.sub(" ", line))
    }


def terminal_audit(
    lark_lines: list[str], spec_lines: list[str]
) -> list[str]:
    """Declared-versus-referenced, within each file and in both directions.

    A terminal nothing refers to is dead weight the reader has to reconcile —
    ``SOME``/``NONE``/``OK``/``ERR``/``COLON`` sat in the Lark grammar that way
    while the constructors they claimed to lex went through ``UPPER_IDENT``.  A
    terminal referred to and never declared is the opposite failure and Lark
    had one of those too, ``DOUBLE_COLON`` in ``module_call``.  Neither
    direction was checked anywhere.
    """
    problems: list[str] = []
    for label, lines, allow_unreferenced in (
        (LARK, lark_lines, set[str]()),
        (SPEC, spec_lines, skipped_terminals(spec_lines)),
    ):
        declared = set(terminal_declarations(lines))
        referenced = _referenced_terminals(rule_bodies(lines))
        if label == SPEC and not allow_unreferenced:
            problems.append(
                f"{label}: no terminal group marked `({_SKIPPED_GROUP})` was "
                f"found, so every declared terminal would have to be referenced"
            )
        for name in sorted(declared - referenced - allow_unreferenced):
            problems.append(f"{label}: terminal {name} is declared and never used")
        for name in sorted(referenced - declared):
            problems.append(f"{label}: terminal {name} is used and never declared")
    return problems


def terminal_patterns(lark_lines: list[str], spec_lines: list[str]) -> list[str]:
    """Every pattern-bearing terminal must be spelled the same in both files.

    Only terminals whose body is a bare ``/regex/`` are compared: the spec
    names each keyword and punctuation mark that Lark writes as an inline
    quoted literal, and those have no Lark declaration to compare against.  The
    regex-bodied ones do, either as a named terminal or as an ``%ignore``, and
    ``BLOCK_COMMENT`` was the one that had neither — the spec published a
    non-nesting ``/\\{-[\\s\\S]*?-\\}/`` for a construct §1.3 says nests and
    ``vera/lexical.py`` resolves by counting depth.
    """
    lark_declared = terminal_declarations(lark_lines)
    spec_declared = terminal_declarations(spec_lines)
    lark_patterns = {
        normalise_pattern(match.group(1))
        for match in (
            _BARE_REGEX.match(body)
            for body in [*lark_declared.values(), *ignore_patterns(lark_lines)]
        )
        if match
    }
    problems: list[str] = []
    for name, body in sorted(spec_declared.items()):
        regex = _BARE_REGEX.match(body)
        if regex is None:
            continue
        if normalise_pattern(regex.group(1)) not in lark_patterns:
            problems.append(
                f"{SPEC}: terminal {name} publishes a pattern {LARK} does not "
                f"have, as a terminal or an %ignore: {body}"
            )
    for name, body in sorted(lark_declared.items()):
        if name not in spec_declared:
            problems.append(f"{SPEC}: terminal {name} is declared only in {LARK}")
        elif normalise_pattern(body) != normalise_pattern(spec_declared[name]):
            problems.append(
                f"{name}: {LARK} has {body}, {SPEC} has {spec_declared[name]}"
            )
    return problems


def _literal_terminals(spec_lines: list[str]) -> tuple[dict[str, str], list[str]]:
    """Map each quoted literal the spec names to its terminal, plus clashes."""
    table: dict[str, str] = {}
    clashes: list[str] = []
    for name, body in sorted(terminal_declarations(spec_lines).items()):
        match = _BARE_STRING.match(body)
        if match is None:
            continue
        literal = match.group(1)
        if literal in table:
            clashes.append(
                f"{SPEC}: terminals {table[literal]} and {name} both spell {body}"
            )
            continue
        table[literal] = name
    return table, clashes


def _symbols(line: str, rules: set[str]) -> tuple[set[str], set[str]]:
    """``(rule references, terminal references)`` in one production body line."""
    return (
        {name for name in re.findall(r"\b[a-z][a-z0-9_]*\b", line)} & rules,
        set(_TERMINAL_REF.findall(_QUOTED.sub(" ", line))),
    )


def _lark_symbols(
    rule: str,
    bodies: dict[str, list[str]],
    rules: set[str],
    literals: dict[str, str],
) -> tuple[set[str], set[str], list[str]]:
    referenced: set[str] = set()
    terminals: set[str] = set()
    unmapped: list[str] = []
    for line in bodies[rule]:
        rule_refs, terminal_refs = _symbols(line, rules)
        referenced |= rule_refs
        terminals |= terminal_refs
        for raw in _QUOTED.findall(line):
            literal = raw.replace('\\"', '"')
            if literal in literals:
                terminals.add(literals[literal])
            else:
                unmapped.append(literal)
    return referenced - {rule}, terminals, unmapped


def _spec_symbols(
    rule: str, bodies: dict[str, list[str]], rules: set[str]
) -> tuple[set[str], set[str], set[str]]:
    """``(rules, terminals, inlined)`` for one spec production.

    A waiver saying "Lark expresses this as an alternative of ``lark_rule``"
    fixes where the spec's separate production corresponds on the Lark side:
    seen from any other rule it *is* ``lark_rule``, and seen from ``lark_rule``
    itself its body is inlined there.  Reading the waiver that way is what lets
    the body comparison run against the shipped files with no waivers of its
    own.

    ``inlined`` names the symbols that arrived by that folding rather than from
    the production's own text.  Inlining moves a symbol across a rule boundary
    and a one-level set comparison cannot say how far it moved — the spec's
    ``tuple_type`` contributes ``LT``/``COMMA``/``GT`` that Lark keeps one rule
    deeper, inside ``type_args`` — so a folded symbol missing on the Lark side
    is not reported.  The other direction still is: a symbol Lark refers to and
    the chapter does not is drift however the waiver reads.
    """
    waived = {name for name, entry in ALLOWLIST.items() if entry.side == "spec"}
    referenced: set[str] = set()
    terminals: set[str] = set()
    for line in bodies[rule]:
        rule_refs, terminal_refs = _symbols(line, rules)
        referenced |= rule_refs
        terminals |= terminal_refs
    folded: set[str] = set()
    inlined: set[str] = set()
    for name in sorted(referenced):
        waiver = ALLOWLIST.get(name) if name in waived else None
        if waiver is None:
            folded.add(name)
        elif waiver.lark_rule is None:
            continue
        elif waiver.lark_rule != rule:
            folded.add(waiver.lark_rule)
        elif name in bodies:
            inner_rules, inner_terminals, _ = _spec_symbols(name, bodies, rules)
            folded |= inner_rules
            terminals |= inner_terminals
            inlined |= inner_rules | inner_terminals
    return (folded - waived) - {rule}, terminals, inlined


def body_drift(lark_lines: list[str], spec_lines: list[str]) -> list[str]:
    """Compare the symbols each shared production refers to.

    Rule references and terminal references, per production, for every rule
    both files declare.  A rule's reference to *itself* is excluded: Lark
    spells repetition with left recursion and the chapter spells it with a
    Kleene star, so the eight operator-precedence rules differ there by
    notation and not by language.
    """
    lark_bodies = rule_bodies(lark_lines)
    spec_bodies = rule_bodies(spec_lines)
    literals, problems = _literal_terminals(spec_lines)
    waived = {name for name, entry in ALLOWLIST.items() if entry.side == "spec"}
    shared = sorted(set(lark_bodies) & set(spec_bodies))
    if not shared:
        return [*problems, "no rule is a production in both files"]
    for rule in shared:
        lark_rules, lark_terms, unmapped = _lark_symbols(
            rule, lark_bodies, set(lark_bodies), literals
        )
        spec_rules, spec_terms, inlined = _spec_symbols(
            rule, spec_bodies, set(spec_bodies)
        )
        for literal in sorted(set(unmapped)):
            problems.append(
                f'{rule}: {LARK} matches the literal "{literal}" and no {SPEC} '
                f"terminal declares it"
            )
        for label, only_lark, only_spec in (
            (
                "rule",
                lark_rules - waived - spec_rules,
                spec_rules - lark_rules - inlined,
            ),
            ("terminal", lark_terms - spec_terms, spec_terms - lark_terms - inlined),
        ):
            for name in sorted(only_lark):
                problems.append(f"{rule}: refers to {label} {name} only in {LARK}")
            for name in sorted(only_spec):
                problems.append(f"{rule}: refers to {label} {name} only in {SPEC}")
    return problems


def _report(title: str, problems: list[str], remedy: str) -> None:
    print(f"\nERROR: {title}:", file=sys.stderr)
    for problem in problems:
        print(f"  {problem}", file=sys.stderr)
    print(f"\n{remedy}", file=sys.stderr)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    lark = extract_lark_rules(root / LARK)
    spec = extract_spec_rules(root / SPEC)

    lark_text = (root / LARK).read_text(encoding="utf-8")
    lark_lines = lark_text.splitlines()
    spec_lines = ebnf_fence_lines((root / SPEC).read_text(encoding="utf-8"))

    differing = lark ^ spec
    actionable, stale, unsound = drift(lark, spec, lark_text)
    unused = terminal_audit(lark_lines, spec_lines)
    patterns = terminal_patterns(lark_lines, spec_lines)
    bodies = body_drift(lark_lines, spec_lines)

    print(f"  {len(lark)} rule headers in {LARK}")
    print(f"  {len(spec)} rule headers in {SPEC}")
    print(f"  {len(differing)} differ, {len(ALLOWLIST)} allowlisted")
    print(
        f"  {len(terminal_declarations(lark_lines))} terminals in {LARK}, "
        f"{len(terminal_declarations(spec_lines))} in {SPEC}"
    )
    print(
        f"  {len(set(rule_bodies(lark_lines)) & set(rule_bodies(spec_lines)))} "
        f"production bodies compared"
    )

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
    if unused:
        _report(
            "terminals declared without a use, or used without a declaration",
            unused,
            "Delete the terminal, or add the production that refers to it. A "
            "terminal nothing refers to is not part of the language.",
        )
    if patterns:
        _report(
            "terminal patterns differ between the two files",
            patterns,
            f"Make {SPEC} publish the pattern the parser actually has. Where a "
            f"construct is not regular — nested block comments are the standing "
            f"case — say so in the chapter rather than publishing a regex that "
            f"accepts a different language.",
        )
    if bodies:
        _report(
            "production bodies refer to different symbols",
            bodies,
            f"Bring the two right-hand sides together. If {SPEC} is the one "
            f"that is wrong, fix the chapter: it is read as the map of the "
            f"parse tree.",
        )
    if actionable or stale or unsound or unused or patterns or bodies:
        return 1

    print(f"OK: {LARK} and {SPEC} agree on every rule name, terminal and body.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
