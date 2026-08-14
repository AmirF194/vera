"""Tests for the grammar rule-name drift gate (scripts/check_grammar_alignment.py).

The gate (#683) compares the rule headers of ``spec/10-grammar.md`` against
those of ``vera/grammar.lark``.  These tests pin the two extractors, the
allowlist arithmetic, and the one false positive the issue itself was built on:
``qualified_call`` and ``module_call`` are *not* drift, and the gate must never
report them.
"""

from __future__ import annotations

import importlib.util
import re
from pathlib import Path
from typing import Any

import pytest

_ROOT = Path(__file__).parent.parent
_SCRIPT = _ROOT / "scripts" / "check_grammar_alignment.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_grammar_alignment", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


def _lark_text() -> str:
    return (_ROOT / _MOD.LARK).read_text(encoding="utf-8")


def _repo_rules() -> tuple[set[str], set[str]]:
    return (
        _MOD.extract_lark_rules(_ROOT / _MOD.LARK),
        _MOD.extract_spec_rules(_ROOT / _MOD.SPEC),
    )


def test_shipped_grammars_agree() -> None:
    assert _MOD.main() == 0


def test_allowlist_stays_small() -> None:
    """Past a handful of entries the header-only comparison is the wrong model.

    The bound sits one above the six entries reviewed, so a seventh is a
    deliberate act with a reason attached and an eighth cannot be added without
    arguing here first.  A bound with room to spare is not a bound.
    """
    assert len(_MOD.ALLOWLIST) <= 7


def test_qualified_and_module_call_are_never_reported() -> None:
    """#683's premise was that these two names had drifted. They had not.

    Both are spec rule headers that Lark expresses as ``-> alias`` names on
    ``fn_call``, and they name two different constructs (``Effect.op()`` versus
    ``mod::fn()``), so "aligning" them would merge two rules into one.  The
    allowlist holds them, and they must stay out of every failure bucket.
    """
    lark, spec = _repo_rules()
    names = {"qualified_call", "module_call"}
    assert names <= set(_MOD.ALLOWLIST)
    assert names <= spec, "both are spec rule headers"
    assert not names & lark, "neither is a Lark rule header — they are aliases"
    actionable, stale, unsound = _MOD.drift(lark, spec, _lark_text())
    assert not names & set(actionable)
    assert not names & set(stale)
    assert not names & {name for name, _ in unsound}


@pytest.mark.parametrize("name", sorted(_MOD.ALLOWLIST))
def test_every_waivers_premise_is_checked(name: str) -> None:
    """A waiver must fail when the fact it rests on stops being true.

    Four entries are held by "Lark has it as a ``-> alias``" and two by "the
    other file calls the same production X".  Both claims were previously only
    asserted in prose: deleting the alias, or the production, left the gate green
    forever.
    """
    lark, spec = _repo_rules()
    waiver = _MOD.ALLOWLIST[name]

    # Removing the name from the side the waiver puts it on must fail.
    own_lark = lark - {name} if waiver.side == "lark" else lark
    own_spec = spec - {name} if waiver.side == "spec" else spec
    _, _, unsound = _MOD.drift(own_lark, own_spec, _lark_text())
    assert name in {n for n, _ in unsound}

    if waiver.lark_alias is None:
        # start/program are plain headers on their own side; there is no alias
        # claim left to check once the side check above holds.
        assert waiver.lark_rule is None, "an alias and its rule are set together"
        return
    assert waiver.lark_rule is not None, "an alias and its rule are set together"
    # Deleting the alternative the reason names must fail too.
    stripped = _lark_text().replace(f"-> {waiver.lark_alias}", "")
    _, _, unsound = _MOD.drift(lark, spec, stripped)
    expected = (
        f"no `-> {waiver.lark_alias}` alternative on "
        f"`{waiver.lark_rule}` left in {_MOD.LARK}"
    )
    assert (name, expected) in unsound


def test_an_alias_named_only_in_a_comment_does_not_hold_a_waiver_up() -> None:
    """A commented-out production must not keep its waiver's premise alive.

    Commenting a production out deletes it; the ``-> alias`` left behind in the
    comment text is prose.  Searching the raw file for the alias let that prose
    hold the waiver up, so deleting the alternative the waiver rests on kept the
    gate green — the exact failure the premise check exists to catch.
    """
    holed = re.sub(r"^(.*-> qualified_call.*)$", r"// \1", _lark_text(), flags=re.M)
    assert "-> qualified_call" in holed, "the comment still names the alias"

    lark, spec = _repo_rules()
    _, _, unsound = _MOD.drift(lark, spec, holed)
    problems = {name: problem for name, problem in unsound}
    assert "qualified_call" in problems
    assert "qualified_call" in problems["qualified_call"]


def test_a_waived_alias_must_sit_on_the_production_its_reason_names() -> None:
    """The premise is "``fn_call`` has this alternative", not "the file does".

    ``constructor_call`` and ``named_type`` are generic aliases; searching the
    whole file for the bare name is satisfied by any occurrence anywhere, so a
    waiver reading "Lark folds it into ``fn_call``'s alternative" survived that
    alternative moving to another rule entirely.
    """
    moved = re.sub(r"[ \t]*-> constructor_call[ \t]*$", "", _lark_text(), flags=re.M)
    moved += '\ndecoy: UPPER_IDENT "(" arg_list? ")" -> constructor_call\n'
    assert "-> constructor_call" in moved, "the alias still exists, on another rule"

    lark, spec = _repo_rules()
    _, _, unsound = _MOD.drift(lark, spec, moved)
    problems = {name: problem for name, problem in unsound}
    assert "tuple_literal" in problems
    assert "constructor_call" in problems["tuple_literal"]
    assert "fn_call" in problems["tuple_literal"], "names the production it left"


def test_one_broken_waiver_yields_one_instruction() -> None:
    """Two buckets firing for one name gave two contradictory instructions.

    A spent waiver whose alias is also gone was reported both as "both files now
    have it, delete the entry" and as "the premise broke, restore what it names".
    Only one of those can be the next edit.
    """
    stripped = re.sub(r"[ \t]*-> qualified_call[ \t]*$", "", _lark_text(), flags=re.M)
    assert "-> qualified_call" not in stripped

    lark, spec = _repo_rules()
    actionable, stale, unsound = _MOD.drift(lark | {"qualified_call"}, spec, stripped)
    reported = (
        [n for n in actionable if n == "qualified_call"]
        + [n for n in stale if n == "qualified_call"]
        + [n for n, _ in unsound if n == "qualified_call"]
    )
    assert reported == ["qualified_call"]
    assert stale == ["qualified_call"], "the waiver is spent; deleting it is the fix"


def test_a_name_deleted_from_both_files_is_not_reported_as_agreement() -> None:
    """Deleting a waived spec production is a doc regression, not a fix.

    ``lark ^ spec`` drops such a name for the same reason it drops one both files
    have, so a side-blind gate reported it as "the sides now agree — remove the
    ALLOWLIST entry", i.e. it directed the maintainer at the edit that makes the
    gate green with the construct documented nowhere.
    """
    lark, spec = _repo_rules()
    actionable, stale, unsound = _MOD.drift(
        lark, spec - {"qualified_call"}, _lark_text()
    )
    assert actionable == []
    assert stale == [], "not agreement — the name is gone from both files"
    assert unsound == [
        (
            "qualified_call",
            "expected a rule header in the spec file, found in neither file",
        )
    ]


def test_the_drift_the_gate_was_built_for_is_detectable() -> None:
    """Restoring the spec's old ``assert_stmt`` name must turn the gate red.

    Without this the suite cannot distinguish "the names agree" from "the
    extractor found nothing".
    """
    lark, spec = _repo_rules()
    mutated = (spec - {"assert_expr"}) | {"assert_stmt"}
    actionable, stale, unsound = _MOD.drift(lark, mutated, _lark_text())
    assert actionable == ["assert_expr", "assert_stmt"]
    assert not stale
    assert not unsound


def test_extractors_are_not_vacuous() -> None:
    lark, spec = _repo_rules()
    # The three rules this PR added to the spec, and a rule shared all along.
    assert {"pure_effect", "effect_set", "with_clause", "handler_clause"} <= lark & spec
    assert len(lark) > 50 and len(spec) > 50


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        ("fn_call: LOWER_IDENT", {"fn_call"}),
        # Lark's inline (?) and keep-tree (!) markers are not part of the name.
        ("?effect_row: pure_effect", {"effect_row"}),
        ("!literal: INT", {"literal"}),
        # A leading underscore only means "inline me"; same rule.
        ("_seperated: item", {"seperated"}),
        # Lark rule priority and template parameters sit between name and colon.
        # Missing them let a rule escape the gate, or be reported as spec-only
        # drift against a Lark file that already had it.
        ("expr.2: term", {"expr"}),
        ("?expr.10: term", {"expr"}),
        ("_sep{item, sepchar}: item (sepchar item)*", {"sep"}),
        ("sep{item}.2: item", {"sep"}),
        # `-> alias` names are deliberately not collected.
        ('fn_call: UPPER_IDENT "." LOWER_IDENT -> qualified_call', {"fn_call"}),
        ("       | module_path -> module_call", set()),
        # Terminals are upper-case and out of scope.
        ("LOWER_IDENT: /[a-z]\\w*/", set()),
        # Directives, comments, continuations and blanks contribute nothing.
        ("%ignore WS", set()),
        ("// assert_stmt: gone", set()),
        ("         | assert_expr", set()),
        ("", set()),
        # The "::" of `module_path` is a literal, not a rule header colon.
        ('module_call: module_path "::" LOWER_IDENT', {"module_call"}),
    ],
)
def test_extract_lark_rules(text: str, expected: set[str], tmp_path: Path) -> None:
    path = tmp_path / "g.lark"
    path.write_text(text, encoding="utf-8")
    assert _MOD.extract_lark_rules(path) == expected


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        ("```ebnf\nfn_call: LOWER_IDENT\n```", {"fn_call"}),
        # Only ebnf fences count — Vera samples are full of `name:` lookalikes.
        ("```vera\nfn_call: LOWER_IDENT\n```", set()),
        ("```\nfn_call: LOWER_IDENT\n```", set()),
        # Prose outside any fence is not grammar.
        ("The rule fn_call: is described below.", set()),
        # A fence must close before the next block starts.
        ("```ebnf\na: X\n```\n```vera\nb: Y\n```\n```ebnf\nc: Z\n```", {"a", "c"}),
        ('```ebnf\nASSERT: "assert"\n```', set()),
        ("```ebnf\n// assert_stmt: gone\n```", set()),
    ],
)
def test_extract_spec_rules(text: str, expected: set[str], tmp_path: Path) -> None:
    path = tmp_path / "s.md"
    path.write_text(text, encoding="utf-8")
    assert _MOD.extract_spec_rules(path) == expected


@pytest.mark.parametrize(
    ("extra_lark", "extra_spec", "actionable"),
    [
        # Agreement.
        (set(), set(), []),
        # Drift in either direction is reported, and names the side it is on.
        ({"assert_expr"}, set(), ["assert_expr"]),
        (set(), {"assert_stmt"}, ["assert_stmt"]),
        # Both halves of a rename show up, sorted.
        ({"assert_expr"}, {"assert_stmt"}, ["assert_expr", "assert_stmt"]),
        # An allowlisted name is skipped even when it differs.
        ({"start"}, {"program"}, []),
    ],
)
def test_drift_actionable(
    extra_lark: set[str], extra_spec: set[str], actionable: list[str]
) -> None:
    """Start from a state where the allowlist is satisfied, then perturb it."""
    base_lark = {"shared", "start"}
    base_spec = {"shared", "program", "qualified_call", "module_call"}
    base_spec |= {"tuple_literal", "tuple_type"}
    assert _MOD.drift(base_lark, base_spec, _lark_text()) == ([], [], [])

    got_actionable, got_stale, got_unsound = _MOD.drift(
        base_lark | extra_lark, base_spec | extra_spec, _lark_text()
    )
    assert got_actionable == actionable
    assert got_stale == []
    assert got_unsound == []


def test_drift_reports_a_rotted_allowlist_entry() -> None:
    """An entry that stops differing must fail, not linger."""
    lark, spec = _repo_rules()
    actionable, stale, unsound = _MOD.drift(lark | {"program"}, spec, _lark_text())
    assert stale == ["program"]
    assert actionable == []
    assert unsound == []


# ---------------------------------------------------------------------------
# Terminals and production bodies (#1290)
#
# Each of these three classes was demonstrated green on a live file before the
# checks existed: a fabricated terminal in §10.2, a rule reference restored to
# a right-hand side, and a production body edited on one side only.
# ---------------------------------------------------------------------------


def _lark_lines() -> list[str]:
    return _lark_text().splitlines()


def _spec_lines() -> list[str]:
    return _MOD.ebnf_fence_lines((_ROOT / _MOD.SPEC).read_text(encoding="utf-8"))


def _messages(*problems: list[str]) -> str:
    return "\n".join(line for group in problems for line in group)


class TestTerminalAudit:
    def test_the_shipped_files_are_clean(self) -> None:
        assert _MOD.terminal_audit(_lark_lines(), _spec_lines()) == []

    def test_a_fabricated_spec_terminal_is_caught(self) -> None:
        """The demonstrated blind spot: `_HEADER` needs a lowercase lead."""
        spec = [*_spec_lines(), 'BOGUS_TERMINAL: "bogus"']
        problems = _MOD.terminal_audit(_lark_lines(), spec)
        assert [p for p in problems if "BOGUS_TERMINAL" in p and "never used" in p]

    def test_a_referenced_but_undeclared_terminal_is_caught(self) -> None:
        """The `DOUBLE_COLON` shape: used by a production, declared nowhere."""
        lark = [
            line.replace("UPPER_IDENT", "PHANTOM_IDENT")
            if line.startswith("slot_ref:")
            else line
            for line in _lark_lines()
        ]
        assert "PHANTOM_IDENT" in "\n".join(lark)
        problems = _MOD.terminal_audit(lark, _spec_lines())
        assert [p for p in problems if "PHANTOM_IDENT" in p and "never declared" in p]

    def test_deleting_a_terminal_still_in_use_is_caught(self) -> None:
        lark = [line for line in _lark_lines() if not line.startswith("INT_LIT:")]
        problems = _MOD.terminal_audit(lark, _spec_lines())
        assert [p for p in problems if "INT_LIT" in p and "never declared" in p]

    def test_a_missing_skipped_group_is_an_error_not_a_skip(self) -> None:
        """Losing the marker must fail, not silently waive every terminal."""
        spec = [
            line.replace("(skipped)", "(ignored by the lexer)") for line in _spec_lines()
        ]
        problems = _MOD.terminal_audit(_lark_lines(), spec)
        assert [p for p in problems if "no terminal group marked" in p]

    def test_a_note_between_declarations_does_not_end_the_skipped_group(self) -> None:
        """A comment after a declaration annotates it; it opens no new group."""
        assert "BLOCK_COMMENT" in _MOD.skipped_terminals(_spec_lines())
        assert "ANNOTATION_COMMENT" in _MOD.skipped_terminals(_spec_lines())

    def test_the_skipped_group_does_not_swallow_the_whole_fence(self) -> None:
        skipped = _MOD.skipped_terminals(_spec_lines())
        assert "FN" not in skipped and "INT_LIT" not in skipped


class TestTerminalPatterns:
    def test_the_shipped_files_are_clean(self) -> None:
        assert _MOD.terminal_patterns(_lark_lines(), _spec_lines()) == []

    def test_the_non_nesting_block_comment_regex_is_caught(self) -> None:
        """The live drift #1290 named: §1.3 says they nest, the regex did not."""
        spec = [
            line
            for line in _spec_lines()
            if not line.startswith(("BLOCK_COMMENT:", "// Block comments nest"))
        ]
        spec.append(r"BLOCK_COMMENT: /\{-[\s\S]*?-\}/")
        problems = _MOD.terminal_patterns(_lark_lines(), spec)
        assert [p for p in problems if "BLOCK_COMMENT" in p]

    def test_a_lark_terminal_missing_from_the_chapter_is_caught(self) -> None:
        spec = [line for line in _spec_lines() if not line.startswith("FLOAT_LIT:")]
        problems = _MOD.terminal_patterns(_lark_lines(), spec)
        assert [p for p in problems if "FLOAT_LIT" in p and "only in" in p]

    def test_a_pattern_that_drifted_is_caught(self) -> None:
        spec = [
            "INT_LIT: /[0-9]+/" if line.startswith("INT_LIT:") else line
            for line in _spec_lines()
        ]
        problems = _MOD.terminal_patterns(_lark_lines(), spec)
        assert [p for p in problems if "INT_LIT" in p]

    @pytest.mark.parametrize(
        ("body", "expected"),
        [
            (r"\"([^\"\\]|\\.)*\"", r'"([^"\\]|\\.)*"'),
            (r"\/\*[^*]*\*\/", r"/\*[^*]*\*/"),
            (r"[^/*]", r"[^/*]"),
            # An escaped backslash is copied whole, so the `\"` after it is
            # still an escape of the quote and not part of a `\\"` triple.
            (r"\\\"", r"\\" + '"'),
        ],
    )
    def test_normalise_pattern(self, body: str, expected: str) -> None:
        assert _MOD.normalise_pattern(body) == expected

    def test_the_two_files_spell_string_lit_differently_and_still_agree(self) -> None:
        """Non-vacuity: the normalisation is doing work, not comparing equals."""
        lark = _MOD.terminal_declarations(_lark_lines())["STRING_LIT"]
        spec = _MOD.terminal_declarations(_spec_lines())["STRING_LIT"]
        assert lark != spec
        assert _MOD.normalise_pattern(lark) == _MOD.normalise_pattern(spec)


class TestBodyDrift:
    def test_the_shipped_files_are_clean(self) -> None:
        assert _MOD.body_drift(_lark_lines(), _spec_lines()) == []

    def test_the_comparison_is_not_vacuous(self) -> None:
        shared = set(_MOD.rule_bodies(_lark_lines())) & set(
            _MOD.rule_bodies(_spec_lines())
        )
        assert len(shared) > 50
        assert {"primary_expr", "statement", "type_expr", "fn_call"} <= shared

    def test_a_restored_ambiguity_on_a_right_hand_side_is_caught(self) -> None:
        """The #1290 case: `statement` regaining its assert/assume alternatives."""
        spec = []
        for line in _spec_lines():
            spec.append(line)
            if line.startswith("statement:"):
                spec.append("         | assert_expr SEMICOLON")
        problems = _MOD.body_drift(_lark_lines(), spec)
        assert [p for p in problems if p.startswith("statement:")]

    def test_an_undocumented_literal_is_caught(self) -> None:
        """Typed holes: `"?"` in Lark, no spec terminal declaring it."""
        spec = [line for line in _spec_lines() if not line.startswith("HOLE:")]
        problems = _MOD.body_drift(_lark_lines(), spec)
        assert [p for p in problems if 'literal "?"' in p]

    def test_a_dropped_alternative_is_caught(self) -> None:
        spec = [
            line
            for line in _spec_lines()
            if "| refinement_type" not in line and "| fn_type" not in line
        ]
        problems = _MOD.body_drift(_lark_lines(), spec)
        assert [p for p in problems if p.startswith("type_expr:")]

    def test_a_terminal_the_chapter_alone_names_is_caught(self) -> None:
        """The `effect_list` defect: an alternative adding only a terminal.

        Every rule reference stays identical, so the rule half of the
        comparison sees nothing — this cell is the only thing that dies when
        the terminal half is deleted.
        """
        spec = []
        for line in _spec_lines():
            spec.append(line)
            if line.startswith("effect_list:"):
                spec.append("           | UPPER_IDENT  // effect variable")
        problems = _MOD.body_drift(_lark_lines(), spec)
        assert [
            p
            for p in problems
            if p.startswith("effect_list:") and "UPPER_IDENT" in p and _MOD.SPEC in p
        ]

    def test_a_terminal_only_lark_names_is_caught(self) -> None:
        spec = [
            line.replace(" SEMICOLON", "")
            if line.lstrip().startswith("| expr SEMICOLON")
            else line
            for line in _spec_lines()
        ]
        assert "| expr SEMICOLON" not in "\n".join(spec)
        problems = _MOD.body_drift(_lark_lines(), spec)
        assert [
            p
            for p in problems
            if p.startswith("statement:") and "SEMICOLON" in p and _MOD.LARK in p
        ]

    def test_a_rule_referring_to_itself_is_not_drift(self) -> None:
        """Lark spells repetition with left recursion, the chapter with `*`."""
        lark = _MOD.rule_bodies(_lark_lines())
        assert "add_expr" in "".join(lark["add_expr"]), "no longer left-recursive"
        assert not [p for p in _MOD.body_drift(_lark_lines(), _spec_lines())]

    def test_a_waived_production_is_folded_at_the_rule_the_waiver_names(self) -> None:
        """`fn_call` inlines what the chapter factors into `module_call`."""
        rules, terminals, inlined = _MOD._spec_symbols(
            "fn_call", _MOD.rule_bodies(_spec_lines()), set(_MOD.rule_bodies(_spec_lines()))
        )
        assert "module_path" in rules
        assert {"DOT", "DOUBLE_COLON"} <= terminals
        assert "module_call" not in rules and "qualified_call" not in rules

    def test_an_aliased_alternative_is_not_read_as_a_rule_reference(self) -> None:
        bodies = _MOD.rule_bodies(_lark_lines())
        assert "func_call" not in "".join(bodies["fn_call"])


class TestCommentStripping:
    def test_a_regex_body_ending_in_a_slash_is_not_truncated(self) -> None:
        """`line.split("//")[0]` cut the annotation-comment terminal in half."""
        line = r"%ignore /\/\*[^*]*\*+([^\/*][^*]*\*+)*\//"
        assert _MOD.strip_comment(line) == line

    def test_a_comment_after_a_regex_is_still_removed(self) -> None:
        assert _MOD.strip_comment(r"INT_LIT: /0|[1-9]/  // numbers") == (
            r"INT_LIT: /0|[1-9]/  "
        )

    def test_a_double_slash_inside_a_literal_is_not_a_comment(self) -> None:
        assert _MOD.strip_comment('sep: "//" name') == 'sep: "//" name'

    def test_a_whole_line_comment_is_still_removed(self) -> None:
        assert _MOD.strip_comment("// assert_stmt: gone").strip() == ""
