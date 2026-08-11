"""Tests for the grammar rule-name drift gate (scripts/check_grammar_alignment.py).

The gate (#683) compares the rule headers of ``spec/10-grammar.md`` against
those of ``vera/grammar.lark``.  These tests pin the two extractors, the
allowlist arithmetic, and the one false positive the issue itself was built on:
``qualified_call`` and ``module_call`` are *not* drift, and the gate must never
report them.
"""

from __future__ import annotations

import importlib.util
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
    """Past a handful of entries the header-only comparison is the wrong model."""
    assert len(_MOD.ALLOWLIST) <= 15


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
        return
    # Deleting the alias the reason names must fail too.
    stripped = _lark_text().replace(f"-> {waiver.lark_alias}", "")
    _, _, unsound = _MOD.drift(lark, spec, stripped)
    assert (name, f"no `-> {waiver.lark_alias}` alias left in {_MOD.LARK}") in unsound


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
        ('LOWER_IDENT: /[a-z]\\w*/', set()),
        # Directives, comments, continuations and blanks contribute nothing.
        ('%ignore WS', set()),
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
        ("```ebnf\nASSERT: \"assert\"\n```", set()),
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
