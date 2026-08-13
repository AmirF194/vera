"""Tests for the editor-grammar drift gate (scripts/check_editor_grammars.py).

The gate (#1156) compares each editor grammar under ``editors/`` against the
compiler's live effect registry.  These tests pin the two halves separately:
the registry read (effects in, abilities out) and the word-boundary presence
test (sound on absence, deliberately optimistic on presence).

Two of them exercise the gate end to end rather than a single function,
because that is where its value sits: a grammar that drops an effect must
exit 1, and the registry it is compared against must come from the tree
being checked rather than from whatever ``vera`` the interpreter can import.
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from vera.environment import TypeEnv

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_editor_grammars.py"


def _load() -> Any:
    """Import the gate script by path, since ``scripts/`` is not a package."""
    spec = importlib.util.spec_from_file_location("check_editor_grammars", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


def test_effect_names_match_the_live_registry() -> None:
    """The gate reads its effect list from the registry, so a new effect
    is picked up without touching this script.
    """
    env = TypeEnv()
    assert _MOD.effect_names() == sorted(env.effects)
    # Abilities are a separate namespace and are out of scope for this gate.
    assert not set(_MOD.effect_names()) & set(env.abilities)


def test_effect_names_is_not_vacuous() -> None:
    """The names the grammars drifted on must actually be in the set checked."""
    names = set(_MOD.effect_names())
    assert {"DB", "HttpServer", "Inference", "Random"} <= names


@pytest.mark.parametrize(
    ("text", "names", "expected"),
    [
        # Present as a whole word -> not missing, in each grammar's own format.
        (r'"match": "\\b(IO|State|DB)\\b"', ["IO", "DB"], []),
        (r"<string>\b(IO|State|DB)\b</string>", ["DB"], []),
        ("syntax keyword veraEffectType IO State DB", ["DB"], []),
        # Absent -> missing (the whole observed failure class).
        (r'"match": "\\b(IO|State|Exn)\\b"', ["DB", "Random"], ["DB", "Random"]),
        # A prefix of a longer name does not satisfy the longer name...
        ("Http", ["HttpServer"], ["HttpServer"]),
        # ...and the longer name does not satisfy its prefix.
        ("HttpServer", ["Http"], ["Http"]),
        # Presence is optimistic by design: a mention in a comment passes.
        ("<!-- Built-in effects: DB -->", ["DB"], []),
        # Regex metacharacters in a name must be matched literally: without
        # re.escape, `\bA.B\b` matches "A0B" and the name is wrongly reported
        # as present.  The pair discriminates — the first case is only [] when
        # the dot is treated as a wildcard, the second only [] when it is not.
        ("A0B", ["A.B"], ["A.B"]),
        ("A.B", ["A.B"], []),
        # Empty registry -> nothing can be missing.
        ("", [], []),
    ],
)
def test_missing_effects(text: str, names: list[str], expected: list[str]) -> None:
    """Matching is whole-word, literal, and optimistic.

    Covers all three grammar formats; both directions of the prefix case
    (``Http`` does not satisfy ``HttpServer``, nor the reverse); the
    ``re.escape`` pair, where ``A.B`` must not match ``A0B``; and that a
    name mentioned only in a comment counts as present.
    """
    assert _MOD.missing_effects(text, names) == expected


def test_shipped_grammars_are_clean() -> None:
    """The grammars in the tree pass the gate — this is what keeps CI red
    if a later effect is added without updating them.
    """
    assert _MOD.main() == 0


def _mirror_checked_files(root: Path, dest: Path) -> None:
    """Copy everything the gate checks into ``dest``, at its repo-relative
    path — the grammars and the two extension READMEs that repeat the effect
    list in prose."""
    for rel in (*_MOD.GRAMMARS, *_MOD.PROSE):
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / rel, target)


def test_drifted_grammar_fails_the_gate(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """The gate's whole point: a listed grammar that drops an effect is red.

    The completeness guard covers grammars nobody listed; this covers the
    failure actually observed — a grammar that *is* listed, and is missing a
    name.  Without it, deleting the ``if missing`` branch from ``main`` leaves
    the rest of this file green.
    """
    root = _SCRIPT.parent.parent
    _mirror_checked_files(root, tmp_path)
    assert _MOD.main(tmp_path) == 0  # control: the mirror alone is clean

    target = tmp_path / _MOD.GRAMMARS[0]
    text = target.read_text(encoding="utf-8")
    assert "|DB)" in text, "fixture assumes DB closes the effect alternation"
    target.write_text(text.replace("|DB)", ")"), encoding="utf-8")

    assert _MOD.main(tmp_path) == 1
    err = capsys.readouterr().err
    assert "DB" in err
    assert _MOD.GRAMMARS[0] in err


def test_drifted_extension_readme_fails_the_gate(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """Both extension READMEs carry a second, prose copy of the effect list.

    They drifted with the grammars and were hand-corrected alongside them, so
    they go through the same registry comparison; otherwise the documented
    list can fall behind the grammar it describes with nothing to say so.
    """
    root = _SCRIPT.parent.parent
    _mirror_checked_files(root, tmp_path)
    assert _MOD.main(tmp_path) == 0  # control: the mirror alone is clean

    target = tmp_path / _MOD.PROSE[0]
    text = target.read_text(encoding="utf-8")
    assert "`Random`, " in text, "fixture assumes Random is listed mid-sentence"
    target.write_text(text.replace("`Random`, ", ""), encoding="utf-8")

    assert _MOD.main(tmp_path) == 1
    err = capsys.readouterr().err
    assert "Random" in err
    assert _MOD.PROSE[0] in err


@pytest.mark.parametrize(
    "rel",
    [
        # Outside a syntax directory, caught by its extension alone.
        "editors/emacs/vera-mode.el",
        # A tree-sitter query set: no syntax directory, no tmLanguage.
        "editors/helix/queries/vera/highlights.scm",
        # A TextMate grammar filed anywhere but ``syntaxes/`` — the case a
        # bare ``.tmlanguage`` suffix misses, since the real vscode grammar is
        # named ``.tmLanguage.json``.
        "editors/zed/vera.tmLanguage.json",
    ],
)
def test_unlisted_grammar_fails_the_gate(
    rel: str, tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A new grammar nobody added to GRAMMARS must fail, not pass unchecked."""
    root = _SCRIPT.parent.parent
    _mirror_checked_files(root, tmp_path)
    assert _MOD.main(tmp_path) == 0  # control: the mirror alone is clean

    newcomer = tmp_path / rel
    newcomer.parent.mkdir(parents=True)
    newcomer.write_text("no effect names here\n", encoding="utf-8")

    assert _MOD.main(tmp_path) == 1
    assert rel in capsys.readouterr().err


def _tree_with_an_extra_effect(dest: Path, extra: str) -> Path:
    """A self-contained checkout: the shipped grammars, a copy of the gate,
    and a ``vera`` package whose registry names one effect they do not.

    Returns the path of the copied script.
    """
    _mirror_checked_files(_SCRIPT.parent.parent, dest)
    (dest / "scripts").mkdir(parents=True, exist_ok=True)
    script = dest / "scripts" / _SCRIPT.name
    shutil.copyfile(_SCRIPT, script)

    package = dest / "vera"
    package.mkdir()
    (package / "__init__.py").write_text("", encoding="utf-8")
    names = sorted([*_MOD.effect_names(), extra])
    (package / "introspect.py").write_text(
        "def effects_payload():\n"
        f"    names = {names!r}\n"
        '    return {"items": [{"name": n, "kind": "effect"} for n in names]}\n',
        encoding="utf-8",
    )
    return script


def test_the_registry_is_read_from_the_tree_being_checked(
    tmp_path: Path,
) -> None:
    """The gate must compare the grammars against *this* checkout's registry.

    ``scripts/`` is not a package, so a bare ``import vera`` resolves through
    site-packages — from a git worktree, an editable install points at the
    main checkout, and the gate would then hold one tree's grammars against
    another tree's effect list and report OK over real drift.  A subprocess is
    the only way to see this: in-process, ``vera`` is already imported.
    """
    script = _tree_with_an_extra_effect(tmp_path, "Telemetry")
    env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}

    proc = subprocess.run(
        [sys.executable, str(script)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        env=env,
        cwd=tmp_path,
        check=False,  # a non-zero exit is the assertion, not an error
    )

    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "Telemetry" in proc.stderr
    # Every grammar is short by exactly the one name the fake registry adds.
    for rel in _MOD.GRAMMARS:
        assert f"{rel}: Telemetry" in proc.stderr


def test_discovery_ignores_non_grammar_editor_files() -> None:
    """Discovery must not flag every file under editors/ (ftplugin, READMEs)."""
    root = _SCRIPT.parent.parent
    assert sorted(_MOD.discovered_grammars(root)) == sorted(_MOD.GRAMMARS)
