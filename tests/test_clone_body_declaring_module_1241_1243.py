"""#1241 + #1243: an imported clone's body calls its OWN module's functions.

A public generic in `glib` whose body calls `glib`'s private `need` is
cloned by the importer and compiled into the importer's flat module.  Both
consumers of that clone body then resolved the bare name `need` in the
IMPORTER's namespace:

* the verifier (#1241) — `_scoped_fn_lookup` falls through to
  `self.env.lookup_function`, and `_declaring_module_scope` swapped the
  naming env and the source buffer but not the function registry; and
* codegen (#1243) — the clone-emission door was the one door that did not
  thread the module's intra-rename map, so a bare sibling call landed on
  the importer's same-named function rather than the module's own `mod$…`
  emission.

The checker's answer is the module's own (spec §8.5.1), proven by a
type-discriminating probe: `glib`'s `need(@Int -> @Int)` beside an
importer's `need(@Int -> @Bool)` checks clean, which only types if
`glib`'s is meant.

THE TWO HALVES CANNOT LAND APART, and the tests are written so that
neither passes alone.  Fixing the verifier alone converts today's
aligned-but-both-wrong state into a FALSE TIER-1: `vera verify` goes
clean while the compiled program still runs the importer's function and
traps on the postcondition it just proved.  Fixing codegen alone leaves a
false REJECTION: the run is right and `vera verify` still refuses a valid
program.  Every case below therefore asserts the verify verdict AND the
runtime value in one test.

The oracle is `glib` STANDALONE — the same module verified and run on its
own — so no expected value here is read off what the importer happens to
produce.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera

# The subprocess must run the SAME compiler this session imported.  A
# checkout that is not the one the editable install points at — a linked
# git worktree, say — otherwise has `python -m vera.cli` resolve the OTHER
# tree, and the cases below would report on a compiler nobody edited.  A
# no-op wherever the two coincide.
_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    return tmp_path


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env,
    )


def _verify_codes(path: Path) -> list[str]:
    """The error codes `vera verify --json` reports for *path*."""
    proc = _cli("verify", "--json", str(path))
    payload = json.loads(proc.stdout)
    return [d["error_code"] for d in payload["diagnostics"]]


def _run_value(path: Path, fn: str | None = None) -> str:
    """`vera run`'s stdout, or a marker naming how it failed."""
    args = ["run", str(path)]
    if fn is not None:
        args += ["--fn", fn]
    proc = _cli(*args)
    if proc.returncode != 0:
        return f"FAILED: {(proc.stdout + proc.stderr).strip()[-400:]}"
    return proc.stdout.strip().splitlines()[-1]


# --- the value shape -------------------------------------------------
# `glib.gen` promises 111 and its own `need` delivers it.  The importer
# declares a DIFFERENT `need` promising (and returning) 999, and calls it
# directly as well, so `main` is 111 + 999 = 1110 — a total that
# distinguishes the right routing (1110) from the wrong one (999 + 999 =
# 1998), rather than merely from a crash.
_GLIB_VALUE = """
private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  111
}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  need(0)
}

public fn glib_main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""

_APP_VALUE = """
import glib(gen);

private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 999)
  effects(pure)
{
  999
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1) + need(0)
}
"""

# --- the type-discriminating shape -----------------------------------
# The importer's `need` returns `@Bool` (i32) where `glib`'s returns
# `@Int` (i64).  The checker accepts the program, which by itself proves
# the clone body means glib's `need`; codegen calling the importer's
# emitted invalid WASM from that check-green source.
_GLIB_TYPED = """
private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  111
}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  need(0)
}

public fn glib_main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""

_APP_TYPED = """
import glib(gen);

private fn need(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if need(0) then { gen(1) } else { 0 }
}
"""

# --- the where-helper shape ------------------------------------------
# The module function the clone reaches is a `where` helper of another of
# the module's functions rather than a top-level private — the same
# routing question one nesting level in.
_GLIB_CHAIN = """
private fn mid(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  need(0)
}

private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  111
}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  mid(0)
}

public fn glib_main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""

_APP_CHAIN = """
import glib(gen);

private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 999)
  effects(pure)
{
  999
}

private fn mid(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 999)
  effects(pure)
{
  999
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1) + need(0)
}
"""


def test_declaring_module_oracle_standalone(tmp_path: Path) -> None:
    """`glib` on its own: verify clean, `gen` returns 111.

    The oracle for every expectation below.  If this ever moves, the
    module's own meaning changed and the cross-module expectations are
    measuring the wrong thing.
    """
    _write(tmp_path, {"glib.vera": _GLIB_VALUE})
    assert _verify_codes(tmp_path / "glib.vera") == []
    assert _run_value(tmp_path / "glib.vera", "glib_main") == "111"


@pytest.mark.parametrize(
    ("glib_src", "app_src", "expected"),
    [
        pytest.param(_GLIB_VALUE, _APP_VALUE, "1110", id="private_callee"),
        pytest.param(_GLIB_CHAIN, _APP_CHAIN, "1110", id="two_hop_callee"),
    ],
)
def test_clone_body_resolves_in_its_own_module(
    tmp_path: Path, glib_src: str, app_src: str, expected: str,
) -> None:
    """Verify verdict AND runtime value, together — the pairing assertion.

    The verifier half alone makes the first assertion pass and leaves the
    second failing on a postcondition trap (a false Tier-1: proved clean,
    violated at run).  The codegen half alone makes the second pass and
    leaves the first refusing a valid program.  Only both together.
    """
    _write(tmp_path, {"glib.vera": glib_src, "app.vera": app_src})
    assert _verify_codes(tmp_path / "app.vera") == [], (
        "false rejection: the clone's contract was proved against the "
        "IMPORTER's same-named function"
    )
    assert _run_value(tmp_path / "app.vera") == expected, (
        "the compiled clone called the importer's function"
    )


def test_type_discriminating_callee_compiles(tmp_path: Path) -> None:
    """A DIFFERENTLY TYPED importer function of the same name.

    `glib`'s `need` returns `@Int` (i64) and the importer's returns
    `@Bool` (i32).  The checker accepts the program — which is itself the
    proof that the clone body means glib's `need` (§8.5.1) — so codegen
    must emit a module that loads and runs.  Routing to the importer's
    emitted invalid WASM from check-green source.
    """
    _write(tmp_path, {"glib.vera": _GLIB_TYPED, "app.vera": _APP_TYPED})
    check = _cli("check", "--quiet", str(tmp_path / "app.vera"))
    assert check.returncode == 0, check.stdout + check.stderr
    assert _verify_codes(tmp_path / "app.vera") == []
    assert _run_value(tmp_path / "app.vera") == "111"


def test_unshadowed_callee_control(tmp_path: Path) -> None:
    """No same-named importer function: the bare emission was already right.

    This case worked before the fix and must keep working — it is what
    proves the defect is the SHADOWED name rather than cross-module calls
    in general, so a reroute that fired unconditionally (or a scope swap
    that lost the module's own registry) would show up here rather than
    passing either way.
    """
    app = """
import glib(gen);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""
    _write(tmp_path, {"glib.vera": _GLIB_VALUE, "app.vera": app})
    assert _verify_codes(tmp_path / "app.vera") == []
    assert _run_value(tmp_path / "app.vera") == "111"
