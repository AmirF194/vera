"""#1215: bare effect-op resolution is deterministic and source-ordered.

Two effects in one function's effect row can declare the SAME op name — the
built-in ``State`` and ``Http`` both declare ``get``, so
``effects(<State<Int>, Http>)`` is a two-candidate row without any user
``effect`` declaration at all.  ``Environment.lookup_effect_op`` used to pick
by iterating ``ConcreteEffectRow.effects``, a ``frozenset`` whose iteration
order depends on ``PYTHONHASHSEED``: the same source bound ``State.get``
(returns the cell's ``Int``) on some interpreter starts and ``Http.get``
(unhandled, so ``E217``) on others.

The pinned rule (spec §7.4): innermost handled effect first, then the
function's DECLARED row in SOURCE order, then the registered-effect
fallback in registration order.  Every layer is an ordered sequence, so the
binding is a property of the program text alone.

The fixtures below make the two candidate bindings produce DIFFERENT
observables rather than two spellings of "an error": the source-order
program runs to ``70`` (7 in the cell, times ten), and the reversed row is a
loud ``E217`` naming ``Http``.  A wrong binding therefore cannot hide behind
a value that coincides with a default.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

from vera.environment import TypeEnv
from vera.types import INT, ConcreteEffectRow, EffectInstance

# Bounded on purpose: six interpreter starts are enough to catch a
# frozenset-order flip (the pre-fix program bound `Http.get` on four of the
# first eight seeds) without turning the default suite into a subprocess farm.
_SEEDS = ("0", "1", "2", "3", "4", "5")

# `probe` delegates a bare `get(())` while declaring BOTH `State<Int>` and
# `Http` — the two-candidate row.  `main` discharges the State half with a
# handler and leaves `Http` to the host, so the whole program compiles and
# runs when (and only when) `get` binds the source-order-first `State`.
_SOURCE_ORDER = """\
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>, Http>)
{
  get(()) * 10
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Http>)
{
  handle[State<Int>](@Int = 7) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    probe(())
  }
}
"""

# The SAME program with the declared row written the other way round.  Under
# the source-order rule `Http.get` binds, and a bare Http op has no handler
# and no bare host route — E217.
_REVERSED = _SOURCE_ORDER.replace(
    "effects(<State<Int>, Http>)", "effects(<Http, State<Int>>)")

# An enclosing `handle[State<Int>]` must beat the DECLARED row, which here
# lists only `Http`: the handled effect is innermost, so `get` is the cell's.
_HANDLED_INNER = """\
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Http>)
{
  handle[State<Int>](@Int = 9) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    get(()) * 10
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Http>)
{
  probe(())
}
"""


def _run_seeded(
    path: Path, seed: str, *argv: str,
) -> subprocess.CompletedProcess[str]:
    """Run `vera <argv> path` in a child interpreter at *seed*."""
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *argv, str(path)],
        capture_output=True, text=True, encoding="utf-8",
        env={**os.environ, "PYTHONHASHSEED": seed},
        timeout=120,  # bound each child so a hang fails here, not at CI timeout
        check=False,
    )


def _sweep(tmp_path: Path, name: str, src: str, *argv: str) -> set[str]:
    """The set of distinct `(returncode, stdout+stderr)` results over _SEEDS."""
    f = tmp_path / name
    f.write_text(src, encoding="utf-8")
    results = set()
    for seed in _SEEDS:
        proc = _run_seeded(f, seed, *argv)
        results.add(f"rc={proc.returncode}\n{proc.stdout}{proc.stderr}")
    return results


def test_two_effects_one_op_binds_source_order_every_hash_seed(
    tmp_path: Path,
) -> None:
    """`effects(<State<Int>, Http>)` binds `State.get` at every seed.

    Pre-fix this was PYTHONHASHSEED roulette: the frozenset handed out
    `Http` first often enough that the program failed to compile on most
    seeds and printed 70 on the rest.
    """
    results = _sweep(tmp_path, "src_order.vera", _SOURCE_ORDER, "run")
    assert len(results) == 1, (
        f"bare-op binding is not hash-seed stable: {len(results)} distinct "
        f"outcomes across seeds {_SEEDS}:\n" + "\n--\n".join(sorted(results))
    )
    only = results.pop()
    # The VALUE, not merely "it compiled": 7 in the State cell times ten.
    # `Http.get` binding instead cannot produce this — it is not callable bare.
    assert only.startswith("rc=0"), only
    assert only.splitlines()[1].strip() == "70", only


def test_reversed_declared_row_binds_the_other_effect(tmp_path: Path) -> None:
    """Swapping the row's two effects swaps the binding — deterministically.

    This is the half that proves the rule is SOURCE ORDER rather than "State
    always wins": the identical program with `effects(<Http, State<Int>>)`
    binds `Http.get`, which has no bare route, so it is rejected at check.
    """
    results = _sweep(tmp_path, "reversed.vera", _REVERSED, "check", "--quiet")
    assert len(results) == 1, (
        f"reversed-row binding is not hash-seed stable: {len(results)} "
        f"distinct outcomes:\n" + "\n--\n".join(sorted(results))
    )
    only = results.pop()
    assert only.startswith("rc=1"), only
    assert "E217" in only, only
    assert "Http.get" in only, only


def test_handled_effect_beats_the_declared_row(tmp_path: Path) -> None:
    """An enclosing `handle[State<Int>]` wins over a declared `Http`.

    The declared row names only `Http`, so a row-order-only rule would bind
    `Http.get` and reject the program; the handled effect is innermost and
    must be consulted first.
    """
    results = _sweep(tmp_path, "handled.vera", _HANDLED_INNER, "run")
    assert len(results) == 1, (
        f"handled-effect precedence is not hash-seed stable: {len(results)} "
        f"distinct outcomes:\n" + "\n--\n".join(sorted(results))
    )
    only = results.pop()
    assert only.startswith("rc=0"), only
    assert only.splitlines()[1].strip() == "90", only


def test_lookup_effect_op_returns_the_ordered_row_head() -> None:
    """The resolved OpInfo itself differs with the recorded order.

    A signature-level assertion, not a diagnostic one: `State.get` returns the
    cell type while `Http.get` takes a URL and returns a `String`, so the two
    candidate bindings are distinguishable values, and swapping the order
    swaps which one comes back.
    """
    env = TypeEnv()
    state = EffectInstance("State", (INT,))
    http = EffectInstance("Http", ())
    env.current_effect_row = ConcreteEffectRow(frozenset({state, http}))

    env.current_effect_order = (state, http)
    first = env.lookup_effect_op("get")
    assert first is not None
    assert first.parent_effect == "State"

    env.current_effect_order = (http, state)
    second = env.lookup_effect_op("get")
    assert second is not None
    assert second.parent_effect == "Http"

    # Distinguishable by SIGNATURE, so a test asserting the wrong one cannot
    # accidentally pass: State's `get` takes nothing, Http's takes a URL.
    assert first.param_types != second.param_types

    # A row member the order tuple never mentions still resolves, by a
    # deterministic name tiebreak rather than set iteration order.
    env.current_effect_order = ()
    fallback = env.lookup_effect_op("get")
    assert fallback is not None
    assert fallback.parent_effect == "Http"  # sorted(("Http", "State"))[0]


def test_qualified_lookup_is_unaffected_by_row_order() -> None:
    """A qualified `State.get` / `Http.get` never consults the row."""
    env = TypeEnv()
    state = EffectInstance("State", (INT,))
    http = EffectInstance("Http", ())
    env.current_effect_row = ConcreteEffectRow(frozenset({state, http}))
    for order in ((state, http), (http, state)):
        env.current_effect_order = order
        state_op = env.lookup_effect_op("get", qualifier="State")
        http_op = env.lookup_effect_op("get", qualifier="Http")
        assert state_op is not None and state_op.parent_effect == "State"
        assert http_op is not None and http_op.parent_effect == "Http"
