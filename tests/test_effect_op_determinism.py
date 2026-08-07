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

import json
import os
import subprocess
import sys
from pathlib import Path

from vera.environment import TypeEnv
from vera.types import INT, ConcreteEffectRow, EffectInstance

# Bounded on purpose: six interpreter starts are enough to catch a
# frozenset-order flip (the pre-fix program bound `Http.get` on six of the
# first eight seeds — 0, 1, 2, 5, 6 and 7) without turning the default suite
# into a subprocess farm.
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


# Spec §7.3.3: the same effect MAY appear twice with different type
# arguments — two independent cells.  Which one a bare `get` names is the
# type-ARGUMENT sibling of the op-NAME question above, and it was the same
# frozenset lottery (`_effect_type_mapping`'s row leg): the checker typed
# `get(())` as Int on some seeds and Bool on others, so the identical source
# was check-clean or E121 depending on the interpreter start.  Codegen
# meanwhile took the LAST instantiation in the row, so even once the checker
# settled the two disagreed — `state_get_Bool` (i32) for a call the checker
# typed Int (i64).  Both sides now take the FIRST in source order.
#   outer Bool cell = true, inner Int cell = 33; probe reads the Int cell
_TWO_INSTANTIATIONS = """\
private fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>, State<Bool>>)
{
  get(())
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Bool>](@Bool = true) {
    get(@Unit) -> { resume(@Bool.0) },
    put(@Bool) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 33) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      probe(())
    }
  }
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


def test_two_instantiations_of_one_effect_bind_source_order(
    tmp_path: Path,
) -> None:
    """`effects(<State<Int>, State<Bool>>)` names the Int cell, every seed.

    Found while fixing the op-NAME lottery: the type-ARGUMENT leg of effect
    resolution had the identical frozenset dependence, and codegen's own
    per-row loop disagreed with it (last in the row rather than first).  The
    value 33 is the source-order-first cell's; the Bool cell holds `true`,
    which is neither 33 nor a plausible default.
    """
    results = _sweep(tmp_path, "two_inst.vera", _TWO_INSTANTIATIONS, "run")
    assert len(results) == 1, (
        f"type-argument resolution is not hash-seed stable: {len(results)} "
        f"distinct outcomes:\n" + "\n--\n".join(sorted(results))
    )
    only = results.pop()
    assert only.startswith("rc=0"), only
    assert only.splitlines()[1].strip() == "33", only


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


# A row whose members the order tuple does not mention at all — the public
# `ordered_effect_row()` fallback.  Its two members share the effect NAME and
# differ only in their type ARGUMENT (spec §7.3.3: two independent cells), so
# a name-only sort key ties them and `sorted`, being stable, hands back the
# `frozenset`'s own iteration order — the PYTHONHASHSEED dependence the whole
# ordering exists to remove.  Printed from a child interpreter so the sweep is
# a genuine cross-seed comparison rather than one process's lucky bucket
# layout.
_ORDER_FALLBACK_PROBE = """\
import json
from vera.checker.core import TypeChecker
from vera.environment import TypeEnv
from vera.types import BOOL, INT, ConcreteEffectRow, EffectInstance, pretty_type

si = EffectInstance("State", (INT,))
sb = EffectInstance("State", (BOOL,))
row = ConcreteEffectRow(frozenset({si, sb}))

env = TypeEnv()
env.current_effect_row = row
env.current_effect_order = ()
order = [
    f"{e.name}<{', '.join(pretty_type(a) for a in e.type_args)}>"
    for e in env.ordered_effect_row()
]

tc = TypeChecker()
tc.env.current_effect_row = row
tc.env.current_effect_order = ()
mapping = {
    k: pretty_type(v) for k, v in tc._effect_type_mapping("State").items()
}
print(json.dumps({"order": order, "mapping": mapping}))
"""


def _sweep_python(payload: str) -> set[str]:
    """The set of distinct stdout results of *payload* over ``_SEEDS``."""
    results = set()
    for seed in _SEEDS:
        proc = subprocess.run(
            [sys.executable, "-c", payload],
            capture_output=True, text=True, encoding="utf-8",
            env={**os.environ, "PYTHONHASHSEED": seed},
            timeout=120,
            check=True,
        )
        results.add(proc.stdout.strip())
    return results


def test_unmentioned_row_members_order_structurally() -> None:
    """The name tiebreak is not a total order — the STRUCTURE has to break it.

    `ordered_effect_row()` is a public method whose docstring promises a
    result independent of the interpreter start, including for a row assigned
    without its companion order tuple (a consumer outside the checker).  Two
    instantiations of ONE effect tie on name, so the fallback fell straight
    back into frozenset iteration order — and `_effect_type_mapping`, which
    reads the same list, then typed a bare `get(())` as `Int` on some seeds
    and `Bool` on others.  Both are asserted here: the order AND the mapping
    it selects, over the same seeds the source-level sweeps use.
    """
    results = _sweep_python(_ORDER_FALLBACK_PROBE)
    assert len(results) == 1, (
        "the unmentioned-member fallback is not hash-seed stable: "
        f"{len(results)} distinct outcomes across seeds {_SEEDS}:\n"
        + "\n--\n".join(sorted(results))
    )
    only = json.loads(results.pop())
    # `Bool` sorts before `Int` under the structural key, so the order —
    # and therefore the type argument `_effect_type_mapping` picks — is a
    # property of the two types, not of the run.
    assert only["order"] == ["State<Bool>", "State<Int>"], only
    assert only["mapping"] == {"T": "Bool"}, only


# The same fallback over two REFINEMENT aliases of one base.  `pretty_type`
# is a presentation renderer: it prints a refinement as `{@Int | ...}` with
# the predicate elided, and strips the built-in type-var marker (`T#b` → `T`).
# Keying the structural tiebreak on it therefore reintroduced the tie one
# level down — `State<Pos>` and `State<Neg>` rendered identically, so the
# stable sort handed back frozenset order again (round-5 review).
_REFINED_ORDER_FALLBACK_PROBE = """\
import json
from vera import ast
from vera.environment import TypeEnv
from vera.types import INT, ConcreteEffectRow, EffectInstance, RefinedType


def refined(op, bound):
    return RefinedType(
        base=INT,
        predicate=ast.BinaryExpr(
            op=op,
            left=ast.SlotRef(type_name="Int", type_args=None, index=0),
            right=ast.IntLit(value=bound)))


pos = EffectInstance("State", (refined(ast.BinOp.GT, 0),))
neg = EffectInstance("State", (refined(ast.BinOp.LT, 0),))
assert pos != neg

env = TypeEnv()
env.current_effect_row = ConcreteEffectRow(frozenset({pos, neg}))
env.current_effect_order = ()
print(json.dumps([
    str(e.type_args[0].predicate.op) for e in env.ordered_effect_row()
]))
"""


def test_refinement_predicates_break_the_order_tie() -> None:
    """Two refinement aliases of one base are ordered, not left to the seed.

    The type-argument tiebreak was rendered with `pretty_type`, which elides
    a refinement's predicate — so this row's two members produced the same
    key and the fallback fell straight back into frozenset iteration order,
    the exact failure the tiebreak exists to remove.  Same seeds as the
    sweeps above; the assertion is a single outcome, not a particular one, so
    it pins determinism rather than an arbitrary choice of winner.
    """
    results = _sweep_python(_REFINED_ORDER_FALLBACK_PROBE)
    assert len(results) == 1, (
        "two refinement-typed instantiations of one effect are not hash-seed "
        f"stable: {len(results)} distinct outcomes across seeds {_SEEDS}:\n"
        + "\n--\n".join(sorted(results))
    )
    order = json.loads(results.pop())
    assert sorted(order) == ["BinOp.GT", "BinOp.LT"], order


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
