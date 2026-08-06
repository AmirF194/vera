"""Differential gate: :mod:`vera.naming` must render what the CHECKER renders.

The consolidation in #1208 / #1209 replaces six per-subsystem naming
renderings with one, and takes the checker's rendering as the rule — so the
load-bearing claim is not "the module looks right", it is "the module is
byte-identical to the checker on every type expression the checker names".
A unit suite cannot establish that: the divergences that caused the bug
class live in alias corners nobody thought to enumerate.

So this instruments the checker's two naming entry points, runs it over the
whole ``.vera`` corpus (examples, conformance programs and their module
fixtures, and the PR #1202 probe corpus) plus an inline battery aimed at the
alias / refinement / function-type / shadowing corners, and asserts ZERO
divergence across every recorded pair.

The module-side environment is built AT RECORD TIME from the live
:class:`~vera.environment.Environment` (``alias_env_from_environment``), so
each comparison sees exactly the alias table and type-parameter scope the
checker had at that instant — mid-check ``forall`` scopes included.  The
checker's own result is what is returned to it, so instrumentation cannot
change what the checker does.

Every recorded pair is compared regardless of whether the program CHECKS:
naming runs while diagnostics accumulate, and a program that fails to check
still exercises the renderer (often on exactly the malformed shapes the
corners live in).  Only a program that fails to PARSE contributes nothing,
and those are counted.

The gate guards itself against becoming vacuous — see
``test_corpus_sweep_is_not_vacuous`` for the floors, and
``test_differential_gate_detects_divergence`` for the live proof that it can
go red.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from vera import ast, naming
from vera.checker.core import TypeChecker
from vera.parser import parse_to_ast

_ROOT = Path(__file__).resolve().parent.parent
_CORPUS_DIRS = (
    _ROOT / "examples",
    _ROOT / "tests" / "conformance",
    _ROOT / "tests" / "probes",
)


# =====================================================================
# The harness
# =====================================================================

@dataclass
class Observation:
    """One (legacy, module) rendering pair, with the context to triage it."""

    origin: str
    entry: str
    legacy: str
    module: str
    env_aliases: int
    alias_in_arg: bool
    shape: str

    @property
    def diverged(self) -> bool:
        return self.legacy != self.module


@dataclass
class Sweep:
    """Accumulated observations plus the corpus bookkeeping."""

    observations: list[Observation] = field(default_factory=list)
    parse_skipped: list[str] = field(default_factory=list)
    files_seen: list[str] = field(default_factory=list)

    @property
    def divergences(self) -> list[Observation]:
        return [o for o in self.observations if o.diverged]

    @property
    def with_aliases(self) -> list[Observation]:
        return [o for o in self.observations if o.env_aliases]

    @property
    def alias_in_arg(self) -> list[Observation]:
        return [o for o in self.observations if o.alias_in_arg]


def _mentions_alias(
    tes: tuple[ast.TypeExpr, ...] | None, aliases: object,
) -> bool:
    """Does any ARGUMENT (at any depth, pre-resolution) name an alias?

    The population that makes this differential meaningful: an
    alias-mentioning argument is precisely where the six renderings
    disagreed.
    """
    stack = list(tes or ())
    while stack:
        te = stack.pop()
        if isinstance(te, ast.NamedType):
            if te.name in aliases:  # type: ignore[operator]
                return True
            stack.extend(te.type_args or ())
        elif isinstance(te, ast.RefinementType):
            stack.append(te.base_type)
        elif isinstance(te, ast.FnType):
            stack.extend(te.params)
            stack.append(te.return_type)
    return False


@contextlib.contextmanager
def _record(origin: str, sweep: Sweep) -> Iterator[None]:
    """Instrument the checker's two naming entry points for the duration.

    ``_slot_ref_key`` routes through ``_slot_type_name``, so slot REFERENCES
    are covered by the same instrumentation as the binding side — the two
    sides being keyed identically is the property that matters.
    """
    had_key = "_slot_type_name" in TypeChecker.__dict__
    orig_te = TypeChecker._type_expr_to_slot_name
    orig_key = TypeChecker._slot_type_name

    def _module_side(
        self: TypeChecker, te: ast.TypeExpr,
        args: tuple[ast.TypeExpr, ...] | None, entry: str, legacy: str,
    ) -> None:
        env = naming.alias_env_from_environment(self.env)
        try:
            module = naming.slot_name(te, env)
        except Exception as exc:  # noqa: BLE001 — a raise IS a divergence
            module = f"<raised {type(exc).__name__}: {exc}>"
        sweep.observations.append(Observation(
            origin=origin,
            entry=entry,
            legacy=legacy,
            module=module,
            env_aliases=len(env.aliases),
            alias_in_arg=_mentions_alias(args, env.aliases),
            shape=ast.format_type_expr(te)
            if isinstance(te, (ast.NamedType, ast.RefinementType, ast.FnType))
            else repr(te),
        ))

    def te_patch(self: TypeChecker, te: ast.TypeExpr) -> str:
        legacy = orig_te(self, te)
        args = te.type_args if isinstance(te, ast.NamedType) else None
        _module_side(self, te, args, "_type_expr_to_slot_name", legacy)
        return legacy

    def key_patch(
        self: TypeChecker, type_name: str,
        type_args: tuple[ast.TypeExpr, ...] | None,
    ) -> str:
        legacy = orig_key(self, type_name, type_args)
        te = ast.NamedType(name=type_name, type_args=type_args)
        _module_side(self, te, type_args, "_slot_type_name", legacy)
        return legacy

    TypeChecker._type_expr_to_slot_name = te_patch  # type: ignore[method-assign]
    TypeChecker._slot_type_name = key_patch  # type: ignore[method-assign]
    try:
        yield
    finally:
        TypeChecker._type_expr_to_slot_name = orig_te  # type: ignore[method-assign]
        if had_key:
            TypeChecker._slot_type_name = orig_key  # type: ignore[method-assign]
        else:
            del TypeChecker._slot_type_name


def _sweep_source(origin: str, source: str, sweep: Sweep) -> None:
    """Parse + check one program with the naming entry points instrumented.

    A parse failure contributes nothing and is counted.  A CHECK failure
    still contributes every observation recorded before it — naming runs
    while diagnostics accumulate, so a rejected program exercises the
    renderer too (and disproportionately often on the malformed shapes the
    corners live in).
    """
    sweep.files_seen.append(origin)
    try:
        program = parse_to_ast(source)
    except Exception:  # noqa: BLE001 — any parse failure, by design
        sweep.parse_skipped.append(origin)
        return
    checker = TypeChecker(source=source, file=origin)
    with _record(origin, sweep):
        with contextlib.suppress(Exception):
            checker.check_program(program)


# =====================================================================
# The inline battery — the corners a corpus does not reliably contain
# =====================================================================

_BATTERY_PRELUDE = """\
type MyAlias = Int;
type A2 = MyAlias;
type Txt = String;
type Count = Nat;
type Box<T> = Option<T>;
type Pair<A, B> = Map<A, B>;
type Pos = { @Int | @Int.0 > 0 };
type PosT<T> = { @T | true };
type Composite = Option<Int>;
type Boxed = Box<MyAlias>;
type Cyc1 = Cyc2;
type Cyc2 = Cyc1;
type Fwd = Later;
type Later = Int;
type Mapper = fn(Int -> Int) effects(pure);
data Wrap<T> { MkWrap(T) }
"""

_BATTERY: tuple[tuple[str, str], ...] = (
    ("alias_head", """\
public fn b1(@MyAlias -> @MyAlias)
  requires(true)
  ensures(true)
  effects(pure)
{
  @MyAlias.0
}
"""),
    ("alias_in_arg", """\
public fn b2(@Option<MyAlias> -> @Option<MyAlias>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<MyAlias>.0
}
"""),
    ("alias_chain_in_arg", """\
public fn b3(@Option<A2> -> @Option<A2>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<A2>.0
}
"""),
    ("nested_alias_in_arg", """\
public fn b4(@Array<Option<A2>> -> @Array<Option<A2>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Option<A2>>.0
}
"""),
    ("parameterised_alias", """\
public fn b5(@Box<MyAlias> -> @Box<MyAlias>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Box<MyAlias>.0
}
"""),
    ("parameterised_alias_in_arg", """\
public fn b6(@Option<Box<Txt>> -> @Option<Box<Txt>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<Box<Txt>>.0
}
"""),
    ("multi_param_alias", """\
public fn b7(@Pair<Txt, MyAlias> -> @Pair<Txt, MyAlias>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pair<Txt, MyAlias>.0
}
"""),
    ("alias_arity_mismatch", """\
public fn b8(@Option<Box> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("refined_alias_in_arg", """\
public fn b9(@Option<Pos> -> @Option<Pos>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<Pos>.0
}
"""),
    ("parameterised_refined_alias", """\
public fn b10(@Option<PosT<MyAlias>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("refinement_over_alias_base", """\
public fn b11(@{ @Array<Txt> | array_length(@Array<Txt>.0) > 0 } -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("fn_type_param_and_arg", """\
public fn b12(@fn(MyAlias -> Txt) effects(pure), @Option<Mapper> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("fn_type_arg_effect_row", """\
public fn b13(@Option<fn(Int -> Int) effects(<State<Count>, IO>)> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("forall_shadowing_alias", """\
public forall<MyAlias> fn b14(@Option<MyAlias>, @MyAlias -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("forall_plain_var", """\
public forall<T> fn b15(@Option<T>, @Wrap<T> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("cycle_and_forward_refs", """\
public fn b16(@Option<Cyc1>, @Option<Fwd>, @Option<Later> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("removed_and_opaque_builtins", """\
public fn b17(
  @Option<Float>,
  @Option<Decimal>,
  @Option<Decimal<Int>>,
  @Decimal<Txt>,
  @Decimal
  -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""),
    ("let_bindings_and_composites", """\
public fn b18(@Array<MyAlias> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<A2> = None;
  let @Composite = None;
  let @Boxed = None;
  1
}
"""),
    ("match_over_alias_adt", """\
public fn b19(@Wrap<MyAlias> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Wrap<MyAlias>.0 {
    MkWrap(@MyAlias) -> @MyAlias.0
  }
}
"""),
    ("state_handler_alias_cell", """\
public fn b20(@Unit -> @Count)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Count>](@Count = 0) {
    get(@Unit) -> { resume(@Count.0) },
    put(@Count) -> { resume(()) }
  } in {
    put(1);
    get(())
  }
}
"""),
    ("closure_over_alias", """\
public fn b21(@Array<MyAlias> -> @Array<MyAlias>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(
    @Array<MyAlias>.0,
    fn(@MyAlias -> @MyAlias) effects(pure) { @MyAlias.0 }
  )
}
"""),
    ("wide_alias_argument_surface", """\
public fn b23(
  @Option<MyAlias>,
  @Option<A2>,
  @Option<Txt>,
  @Option<Count>,
  @Option<Composite>,
  @Option<Boxed>,
  @Array<Box<Txt>>,
  @Map<Txt, Count>,
  @Wrap<A2>
  -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Pos> = None;
  let @Array<Option<MyAlias>> = [];
  let @Map<MyAlias, Txt> = map_new();
  1
}
"""),
    ("where_helper_alias_args", """\
public fn b22(@Option<Txt> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  inner(@Option<Txt>.0)
}
where {
  fn inner(@Option<Txt> -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    1
  }
}
"""),
)


def _battery_sources() -> list[tuple[str, str]]:
    return [(f"<battery:{name}>", _BATTERY_PRELUDE + body)
            for name, body in _BATTERY]


# =====================================================================
# The sweep (session-scoped: parse + check only, no verify/compile)
# =====================================================================

@pytest.fixture(scope="module")
def sweep() -> Sweep:
    result = Sweep()
    for origin, source in _battery_sources():
        _sweep_source(origin, source, result)
    for directory in _CORPUS_DIRS:
        for path in sorted(directory.rglob("*.vera")):
            _sweep_source(
                str(path.relative_to(_ROOT)),
                path.read_text(encoding="utf-8"),
                result,
            )
    return result


def test_no_divergence_across_the_corpus(sweep: Sweep) -> None:
    """THE gate: every name the checker renders, the module renders too."""
    diverged = sweep.divergences
    report = "\n".join(
        f"  {o.origin} [{o.entry}] {o.shape}: "
        f"checker={o.legacy!r} module={o.module!r}"
        for o in diverged[:25]
    )
    assert not diverged, (
        f"{len(diverged)} of {len(sweep.observations)} renderings diverge "
        f"from the checker:\n{report}"
    )


def test_corpus_sweep_is_not_vacuous(sweep: Sweep) -> None:
    """Floors, so the gate cannot pass by observing nothing interesting.

    A differential that records ten trivial ``Int`` renderings proves
    nothing; these are the populations that make it evidence.  If the corpus
    stops reaching a floor, extend the inline battery rather than lowering
    the number.
    """
    assert len(sweep.observations) > 2000, len(sweep.observations)
    assert len(sweep.with_aliases) > 200, len(sweep.with_aliases)
    assert len(sweep.alias_in_arg) >= 40, len(sweep.alias_in_arg)
    # Both entry points must actually be exercised — `_slot_ref_key` routes
    # through `_slot_type_name`, so this is also the reference-side cover.
    entries = {o.entry for o in sweep.observations}
    assert entries == {"_type_expr_to_slot_name", "_slot_type_name"}, entries


def test_corpus_is_almost_entirely_parseable(sweep: Sweep) -> None:
    """A silently-shrinking corpus is the other way this goes vacuous."""
    assert len(sweep.files_seen) > 500, len(sweep.files_seen)
    assert len(sweep.parse_skipped) <= 10, sweep.parse_skipped


def test_inline_battery_reaches_the_alias_corners(sweep: Sweep) -> None:
    """The battery is what pins the corners in place if the corpus drifts."""
    battery = [o for o in sweep.observations
               if o.origin.startswith("<battery:")]
    assert len(battery) > 100, len(battery)
    assert sum(1 for o in battery if o.alias_in_arg) >= 40
    # The corners themselves, by rendered shape.
    rendered = {o.legacy for o in battery}
    assert "Option<Int>" in rendered          # alias resolved in argument
    assert "Option<{@Int | ...}>" in rendered  # refinement, elided
    assert "Fn" in rendered                    # function type at top level
    assert "Option<?>" in rendered             # arity mismatch / removed
    assert any(r.startswith("Option<fn(") for r in rendered)


def test_differential_gate_detects_divergence() -> None:
    """The gate can go RED: perturb the module renderer, see it reported.

    Without this, a green differential is equally consistent with "the
    harness records nothing it compares".
    """
    source = _BATTERY_PRELUDE + _BATTERY[1][1]
    clean = Sweep()
    _sweep_source("<probe>", source, clean)
    assert clean.observations
    assert not clean.divergences

    original = naming.slot_name

    def perturbed(te: ast.TypeExpr, env: naming.AliasEnv) -> str:
        return original(te, env) + "$MUTANT"

    perturbed_sweep = Sweep()
    naming.slot_name = perturbed  # type: ignore[assignment]
    try:
        _sweep_source("<probe>", source, perturbed_sweep)
    finally:
        naming.slot_name = original  # type: ignore[assignment]

    assert len(perturbed_sweep.observations) == len(clean.observations)
    assert len(perturbed_sweep.divergences) == len(
        perturbed_sweep.observations)
    assert all(o.module.endswith("$MUTANT")
               for o in perturbed_sweep.divergences)
    # ...and the checker itself was unaffected by the perturbation: the
    # instrumentation returns the legacy result either way.
    assert ([o.legacy for o in perturbed_sweep.observations]
            == [o.legacy for o in clean.observations])
