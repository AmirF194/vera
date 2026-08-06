"""Differential gate: the CHECKER must render what :mod:`vera.naming` renders.

The consolidation in #1208 / #1209 replaces six per-subsystem naming
renderings with one, and takes the checker's rendering as the rule — so the
load-bearing claim is not "the module looks right", it is "the module is
byte-identical to the historical checker rendering on every type expression
the checker names".  A unit suite cannot establish that: the divergences
that caused the bug class live in alias corners nobody thought to enumerate.

WHY THE REFERENCE RENDERING LIVES IN THIS FILE.  Before the delegation
commit, the LEGACY side of each pair was simply the checker's own return
value, and the MODULE side was :func:`vera.naming.slot_name`.  Once the
checker delegates, that comparison is the module against itself and proves
nothing.  So the legacy side is now ``_reference_slot_name`` below: the
historical in-checker composition — syntactic head, arguments through
``checker._resolve_type`` and joined by ``canonical_type_name``, the
refined-top recursion, ``Fn``, ``?`` — rebuilt from checker machinery that
is still live and still used broadly (``_resolve_type`` /
``canonical_type_name`` did not move).  It is deliberately NOT imported from
:mod:`vera.naming`: an independent statement of the rule is what pins the
rule in place, so a future edit to the module has to disagree with a written
-down reference rather than silently re-baseline both sides at once.

This instruments the checker's two naming entry points, runs it over the
whole ``.vera`` corpus (examples, conformance programs and their module
fixtures, and the PR #1202 probe corpus) plus an inline battery aimed at the
alias / refinement / function-type / shadowing corners, and asserts ZERO
divergence across every recorded pair.

The comparison happens AT RECORD TIME against the live
:class:`~vera.environment.Environment`, so each pair sees exactly the alias
table and type-parameter scope the checker had at that instant — mid-check
``forall`` scopes included.  The checker's own result is what is returned to
it, so instrumentation cannot change what the checker computes; the
reference's extra ``_resolve_type`` calls can append duplicate diagnostics,
which nothing here reads.

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
from vera.types import canonical_type_name

_ROOT = Path(__file__).resolve().parent.parent
_CORPUS_DIRS = (
    _ROOT / "examples",
    _ROOT / "tests" / "conformance",
    _ROOT / "tests" / "probes",
)


# =====================================================================
# The harness
# =====================================================================

def _reference_slot_name(checker: TypeChecker, te: ast.TypeExpr) -> str:
    """The historical in-checker rendering, rebuilt from live machinery.

    Byte-for-byte the composition ``TypeChecker._type_expr_to_slot_name``
    carried before it delegated to :mod:`vera.naming`, expressed against the
    parts that stayed in the checker: ``_resolve_type`` (argument-position
    resolution) and ``canonical_type_name`` (the join).  ``_slot_type_name``'s
    historical body was the ``NamedType`` case of this, so one reference
    covers both entry points.

    Kept here, not in ``vera/``, precisely because it is the thing the module
    is being checked AGAINST — see the module docstring.
    """
    if isinstance(te, ast.NamedType):
        if te.type_args:
            resolved = tuple(checker._resolve_type(a) for a in te.type_args)
            return canonical_type_name(te.name, resolved)
        return te.name
    if isinstance(te, ast.RefinementType):
        return _reference_slot_name(checker, te.base_type)
    if isinstance(te, ast.FnType):
        return "Fn"
    return "?"


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

    The MODULE side is what the (delegating) checker returns; the LEGACY side
    is :func:`_reference_slot_name`.  The checker's own value is returned
    unchanged either way, so the program under check behaves as it would
    without the instrumentation.
    """
    had_key = "_slot_type_name" in TypeChecker.__dict__
    orig_te = TypeChecker._type_expr_to_slot_name
    orig_key = TypeChecker._slot_type_name

    def _observe(
        self: TypeChecker, te: ast.TypeExpr,
        args: tuple[ast.TypeExpr, ...] | None, entry: str, module: str,
    ) -> None:
        aliases = naming.alias_env_from_environment(self.env).aliases
        try:
            legacy = _reference_slot_name(self, te)
        except Exception as exc:  # noqa: BLE001 — a raise IS a divergence
            legacy = f"<raised {type(exc).__name__}: {exc}>"
        sweep.observations.append(Observation(
            origin=origin,
            entry=entry,
            legacy=legacy,
            module=module,
            env_aliases=len(aliases),
            alias_in_arg=_mentions_alias(args, aliases),
            shape=ast.format_type_expr(te)
            if isinstance(te, (ast.NamedType, ast.RefinementType, ast.FnType))
            else repr(te),
        ))

    def te_patch(self: TypeChecker, te: ast.TypeExpr) -> str:
        module = orig_te(self, te)
        args = te.type_args if isinstance(te, ast.NamedType) else None
        _observe(self, te, args, "_type_expr_to_slot_name", module)
        return module

    def key_patch(
        self: TypeChecker, type_name: str,
        type_args: tuple[ast.TypeExpr, ...] | None,
    ) -> str:
        module = orig_key(self, type_name, type_args)
        te = ast.NamedType(name=type_name, type_args=type_args)
        _observe(self, te, type_args, "_slot_type_name", module)
        return module

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
    # The data-type branch outranks the `Decimal` / removed-alias branches
    # in the checker's `_resolve_named_type`, so an ADT that takes one of
    # those names changes what its own name renders as.  Declared in the
    # BODY, not the shared prelude, so the other battery entries keep
    # reaching the built-in spellings (`Option<?>`, argument-dropping
    # `Decimal`).  The ADTs are declared ABOVE the aliases that name them —
    # ADT visibility is not declaration-order-bounded here, see
    # `test_adt_visibility_is_not_bounded_by_declaration_order`.
    ("data_type_shadows_special_names", """\
private data Float { MkFl(Int) }
private data Decimal { MkDec(Int) }
private data Array { MkArr(Int) }
type Money = Decimal<Int>;
type Amount = Option<Float>;

public fn b24(
  @Option<Float>,
  @Float,
  @Option<Decimal>,
  @Option<Decimal<Int>>,
  @Decimal<Float>,
  @Option<Array>,
  @Option<Array<MyAlias>>,
  @Option<Money>,
  @Option<Amount>
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


# The declaration-ORDER corner (#1208) needs its own preludes: the whole
# point is where the `data` sits relative to the `type`, so these cannot ride
# the shared prelude.  An ADT named after a built-in special case (`Decimal`)
# or a removed alias (`Float`) is the only shape whose rendering the ordering
# can change, and each is swept in BOTH orders — a visibility bound applied
# in the wrong direction agrees with the checker on one ordering only.
_ORDERING_FN = """\
public fn ord(@Option<{alias}>, @{adt}<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Option<{alias}> = @Option<{alias}>.0;
  1
}}
"""

_ORDERING_BATTERY: tuple[tuple[str, str], ...] = tuple(
    (f"decl_order_{adt.lower()}_{label}", prelude + _ORDERING_FN.format(
        alias="M", adt=adt))
    for adt in ("Decimal", "Float")
    for label, prelude in (
        ("alias_first",
         f"type M = {adt}<Int>;\nprivate data {adt} {{ Mk{adt}(Int) }}\n"),
        ("adt_first",
         f"private data {adt} {{ Mk{adt}(Int) }}\ntype M = {adt}<Int>;\n"),
    )
)


def _battery_sources() -> list[tuple[str, str]]:
    return [(f"<battery:{name}>", _BATTERY_PRELUDE + body)
            for name, body in _BATTERY] + [
        (f"<battery:{name}>", source)
        for name, source in _ORDERING_BATTERY
    ]


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
    # #1208: the declaration-ORDER corner, in both directions.  An ADT
    # declared below the alias that names it is invisible to that body (the
    # built-in `Decimal` branch, arguments dropped; `?` for the removed
    # `Float`); declared above it, the ADT branch wins and keeps them.  A
    # bound applied in one direction only still renders three of these four.
    ordering = {o.legacy for o in sweep.observations
                if o.origin.startswith("<battery:decl_order_")}
    assert {"Option<Decimal>", "Option<Decimal<Int>>",
            "Option<?>", "Option<Float<Int>>"} <= ordering, ordering


def test_differential_gate_detects_divergence() -> None:
    """The gate can go RED: perturb the module renderer, see it reported.

    Without this, a green differential is equally consistent with "the
    harness records nothing it compares".  This is also what keeps the gate
    non-vacuous after the delegation: the perturbation moves the checker's
    answer (it now routes through :func:`vera.naming.slot_name`) while
    ``_reference_slot_name`` — which reaches ``_resolve_type`` and
    ``canonical_type_name`` directly — stands still, so the two sides really
    are two sides.
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
    # ...and the reference side is independent of the module: it renders the
    # same strings whether or not the module is perturbed.
    assert ([o.legacy for o in perturbed_sweep.observations]
            == [o.legacy for o in clean.observations])
    assert not any(o.legacy.endswith("$MUTANT") for o in clean.observations)
