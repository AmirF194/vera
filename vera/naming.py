"""The ONE renderer for slot names, slot-reference keys, and cell families.

Six subsystems used to answer the question "what is the name of this type
expression?" independently, and disagreed about aliases; the disagreements
are the #1208 / #1209 bug class, where a name minted one way and looked up
another silently misses and the miss reads as "not statically known".

Every slot name and every slot-reference key now comes from here, on the
BIND side and the REFERENCE side together: the checker's two naming entry
points, the monomorphizer's De Bruijn recount, codegen (parameters, ``let``
and match binders, closure captures, handler clause scopes, refinement
guards, slot references), the verifier, the SMT layer, the tester, and
``vera check --explain-slots``.  They move together by construction, because
there is one function of one environment.

The State/Exn cell FAMILY renders here too (:func:`family_name`, #1209):
one cell per checker is one cell per codegen, so a composite alias joins
the family its resolution names instead of minting a second one.

TWO derivations deliberately stay behind in :mod:`vera.slots`, and both are
about a type's REPRESENTATION rather than about naming anything:
:func:`~vera.slots.type_expr_slot_name` answers the alias-opaque syntactic
spelling for the WASM width / erasure walks and the structural-``Eq``
derivability oracle, and :func:`~vera.slots.family_fallback_name` supplies
the name a family falls back on when its type expression has no nameable
family at all.  Nothing else derives a name of its own: codegen's refinement
boundary guard consumed the last copy — :func:`refinement_binder_parts` — in
#1208 review, and layers only its erasure and E618 decisions on top.

THE RULE, and this module implements exactly it, is **the checker's current
rendering** — because the checker's rendering is what the binding table is
keyed by, so everything downstream must match it or it matches nothing:

* the top-level HEAD is syntactic (alias-opaque): a parameter declared
  ``@MyAlias`` renders ``MyAlias``, never ``Int``;
* type ARGUMENTS are fully resolved: ``@Option<MyAlias>`` where
  ``type MyAlias = Int`` renders ``Option<Int>``;
* a refinement at top level renders its base; in argument position it
  renders the predicate-elided ``{@Int | ...}`` form;
* a function type renders ``Fn`` at top level, and its full
  ``fn(...) effects(...)`` spelling (effect row SORTED) in argument
  position;
* every renderer is TOTAL — an unresolvable type renders ``?``, matching
  the checker's ``UnknownType``, and none of them raise, at any input the
  parser accepts.  Totality is a property to defend, not to assume: alias
  resolution is ITERATIVE, ONE dependency at a time (see
  :func:`_resolve_alias`), precisely because a recursive descent raised
  ``RecursionError`` on a legal 340-hop alias chain — and because resolving
  a whole pending list at once merely moved the recursion onto a
  sibling-shaped alias graph, which raised it again.  The alias branch also
  checks ``env.aliases`` membership so an environment carrying an index
  without a body falls through rather than raising.

Argument resolution is done by rebuilding the checker's own semantic
:class:`~vera.types.Type` and handing it to the checker's own
:func:`~vera.types.pretty_type`, rather than by re-implementing the
rendering; :func:`slot_name` reaches it through :func:`type_arg_name` so
there is one per-argument answer rather than two compositions of the same
steps.  Only the ``Head<a, b>`` JOIN is restated here, and the differential
in ``tests/test_slot_naming_differential.py`` compares against
``canonical_type_name`` directly, so a drift in the separator or the
bracketing goes red across the whole corpus.  Byte-identity with the checker
is therefore structural, not a coincidence to be maintained.

One renderer is only half the contract; the other half is the ENVIRONMENT it
is handed, and getting that wrong fails exactly as silently.  Two rules:

An :class:`AliasEnv` is MODULE-scoped (spec §8.4.1), so every consumer must
render a type expression against the env of the module that DECLARED the
enclosing function — codegen's ``_module_alias_scope``-current env, the
clone's ORIGIN module env in the monomorphizer, the verifier's own
per-module registration (``ContractVerifier._module_alias_envs``, which is
also what an IMPORTED callee's contract renders against).  Rendering against
a neighbouring module's namespace is the same failure as rendering with a
different renderer.

And a ``forall`` variable SHADOWS a same-named module alias for the whole
signature and body it is declared over — the checker binds it before it
binds any slot — so a function-scoped type expression renders against the
module env NARROWED by :func:`~vera.slots.fn_slot_scope`, accumulating a
``where`` helper's ancestors' variables as well as its own.  Un-narrowed,
``forall<T> fn f(@Option<T>, @Option<Int>)`` under ``type T = Int`` collapses
two parameter stacks the checker keeps apart, and every reference into them
resolves onto the wrong parameter.

Alias visibility follows the checker's REGISTRATION ORDER: an alias body is
resolved against only the aliases declared before it, exactly as
``_register_alias`` resolves each alias against the table as it stood at
that point.  A forward reference (``type A = B;`` before ``type B = Int;``)
therefore stays opaque as ``B``, and a cycle (``type A = B; type B = A;``)
terminates with the same placeholder the checker produces rather than
looping — the ordering restriction is well-founded by construction, and it
is what makes the iterative resolution's dependency graph a DAG.
"""

from __future__ import annotations

import re
import sys
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field

from vera import ast
from vera.types import (
    PRIMITIVES,
    REMOVED_ALIASES,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    pretty_type,
    substitute,
)

__all__ = [
    "EMPTY_ALIAS_ENV",
    "AliasEnv",
    "RefinementBinder",
    "alias_env_from_environment",
    "family_name",
    "is_ref_spellable",
    "refinement_binder_parts",
    "resolve_type_expr",
    "slot_name",
    "slot_name_or_none",
    "slot_ref_key",
    "type_arg_name",
    "with_type_params",
]


# =====================================================================
# The naming environment
# =====================================================================

@dataclass(frozen=True)
class AliasEnv:
    """The module-scoped naming context: aliases plus type params in scope.

    Vera's alias namespace is MODULE-scoped (spec §8.4.1), so one of these
    describes one module's view.  *aliases* maps an alias name to its
    SYNTACTIC body (``TypeAliasInfo.body``, #1208) in DECLARATION ORDER —
    the order is load-bearing, see the module docstring.  *alias_params* is
    the same key set mapped to each alias's declared type parameters
    (``None`` for a non-parameterised alias).  *type_params* is the set of
    type-variable names in scope at the point being rendered; a type
    parameter SHADOWS a same-named alias, which is why it is tested first.
    *data_types* maps each declared ADT name to its DECLARATION INDEX, in the
    same shared index space as ``_order`` (#1208).  An ADT matters to naming
    only because a user ADT may take a name the resolver otherwise treats
    specially — and whether it does so depends on where it was declared
    relative to the alias body asking, hence the index rather than a flat
    set; see :func:`_resolve_named`.  A built-in ADT carries ``-1``: it
    precedes every user declaration and is therefore always visible.
    """

    aliases: Mapping[str, ast.TypeExpr]
    alias_params: Mapping[str, tuple[str, ...] | None]
    type_params: frozenset[str] = frozenset()
    data_types: Mapping[str, int] = field(default_factory=dict)
    # Alias name -> declaration index, so an alias body can be resolved
    # against only the declarations that precede it.  Shares ONE index space
    # with ``data_types``, which is what lets the bound order the two
    # registries against each other.  Also the per-env memo of
    # already-resolved alias bodies (an alias's restricted resolution is
    # fixed, so it is computed at most once).
    _order: Mapping[str, int] = field(
        default_factory=dict, repr=False, compare=False)
    _memo: dict[str, Type] = field(
        default_factory=dict, repr=False, compare=False)

    def __post_init__(self) -> None:
        if not self._order:
            object.__setattr__(
                self, "_order",
                {name: i for i, name in enumerate(self.aliases)},
            )


EMPTY_ALIAS_ENV = AliasEnv(aliases={}, alias_params={})
"""The alias-free environment.

Legitimate ONLY where the caller can show no alias can be in scope — a
rendering of built-in / synthesized type expressions that never came from
user source.  Every use must be able to state that argument: reaching for
this constant because an environment is inconvenient to thread is exactly
the "renders one way, is looked up another" failure #1208 exists to close,
and it fails SILENTLY (an alias renders opaquely, the key misses).
"""


def alias_env_from_environment(env: object) -> AliasEnv:
    """Build the naming env from a live checker/verifier ``Environment``.

    Reads the syntactic bodies recorded by ``_register_alias``
    (``TypeAliasInfo.body``, #1208).  An entry whose body is ``None`` — a
    ``TypeAliasInfo`` built by some future path that has no TypeExpr in hand
    — is OMITTED rather than guessed at, so it renders opaquely (the
    conservative direction: an opaque head is what the checker produces for
    an unknown name anyway).  ``env.type_params`` supplies the shadowing set
    and ``env.data_types`` the declared-ADT set, so the result reflects the
    checker's state at the moment it is called, mid-check type parameters
    included.
    """
    aliases: dict[str, ast.TypeExpr] = {}
    alias_params: dict[str, tuple[str, ...] | None] = {}
    order: dict[str, int] = {}
    type_aliases = getattr(env, "type_aliases", {})
    for name, info in type_aliases.items():
        body = getattr(info, "body", None)
        if body is None:
            continue
        aliases[name] = body
        alias_params[name] = getattr(info, "type_params", None)
        order[name] = getattr(info, "decl_index", -1)
    data_types = {
        name: getattr(info, "decl_index", -1)
        for name, info in getattr(env, "data_types", {}).items()
    }
    return AliasEnv(
        aliases=aliases,
        alias_params=alias_params,
        type_params=frozenset(getattr(env, "type_params", {})),
        data_types=data_types,
        _order=order,
    )


def with_type_params(env: AliasEnv, params: Iterable[str]) -> AliasEnv:
    """*env* with *params* added to the shadowing set.

    A type parameter shadows a same-named alias for the whole scope it is
    declared over (a ``forall<T>`` signature, an alias's own parameters), so
    entering such a scope means extending the env, never mutating it.
    """
    return AliasEnv(
        aliases=env.aliases,
        alias_params=env.alias_params,
        type_params=env.type_params | frozenset(params),
        data_types=env.data_types,
        _order=env._order,
        _memo=env._memo,
    )


# =====================================================================
# Resolution — the checker's `_resolve_type`, as a pure function
# =====================================================================

_UNBOUNDED = sys.maxsize
"""The visibility bound for a rendering that is NOT inside an alias body.

The checker resolves a parameter's type expression after registration has
finished, so every declaration is in scope; only an alias BODY is bounded,
and only by its own declaration index.  A sentinel rather than
``len(env.aliases)``, because the index space is shared with the ADTs and so
runs past the alias count.
"""


def resolve_type_expr(te: ast.TypeExpr, env: AliasEnv) -> Type:
    """Resolve *te* to the semantic :class:`~vera.types.Type` the checker's
    ``_resolve_type`` would produce for it.

    Clause of THE RULE: this is the ARGUMENT-position resolution — full
    alias resolution, refinements preserved as :class:`RefinedType`, an
    unresolvable type expression as :class:`UnknownType` (renders ``?``).
    Total: it reports no diagnostics and raises nothing, where the checker
    would additionally emit E133 / E134 / E135 and return the same type.
    """
    return _resolve(te, env, env.type_params, _UNBOUNDED)


def _resolve(
    te: ast.TypeExpr,
    env: AliasEnv,
    type_params: frozenset[str],
    limit: int,
) -> Type:
    """``_resolve_type`` with the alias-visibility bound *limit* (only
    aliases whose declaration index is ``< limit`` are in scope) and an
    explicit *type_params* set (an alias body sees its OWN parameters, not
    the caller's — matching the ``saved_params`` swap in
    ``_register_alias``)."""
    if isinstance(te, ast.NamedType):
        return _resolve_named(te, env, type_params, limit)
    if isinstance(te, ast.FnType):
        params = tuple(_resolve(p, env, type_params, limit) for p in te.params)
        ret = _resolve(te.return_type, env, type_params, limit)
        eff = _resolve_effect_row(te.effect, env, type_params, limit)
        return FunctionType(params, ret, eff)
    if isinstance(te, ast.RefinementType):
        return RefinedType(
            _resolve(te.base_type, env, type_params, limit), te.predicate)
    return UnknownType()


def _resolve_named(
    te: ast.NamedType,
    env: AliasEnv,
    type_params: frozenset[str],
    limit: int,
) -> Type:
    """``_resolve_named_type``'s branch order, exactly.

    Type parameter (SHADOWS everything) -> primitive -> alias (arity-checked,
    substituted) -> DECLARED ADT -> ``Decimal`` (opaque, arguments dropped)
    -> removed alias (``?``) -> opaque ADT.  The checker's built-in-container
    branch (``Array``/``Tuple``/``Map``/``Set``) is absorbed by the last one:
    it builds ``AdtType(name, args)`` from the same resolved arguments, and
    its extra work is E135 diagnostics, which naming does not emit.

    The declared-ADT branch, by contrast, is NOT absorbable, and it must sit
    exactly where the checker puts it — ahead of the ``Decimal`` and removed
    -alias branches.  A user may declare ``data Float`` or ``data Decimal``
    (both check clean), and for those the checker takes the ADT branch first:
    ``@Option<Float>`` renders ``Option<Float>``, not ``Option<?>``, and a
    user ``Decimal`` keeps its type arguments (``Option<Decimal<Int>>``)
    instead of having them dropped by the built-in ``Decimal`` branch.

    ADT visibility is bounded by declaration index exactly as alias
    visibility is, because the two registries share ONE index space (#1208).
    ``type M = Decimal;`` declared ABOVE ``data Decimal`` resolved, at
    registration time, against a table that did not yet hold the ADT — so the
    built-in ``Decimal`` branch is what the checker took, and what is taken
    here.  Declared below it, the ADT branch wins on both sides.  The bound
    only ever matters for an ADT named after a removed alias or a built-in in
    the first place; every other ADT reaches the same opaque ``AdtType``
    whichever branch it takes.
    """
    name = te.name
    if name in type_params:
        # `env.type_params` maps every name to `TypeVar(name)`.
        return TypeVar(name)
    if name in PRIMITIVES and not te.type_args:
        return PRIMITIVES[name]
    idx = env._order.get(name)
    # ``name in env.aliases`` is what makes the branch TOTAL: the two maps
    # agree for every environment this module builds, but an env assembled
    # elsewhere with an ``_order`` entry and no body must fall through to the
    # ADT branch rather than raise.
    if idx is not None and idx < limit and name in env.aliases:
        params = env.alias_params.get(name) or ()
        n_supplied = len(te.type_args) if te.type_args else 0
        if n_supplied != len(params):
            return UnknownType()  # checker: E133, then UnknownType
        body = _resolve_alias(name, env)
        if te.type_args and params:
            args = tuple(
                _resolve(a, env, type_params, limit) for a in te.type_args)
            return substitute(body, dict(zip(params, args)))
        return body
    adt_idx = env.data_types.get(name)
    if adt_idx is None or adt_idx >= limit:
        if name == "Decimal":
            return AdtType("Decimal", ())  # checker: E134 when args supplied
        if name in REMOVED_ALIASES:
            return UnknownType()
    return AdtType(name, tuple(
        _resolve(a, env, type_params, limit) for a in te.type_args
    ) if te.type_args else ())


def _mentioned_names(te: ast.TypeExpr, out: list[str]) -> None:
    """Every type NAME written anywhere in *te*, deliberately over-approximated.

    Used only to order alias resolution (see :func:`_resolve_alias`), never to
    decide a rendering — so it collects names a resolution would skip (a
    shadowing type parameter, an arity mismatch, a primitive) rather than
    re-deciding :func:`_resolve_named`'s branch order.  Over-approximating is
    what keeps it from drifting: resolving one extra alias early is inert,
    since an alias's own resolution does not depend on who asked for it.
    """
    if isinstance(te, ast.NamedType):
        out.append(te.name)
        for arg in te.type_args or ():
            _mentioned_names(arg, out)
    elif isinstance(te, ast.FnType):
        for param in te.params:
            _mentioned_names(param, out)
        _mentioned_names(te.return_type, out)
        if isinstance(te.effect, ast.EffectSet):
            for ref in te.effect.effects:
                for arg in getattr(ref, "type_args", None) or ():
                    _mentioned_names(arg, out)
    elif isinstance(te, ast.RefinementType):
        _mentioned_names(te.base_type, out)


def _resolve_alias(name: str, env: AliasEnv) -> Type:
    """The alias's registration-time ``resolved_type``, recomputed.

    Resolved against only the aliases DECLARED BEFORE it and with only its
    own type parameters in scope — the state ``_register_alias`` had when it
    resolved that body.  The strictly-decreasing visibility bound makes the
    resolution well-founded, so a cyclic or forward-referencing alias
    terminates on the opaque placeholder the checker also produces.

    ITERATIVE, dependency-first, because the chain length is the user's to
    choose and the checker's is O(1) per hop (it stores each alias's
    ``resolved_type`` at registration).  A recursive descent spent Python
    frames per hop and died on a legal program — ``type A1 = A0; type A2 =
    A1; …`` at ~340 hops raised an uncaught ``RecursionError`` from inside a
    renderer this module's docstring calls TOTAL (#1208 review, probe
    ``d01_deep_chain``).  Every alias a body mentions has a strictly smaller
    declaration index, so the mention graph is a DAG.

    ONE dependency is pushed per iteration, and that is the load-bearing
    detail rather than a stylistic one.  Pushing a body's whole pending list
    at once puts SIBLINGS in progress together, and the ``in_progress`` guard
    below then FILTERS a sibling that is also a real dependency — so the body
    is resolved with that sibling still unmemoized and ``_resolve`` reaches it
    through a nested ``_resolve_alias``, one Python frame per level.  ``type
    Bk = D(k-1); type Ck = Drop<Bk>; type Dk = Drop2<Bk, Ck>;`` is that shape,
    and it raised ``RecursionError`` from the same renderer at a few hundred
    levels (#1208 round-2 review, probe ``sib_300``).  Pushing one at a time
    leaves only this walk's ANCESTORS in progress, and an ancestor can never
    be a pending dependency (its index is strictly larger), so nothing is ever
    filtered: by the time a body is resolved every alias it mentions is in the
    memo, and the ``_resolve_alias`` calls underneath it return from the memo
    without recursing.  The Python nesting is therefore ONE frame below this
    one, whatever the chain length — the depth of the ``_resolve`` walk itself
    stays bounded by the alias body's own syntactic nesting.

    Equivalence with the checker is preserved exactly — this is an evaluation
    ORDER, not a depth bound, so a long chain still renders its real
    resolution rather than a truncated ``?``.
    """
    memo = env._memo
    cached = memo.get(name)
    if cached is not None:
        return cached
    stack: list[str] = [name]
    # Exactly this walk's ancestors — see the docstring.  Defence in depth,
    # and provably inert on any environment this module builds: the visibility
    # bound strictly decreases along a dependency edge, so an ancestor's index
    # is strictly larger than every pending dependency's and can never be one
    # of them.  Should that invariant ever be broken, skipping an in-progress
    # name terminates on the same opaque placeholder the checker produces
    # instead of spinning.
    in_progress: set[str] = {name}
    while stack:
        cur = stack[-1]
        if cur in memo:
            in_progress.discard(cur)
            stack.pop()
            continue
        limit = env._order[cur]
        mentioned: list[str] = []
        _mentioned_names(env.aliases[cur], mentioned)
        pending = next((
            ref for ref in mentioned
            if ref not in memo
            and ref not in in_progress
            and ref in env.aliases
            and env._order.get(ref, _UNBOUNDED) < limit
        ), None)
        if pending is not None:
            # ONE at a time, so only ancestors are ever in progress and no
            # real dependency is filtered.  Strictly smaller indices, so the
            # stack cannot cycle and each alias is resolved at most once
            # (a later push hits the memo).
            stack.append(pending)
            in_progress.add(pending)
            continue
        memo[cur] = _resolve(
            env.aliases[cur], env,
            frozenset(env.alias_params.get(cur) or ()), limit)
        in_progress.discard(cur)
        stack.pop()
    return memo[name]


def _resolve_effect_row(
    er: ast.EffectRow,
    env: AliasEnv,
    type_params: frozenset[str],
    limit: int,
) -> EffectRowType:
    """``_resolve_effect_row``, as a pure function.

    An effect name that is a type parameter in scope is the row VARIABLE
    (effect polymorphism), not an instance.  The rendering
    (:func:`~vera.types.pretty_effect`, reached through ``pretty_type`` on a
    ``FunctionType``) sorts the instances, so a row renders identically
    across hash seeds.
    """
    if isinstance(er, ast.EffectSet):
        instances: list[EffectInstance] = []
        row_var: str | None = None
        for ref in er.effects:
            if isinstance(ref, ast.EffectRef):
                if ref.name in type_params:
                    row_var = ref.name
                    continue
                instances.append(EffectInstance(ref.name, tuple(
                    _resolve(a, env, type_params, limit) for a in ref.type_args
                ) if ref.type_args else ()))
            elif isinstance(ref, ast.QualifiedEffectRef):
                instances.append(EffectInstance(
                    f"{ref.module}.{ref.name}", tuple(
                        _resolve(a, env, type_params, limit)
                        for a in ref.type_args
                    ) if ref.type_args else ()))
        return ConcreteEffectRow(frozenset(instances), row_var)
    return PureEffectRow()


# =====================================================================
# The renderers
# =====================================================================

def slot_name(te: ast.TypeExpr, env: AliasEnv) -> str:
    """THE renderer: the slot-matching name of a parameter type expression.

    Clause of THE RULE: SYNTACTIC head, RESOLVED arguments.  A named type
    with no arguments renders as itself (an alias stays opaque — ``@PosInt``
    counts ``PosInt`` bindings, not ``Int``); with arguments it renders
    ``Head<arg, arg>`` where each argument goes through
    :func:`type_arg_name`.  A refinement renders its base's name; a function
    type renders the synthetic ``Fn``; anything else renders ``?``.  Total.
    """
    if isinstance(te, ast.NamedType):
        if te.type_args:
            # Each argument through :func:`type_arg_name`, then the checker's
            # own join shape (``Head<a, b>``, ", "-separated).  Routed through
            # the argument renderer rather than handing resolved
            # :class:`~vera.types.Type` values straight to
            # ``canonical_type_name``, so the two ways of asking "what does
            # this type argument render as?" are ONE way — the docstring
            # below promised that composition and it has to be real.  The join
            # is the only thing restated here, and it cannot drift silently:
            # the corpus differential's reference side calls
            # ``canonical_type_name`` directly, so a divergence in either the
            # separator or the bracketing goes red across every parameterised
            # rendering in the corpus.
            return "{}<{}>".format(
                te.name,
                ", ".join(type_arg_name(a, env) for a in te.type_args),
            )
        return te.name
    if isinstance(te, ast.RefinementType):
        return slot_name(te.base_type, env)
    if isinstance(te, ast.FnType):
        return "Fn"
    return "?"


def slot_name_or_none(te: ast.TypeExpr, env: AliasEnv) -> str | None:
    """:func:`slot_name`, with the unnameable ``?`` reported as ``None``.

    The subsystems downstream of the checker carry a ``str | None`` naming
    contract and branch on ``None`` to skip (a ``CodegenSkip``, an untranslated
    SMT term).  ``?`` is the checker's ``UnknownType`` rendering — a type
    expression the checker could not resolve either — so it is the one
    rendering that should still take those branches.  Everything else now
    HAS a name, including the shapes the pre-#1208 syntactic builder gave up
    on (a function type nested in a type argument): the checker binds those,
    so binding them here is what makes the two sides agree.
    """
    name = slot_name(te, env)
    return None if name == "?" else name


def type_arg_name(te: ast.TypeExpr, env: AliasEnv) -> str:
    """The ARGUMENT-position rendering of a type expression.

    Clause of THE RULE: fully resolved, then rendered by the checker's own
    :func:`~vera.types.pretty_type` — so a refinement renders its
    predicate-elided ``{@Int | ...}`` form, a function type its full
    ``fn(...) effects(...)`` spelling with a SORTED effect row, and anything
    unresolvable renders ``?``.  This is exactly the per-argument rendering
    :func:`slot_name`'s join performs — literally, since #1208 review:
    ``slot_name`` calls this per argument rather than composing the same two
    steps itself, so the two answers are one answer by construction.
    """
    return pretty_type(resolve_type_expr(te, env))


def slot_ref_key(ref: ast.SlotRef, env: AliasEnv) -> str:
    """The binding-table key a ``@T.n`` reference looks itself up under.

    Clause of THE RULE: identical to :func:`slot_name` over the reference's
    head and arguments — the checker's ``_slot_ref_key`` routes through the
    same renderer as the binding side, and a reference that rendered
    differently from the binding would miss, silently.
    """
    return slot_name(
        ast.NamedType(name=ref.type_name, type_args=ref.type_args), env)


def family_name(
    te: ast.TypeExpr | None, env: AliasEnv, fallback: str,
) -> str:
    """The State/Exn cell FAMILY name for an effect type argument (#1209).

    Clause of THE RULE, and the one place it differs: a family names a CELL,
    not a source spelling, so the head resolves too — ``State<MyAlias>``
    where ``type MyAlias = Option<Int>`` is the ``Option<Int>`` family, the
    same cell ``State<Option<Int>>`` names.  (Scalar aliases already
    collapsed this way, #1205; composite ones splitting the family was
    #1209.)  This mirrors the checker, which resolves effect-instance type
    arguments in full (``_resolve_effect_ref``), so the family agrees with
    the cell type the checker typed.  Refinements collapse to their base —
    ``{@Int | P}`` and ``Int`` are one cell.

    *fallback* is returned when there is no type expression, when the
    resolution has no nameable family (a function type, or an unresolvable
    type), and when the RENDERING is not mangle-safe.  That last gate is
    what keeps the answer usable as a WAT symbol: a family feeds
    ``mangle_type_name``, whose escape covers exactly the canonical
    ``Head<arg, arg>`` grammar :func:`is_ref_spellable` describes, and a
    resolution rendering outside it (``Option<{@Int | ...}>``,
    ``Option<fn(@Int) -> @Int>``) would emit an import name WAT cannot
    parse.  Those keep the alias-opaque spelling, which is the conservative
    direction: it can leave a family split, never merge two cells the
    checker keeps apart.
    """
    if te is None:
        return fallback
    ty = base_type(resolve_type_expr(te, env))
    if isinstance(ty, (FunctionType, UnknownType)):
        return fallback
    name = pretty_type(ty)
    return name if is_ref_spellable(name) else fallback


_IDENT_RE = re.compile(r"[A-Z][A-Za-z0-9_]*")


def _scan_spellable(name: str, i: int) -> int:
    """Consume one ``UPPER_IDENT type_args?`` from *name* at *i*; return the
    end offset, or -1 if it is not that shape."""
    m = _IDENT_RE.match(name, i)
    if m is None:
        return -1
    i = m.end()
    if i < len(name) and name[i] == "<":
        i += 1
        while True:
            i = _scan_spellable(name, i)
            if i < 0:
                return -1
            if name.startswith(", ", i):
                i += 2
                continue
            break
        if i >= len(name) or name[i] != ">":
            return -1
        i += 1
    return i


def is_ref_spellable(name: str) -> bool:
    """Can *name* appear as the type of a ``@Name.n`` slot reference?

    The grammar's slot reference is ``"@" UPPER_IDENT type_args? "." INT``,
    so a spellable name is an upper-initial identifier optionally applied to
    spellable arguments — the shape :func:`~vera.slots.type_expr_slot_name`
    builds and returns non-``None`` for.  ``?`` is never spellable, and
    neither is an argument-position rendering that elides
    (``{@Int | ...}``) or spells a function type — a reference written that
    way could not be parsed, so a name in that shape can only ever dangle.
    The synthetic ``Fn`` IS spellable: ``@Fn.0`` is how a function-typed
    parameter is referenced.
    """
    return _scan_spellable(name, 0) == len(name) and bool(name)


# =====================================================================
# Refinement binders
# =====================================================================

@dataclass(frozen=True)
class RefinementBinder:
    """What a refinement's runtime guard binds its predicate over.

    *predicate* is the guard's predicate, closed over ``@<binder_name>.0``;
    *binder_name* is that binder's slot name; *base* is the alias-chased
    base type expression (the caller decides whether it has a WASM
    representation); *base_is_refinement* flags a refinement whose base
    resolves to another refinement — a shape whose guard would silently drop
    the inner membership predicate, so the caller rejects it (E618).
    """

    predicate: ast.Expr
    binder_name: str
    base: ast.TypeExpr
    base_is_refinement: bool


def refinement_binder_parts(
    te: ast.TypeExpr, env: AliasEnv,
) -> RefinementBinder | None:
    """The binder a refinement's runtime guard uses, or ``None``.

    Clause of THE RULE, and THE derivation both consumers use: chase the
    alias chain (bare-name follows only, cycle-guarded) to a
    ``RefinementType``, then name its base as the predicate's binder.  It was
    a second copy of codegen's ``_refinement_guard_parts`` walk until #1208
    converged them; codegen now calls this and layers its two WASM-specific
    decisions on top (reject a nested refinement base with E618, emit no
    guard for a base that erases), because a type's REPRESENTATION is not a
    naming question and this module must not import the backend.
    ``tests/test_refinement_binder_convergence_1208.py`` is the differential
    that keeps the two from drifting apart again.

    The binder itself is named by :func:`slot_name` (#1208), so the guard
    pushes the value under exactly the key a predicate's ``@Base.n``
    resolves to through :func:`slot_ref_key` — and under the key the checker
    bound the predicate's binder to.  The pre-consolidation derivation named
    the base's type arguments SYNTACTICALLY (``Array<Txt>`` for
    ``type Txt = String``), which met its reference side only because that
    side was syntactic too; with both resolved they meet on
    ``Array<String>``.

    One deliberate difference from :func:`slot_name` remains, because the
    guard and the predicate must agree with each other: the alias chain is
    followed by NAME with no substitution, so a parameterised alias
    application is chased as its head.

    The ``@Nat``/``@Byte`` implicit range predicates are conjoined here, as
    codegen does, so a value satisfying the written predicate but outside
    the base's range cannot launder past the guard.  They are NOT conjoined
    when ``base_is_refinement`` — the caller rejects that shape before it
    would use the predicate.
    """
    node: ast.TypeExpr = te
    seen: set[str] = set()
    while (isinstance(node, ast.NamedType)
           and node.name in env.aliases
           and node.name not in seen):
        seen.add(node.name)
        node = env.aliases[node.name]
    if not isinstance(node, ast.RefinementType):
        return None
    base = node.base_type
    if not isinstance(base, ast.NamedType):
        return None
    name = slot_name(base, env)
    base_node: ast.TypeExpr = base
    bseen: set[str] = set()
    while (isinstance(base_node, ast.NamedType)
           and base_node.name in env.aliases
           and base_node.name not in bseen):
        bseen.add(base_node.name)
        base_node = env.aliases[base_node.name]
    if isinstance(base_node, ast.RefinementType):
        return RefinementBinder(node.predicate, name, base_node, True)
    predicate = node.predicate
    if isinstance(base_node, ast.NamedType) and base_node.name == "Nat":
        predicate = ast.BinaryExpr(
            op=ast.BinOp.AND,
            left=ast.BinaryExpr(
                op=ast.BinOp.GE,
                left=ast.SlotRef(type_name=name, type_args=None, index=0),
                right=ast.IntLit(value=0),
            ),
            right=predicate,
        )
    elif isinstance(base_node, ast.NamedType) and base_node.name == "Byte":
        slot = ast.SlotRef(type_name=name, type_args=None, index=0)
        predicate = ast.BinaryExpr(
            op=ast.BinOp.AND,
            left=ast.BinaryExpr(
                op=ast.BinOp.AND,
                left=ast.BinaryExpr(
                    op=ast.BinOp.GE, left=slot, right=ast.IntLit(value=0)),
                right=ast.BinaryExpr(
                    op=ast.BinOp.LE, left=slot, right=ast.IntLit(value=255)),
            ),
            right=predicate,
        )
    return RefinementBinder(predicate, name, base_node, False)
