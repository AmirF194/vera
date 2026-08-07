"""Slot resolution tables, and the two walks that are not about naming.

:func:`slot_table` computes a function's slot resolution table from its
parameter type expressions and a module's :class:`~vera.naming.AliasEnv` —
what ``vera check --explain-slots`` prints, and what the verifier and the
LSP map a ``@T.n`` back to a parameter with.  The naming itself is
:mod:`vera.naming`'s (#1208): the table reports the names the checker
actually bound and every consumer resolves against, so it cannot tell the
user something no subsystem agrees with.

What remains here is deliberately NOT naming.
:func:`type_expr_slot_name` is the alias-opaque syntactic spelling the WASM
representation walks want, and :func:`resolve_scalar_alias_te` /
:func:`family_fallback_name` are the State/Exn cell FAMILY — an import name
and a WASM tag, not a binding key.  Each says why in its own docstring.

The De Bruijn convention: @T.0 is the *last* (rightmost) parameter of
type T in the signature; @T.1 is second-to-last; and so on.  For a
function ``fn foo(@Int, @Int -> @Int)``:
  - @Int.0 → parameter 2 (last @Int)
  - @Int.1 → parameter 1 (first @Int)
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterable, Mapping

from vera import ast, naming

# `substitute_named`, `resolve_alias_type_expr` and `AliasResolutionDepthError`
# MOVED to `vera.naming` (#1208), which owns every type-expression naming and
# resolution walk.  Re-exported here — unchanged, one implementation — so the
# existing `from vera.slots import ...` call sites (codegen/core.py,
# wasm/inference.py) keep working.
from vera.naming import (
    AliasEnv,
    AliasResolutionDepthError,
    resolve_alias_type_expr,
    substitute_named,
)

__all__ = [
    "AliasResolutionDepthError",
    "family_fallback_name",
    "fn_slot_scope",
    "format_slot_table",
    "resolve_alias_type_expr",
    "resolve_scalar_alias_te",
    "slot_table",
    "slot_table_dict",
    "substitute_named",
    "type_expr_slot_name",
]


# ------------------------------------------------------------------
# Canonical slot-name construction (single source of truth)
# ------------------------------------------------------------------

def type_expr_slot_name(te: ast.TypeExpr) -> str | None:
    """The SYNTACTIC full-depth type name of a TypeExpr, or ``None``.

    NOT a slot-environment key and NOT a slot-reference lookup: both of
    those render through :mod:`vera.naming` against a module's alias
    environment (#1208), because a name minted one way and looked up
    another misses silently.  What remains here is the alias-OPAQUE
    spelling — no environment, so nothing to resolve against — which is
    what the two REPRESENTATION walks want: the hop-by-hop alias
    canonicalization behind the WASM width / erasure deciders
    (``_canonicalize_alias_slot_name``) and the structural-``Eq``
    derivability oracle (``_ground_field_type_name``).  Both ask a
    question about a type's machine representation, one alias hop at a
    time; neither keys a binding.

    A parameterized type recurses into its type arguments to a
    FULLY-QUALIFIED name, so nested composites stay distinguishable
    (``Option<Tuple<Int, Int>>`` and ``Option<Tuple<Bool, Bool>>`` do NOT
    collapse to one ``Option<Tuple>`` — the pre-#914 one-level bug).
    Refinements resolve to their base name only.

    Returns ``None`` when a component is neither a `NamedType` nor a
    `RefinementType` chain over one — e.g. a `FnType` **nested inside** a
    type argument.  A top-level `FnType` yields the synthetic ``"Fn"``.
    """
    if isinstance(te, ast.NamedType):
        if te.type_args:
            inner_names: list[str] = []
            for a in te.type_args:
                inner = type_expr_slot_name(a)
                if inner is None:
                    return None
                inner_names.append(inner)
            return f"{te.name}<{', '.join(inner_names)}>"
        return te.name
    if isinstance(te, ast.RefinementType):
        return type_expr_slot_name(te.base_type)
    if isinstance(te, ast.FnType):
        return "Fn"
    return None


_SCALAR_BASE_NAMES = frozenset({"Int", "Nat", "Float64", "Bool", "Byte"})


def resolve_scalar_alias_te(
    te: ast.TypeExpr,
    aliases: Mapping[str, ast.TypeExpr],
    alias_params: Mapping[str, tuple[str, ...] | None],
) -> str | None:
    """Collapse a ``State<T>``/``Exn<E>`` type argument to its scalar
    base name IFF it resolves to a scalar primitive; ``None`` otherwise.

    The single resolution rule for the host-import and tag FAMILIES
    (#1205): the family's WASM type is derived from the RESOLVED type
    (``_type_expr_to_wasm_type`` canonicalizes), so the family NAME must
    resolve identically or a scalar alias splits into a name keyed one
    way and a WASM type keyed the other — the emitted ``state_put_Count``
    family carried i64 values into i32-typed uses, and the parameterised
    spellings (``Id<Nat>``, an alias of ``Id<Nat>``, ``Exn<Id<Int>>``)
    split identically.  Collapsing means a scalar-resolving argument
    NEVER mints a new import name: it joins the base family
    (``state_put_Nat``) every host binding (wasmtime, api.py,
    runtime.mjs) already provides — no #808-class import-surface fan-in.
    Composite-resolving names stay opaque on purpose: their WASM type is
    uniformly i32 (pointer), so name and type cannot diverge, and
    collapsing them WOULD change the import surface (#914 full-name
    invariant).
    """
    cn = resolve_alias_type_expr(te, aliases, alias_params)
    if cn is not None and not cn.type_args and cn.name in _SCALAR_BASE_NAMES:
        return cn.name
    return None


# ------------------------------------------------------------------
# Internal helpers
# ------------------------------------------------------------------

def _te_slot_name(te: ast.TypeExpr, env: AliasEnv) -> str:
    """Return the slot-matching name for a parameter TypeExpr (#1208).

    :func:`vera.naming.slot_name` against the module's naming environment —
    the ONE renderer, so the table reports the names the checker actually
    bound and every consumer resolves against, not a syntactic rebuild of
    them.  Already ``str``-total: an unresolvable component is ``"?"``.
    """
    return naming.slot_name(te, env)


def fn_slot_scope(
    env: AliasEnv, forall_vars: Iterable[str] | None,
) -> AliasEnv:
    """*env* as seen from INSIDE a function with those type parameters.

    A ``forall<T>`` variable shadows a same-named module alias for the whole
    signature — the checker binds it in ``_check_fn`` step 1, before it
    renders any parameter or reference — so both sides of a slot lookup have
    to be rendered here, never against the bare module environment.  One
    helper rather than a ``with_type_params`` call per consumer, so the
    binding side (:func:`slot_table`) and the reference side
    (:func:`vera.naming.slot_ref_key`) cannot end up scoped differently.
    """
    return naming.with_type_params(env, forall_vars) if forall_vars else env


def _label(tname: str, slot_idx: int, n: int) -> str:
    """Human-readable label for a slot entry, e.g. 'last @Int'."""
    if n == 1:
        return f"only @{tname}"
    if slot_idx == 0:
        return f"last @{tname}"
    if slot_idx == n - 1:
        return f"first @{tname}"
    return f"{n - slot_idx} from last @{tname}"


# ------------------------------------------------------------------
# Public API
# ------------------------------------------------------------------

def slot_table(
    params: tuple[ast.TypeExpr, ...],
    env: AliasEnv,
    forall_vars: Iterable[str] | None,
) -> dict[str, list[int]]:
    """Return the slot resolution table for a function's parameter list.

    Returns ``{type_name: [1-based param positions, slot-0-first]}``.

    Example: ``(@Int, @Int)`` → ``{"Int": [2, 1]}``
    meaning ``@Int.0`` = parameter 2, ``@Int.1`` = parameter 1.

    *env* is the module's naming environment (#1208): the table is a NAMING
    answer, so it is rendered by the one renderer rather than rebuilt
    syntactically.  Required rather than defaulted — an empty environment
    silently renders every alias opaquely, which is the failure mode the
    consolidation exists to close.

    *forall_vars* is the owning function's own type parameters (``None`` for
    a non-generic one), which SHADOW same-named module aliases for the whole
    signature — the checker binds its parameters with them already in scope
    (``_check_fn`` step 1, before step 4's slot binding), so a table rendered
    without them can disagree.  Concretely, under ``type T = Int`` the
    signature ``forall<T> fn g(@Option<Int>, @Option<T>)`` binds two stacks
    for the checker and ONE for a module-only rendering — which then reports
    ``@Option<Int>.0`` as parameter 2 where the checker resolves it to
    parameter 1.  Required, not defaulted, for the same reason *env* is: the
    omission has no symptom of its own.
    """
    scope = fn_slot_scope(env, forall_vars)
    by_type: dict[str, list[int]] = defaultdict(list)
    for i, te in enumerate(params, 1):
        by_type[_te_slot_name(te, scope)].append(i)
    return {tname: list(reversed(pos)) for tname, pos in by_type.items()}


def format_slot_table(
    fn_name: str,
    params_str: str,
    table: dict[str, list[int]],
) -> str:
    """Format a human-readable slot environment block for one function.

    Returns a multi-line string suitable for printing to stdout, e.g.::

        fn divide(@Int, @Int -> @Int)
          @Int.0  parameter 2 (last @Int)
          @Int.1  parameter 1 (first @Int)
    """
    lines = [f"  fn {fn_name}({params_str})"]
    for tname in sorted(table):
        positions = table[tname]
        n = len(positions)
        for slot_idx, param_pos in enumerate(positions):
            lines.append(
                f"    @{tname}.{slot_idx}  "
                f"parameter {param_pos} ({_label(tname, slot_idx, n)})"
            )
    return "\n".join(lines)


def slot_table_dict(
    fn_name: str,
    table: dict[str, list[int]],
) -> dict[str, object]:
    """Return a JSON-serialisable slot table for a single function."""
    entries: list[dict[str, object]] = []
    for tname in sorted(table):
        for slot_idx, param_pos in enumerate(table[tname]):
            entries.append({
                "slot": f"@{tname}.{slot_idx}",
                "type": tname,
                "parameter": param_pos,
            })
    return {"function": fn_name, "slots": entries}


def family_fallback_name(te: ast.TypeExpr) -> str:
    """The opaque fallback for a ``State<T>`` / ``Exn<E>`` cell FAMILY.

    The family names an IMPORT and a WASM tag, not a slot, and it stays on
    the alias-opaque syntactic spelling for now: resolving it is a change to
    the emitted import surface (#1209), separate from the #1208 slot-naming
    consolidation, and the checker's own argument rendering is not
    mangle-safe — a refined argument renders ``Option<{@Int | ...}>``, which
    ``mangle_type_name`` does not escape.  Total, because a family must
    always have a name to mangle.

    Derived here rather than passed in by each of the eight call sites: the
    scalar collapse and its fallback are one decision about one type
    expression, and the two `_family_name` methods that make it are the only
    places allowed to make it.
    """
    return type_expr_slot_name(te) or "?"
