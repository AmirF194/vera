"""Slot reference table utilities for ``vera check --explain-slots``.

Computes a slot resolution table for a function purely from its parameter
type expressions (no live type-checker environment required).

The De Bruijn convention: @T.0 is the *last* (rightmost) parameter of
type T in the signature; @T.1 is second-to-last; and so on.  For a
function ``fn foo(@Int, @Int -> @Int)``:
  - @Int.0 → parameter 2 (last @Int)
  - @Int.1 → parameter 1 (first @Int)
"""

from __future__ import annotations

from collections import defaultdict

from vera import ast


# ------------------------------------------------------------------
# Canonical slot-name construction (single source of truth)
# ------------------------------------------------------------------

def type_expr_slot_name(te: ast.TypeExpr) -> str | None:
    """Canonical slot-matching name for a TypeExpr, or ``None`` if the
    type has no nameable slot form.

    The ONE recursive builder for slot-environment keys and slot-reference
    lookups across the codegen and verifier subsystems (#914 finding 2 /
    dedup): a parameterized type recurses into its type arguments to a
    FULLY-QUALIFIED name, so nested composites are distinguishable
    (``Option<Tuple<Int, Int>>`` and ``Option<Tuple<Bool, Bool>>`` do NOT
    collapse to the same ``Option<Tuple>`` — the pre-#914 one-level bug that
    collided their `state_*` imports / `exn_*` tags and any two same-outer
    nested slots in one scope).  Type aliases stay OPAQUE (``@PosInt.0``
    counts ``PosInt`` bindings, not ``Int``) — refinements resolve to their
    base name only.  Matches the checker's own recursive key (via
    ``canonical_type_name`` → ``pretty_type``), so the checker's slot
    environment and the downstream codegen/verifier ones agree.

    Returns ``None`` when a component is neither a `NamedType` nor a
    `RefinementType` chain over one — e.g. a `FnType` **nested inside** a
    type argument — so the strict codegen callers (`str | None`) can skip.
    A top-level `FnType` yields the synthetic ``"Fn"`` name.
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


def substitute_named(
    te: ast.TypeExpr, subst: dict[str, ast.TypeExpr],
) -> ast.TypeExpr:
    """Rewrite ``NamedType`` occurrences of *subst* keys inside *te* —
    the minimal substitution the alias walk below needs (a parameterised
    alias body mentions its params as bare or argument-position
    ``NamedType``s).  Refinement predicates are left untouched: the walk
    only ever *names* the result, never re-checks the predicate."""
    if isinstance(te, ast.NamedType):
        if not te.type_args and te.name in subst:
            return subst[te.name]
        if te.type_args:
            return ast.NamedType(
                name=te.name,
                type_args=tuple(
                    substitute_named(a, subst) for a in te.type_args),
            )
        return te
    if isinstance(te, ast.RefinementType):
        return ast.RefinementType(
            base_type=substitute_named(te.base_type, subst),
            predicate=te.predicate,
        )
    return te


_RESOLVE_DEPTH_LIMIT = 32


def resolve_alias_type_expr(
    te: ast.TypeExpr,
    aliases: dict[str, ast.TypeExpr],
    alias_params: dict[str, tuple[str, ...]],
    _depth: int = 0,
) -> ast.NamedType | None:
    """Walk *te* to its terminal ``NamedType`` through refinement
    unwrapping, bare alias-chain follows, and PARAMETERISED alias
    substitution (``type Id<T> = T`` applied at ``Id<Nat>`` — the
    #630-era latent gap the PR #1202 adversarial rounds showed still
    split the state family).  ``None`` when the walk lands on a
    non-``NamedType`` (an ``FnType``-bodied alias, etc.).  Lives here so
    the ``CodeGenerator`` registration side and the ``WasmContext``
    lowering side resolve through ONE implementation and cannot drift.

    Arguments resolve FIRST, mirroring the checker's order — a
    seen-set head-follow truncated legitimate finite expansions
    (``Id<Id<Nat>>`` substitutes to ``Id<Nat>``, whose head re-entry a
    seen-set misreads as a cycle, stopping one level short: the round-3
    review's silent handler-bypass and invalid-WASM shapes).  True
    cycles are E132 at check; the depth bound is defence-in-depth so a
    future upstream regression degrades to the opaque fallback instead
    of a hang."""
    if _depth > _RESOLVE_DEPTH_LIMIT:
        return None
    while isinstance(te, ast.RefinementType):
        te = te.base_type
    if not isinstance(te, ast.NamedType):
        return None
    if te.type_args:
        resolved_args: list[ast.TypeExpr] = []
        for a in te.type_args:
            ra = resolve_alias_type_expr(a, aliases, alias_params, _depth + 1)
            resolved_args.append(ra if ra is not None else a)
        te = ast.NamedType(name=te.name, type_args=tuple(resolved_args))
    alias = aliases.get(te.name)
    if alias is None:
        return te
    if not isinstance(alias, (ast.NamedType, ast.RefinementType)):
        return None
    params = alias_params.get(te.name)
    if params and te.type_args and len(params) == len(te.type_args):
        alias = substitute_named(alias, dict(zip(params, te.type_args)))
    elif te.type_args:
        # A parameterised application of a non-parameterised alias (or an
        # arity mismatch) is ill-formed upstream — keep it opaque rather
        # than resolving to something the application didn't mean.
        return te
    return resolve_alias_type_expr(alias, aliases, alias_params, _depth + 1)


def resolve_scalar_alias_te(
    te: ast.TypeExpr,
    aliases: dict[str, ast.TypeExpr],
    alias_params: dict[str, tuple[str, ...]],
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


def slot_ref_name(ref: ast.SlotRef) -> str | None:
    """Canonical lookup name for a ``@T.n`` slot reference, or ``None``.

    The lookup-side counterpart of :func:`type_expr_slot_name` — a
    `SlotRef` carries `type_name` (str) + `type_args` (TypeExprs), so it
    resolves through the SAME recursive builder as the key side, keeping
    env-key construction and slot lookup matched for nested composites
    (#914 finding 2).  Bare (no-type-arg) refs return `type_name` unchanged.
    """
    if not ref.type_args:
        return ref.type_name
    return type_expr_slot_name(
        ast.NamedType(name=ref.type_name, type_args=ref.type_args)
    )


# ------------------------------------------------------------------
# Internal helpers
# ------------------------------------------------------------------

def _te_slot_name(te: ast.TypeExpr) -> str:
    """Return the canonical slot-matching name for a parameter TypeExpr.

    Thin ``str``-total wrapper over :func:`type_expr_slot_name` (the shared
    recursive builder) for the ``--explain-slots`` table, which wants a
    display string for every input: an unnameable component becomes ``"?"``.
    """
    return type_expr_slot_name(te) or "?"


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
) -> dict[str, list[int]]:
    """Return the slot resolution table for a function's parameter list.

    Returns ``{type_name: [1-based param positions, slot-0-first]}``.

    Example: ``(@Int, @Int)`` → ``{"Int": [2, 1]}``
    meaning ``@Int.0`` = parameter 2, ``@Int.1`` = parameter 1.
    """
    by_type: dict[str, list[int]] = defaultdict(list)
    for i, te in enumerate(params, 1):
        by_type[_te_slot_name(te)].append(i)
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
