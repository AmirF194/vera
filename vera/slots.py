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
representation walks want, and :func:`family_fallback_name` is what a
State/Exn cell family falls back on when its type expression names no
family at all.  Each says why in its own docstring.  The family itself
renders through :func:`vera.naming.family_name` (#1209).

The De Bruijn convention: @T.0 is the *last* (rightmost) parameter of
type T in the signature; @T.1 is second-to-last; and so on.  For a
function ``fn foo(@Int, @Int -> @Int)``:
  - @Int.0 → parameter 2 (last @Int)
  - @Int.1 → parameter 1 (first @Int)
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterable, Iterator

from vera import ast, naming
from vera.naming import AliasEnv

__all__ = [
    "family_fallback_name",
    "fn_scopes",
    "fn_slot_scope",
    "format_slot_table",
    "slot_table",
    "slot_table_dict",
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


def fn_scopes(
    decl: ast.FnDecl,
    inherited: Iterable[str] = (),
    _path: tuple[str, ...] = (),
) -> Iterator[tuple[ast.FnDecl, tuple[str, ...], tuple[str, ...]]]:
    """*decl* and every function nested in its ``where`` block, in source
    order, as ``(fn, type parameters in scope OVER it, qualified name path)``.

    A ``where`` helper sees its parent's ``forall`` variables as well as its
    own: ``_check_fn`` saves and restores one shared type-parameter map
    rather than replacing it, so entering a helper ADDS to the scope.  The
    accumulated tuple is therefore what :func:`fn_slot_scope` has to be given
    for a helper — narrowed by the parent's variables, a same-named module
    alias stays shadowed all the way down, and rendering the helper against
    the bare module environment silently merges parameter stacks the checker
    keeps apart.

    The path is the enclosing function names followed by this one, so its
    length carries the nesting depth and its join is a name unique within the
    module (helpers of two different functions may share a bare name).

    One walk rather than one per consumer (``vera check --explain-slots`` and
    the LSP's go-to-definition, #1217): both ask the same question about the
    same nesting, and an accumulation that differed between them would put
    the two surfaces' answers about one helper out of step.
    """
    in_scope = (*inherited, *(decl.forall_vars or ()))
    path = (*_path, decl.name)
    yield decl, in_scope, path
    for helper in decl.where_fns or ():
        yield from fn_scopes(helper, in_scope, path)


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
    depth: int = 0,
) -> str:
    """Format a human-readable slot environment block for one function.

    Returns a multi-line string suitable for printing to stdout.  EVERY line
    carries a leading indent — at ``depth=0`` the ``fn`` line is indented two
    spaces and its slot rows four, two more of each per ``where`` level — so
    the block below is what the caller prints, shifted right by two::

        fn divide(@Int, @Int -> @Int)
          @Int.0  parameter 2 (last @Int)
          @Int.1  parameter 1 (first @Int)

    *depth* is the ``where``-nesting level (#1217): a helper is indented one
    step further than its parent and labelled ``where fn``, so the printed
    tables carry the nesting that decides which parameters a ``@T.n`` inside
    the helper can name.
    """
    indent = "  " * (depth + 1)
    keyword = "where fn" if depth else "fn"
    lines = [f"{indent}{keyword} {fn_name}({params_str})"]
    for tname in sorted(table):
        positions = table[tname]
        n = len(positions)
        for slot_idx, param_pos in enumerate(positions):
            lines.append(
                f"{indent}  @{tname}.{slot_idx}  "
                f"parameter {param_pos} ({_label(tname, slot_idx, n)})"
            )
    return "\n".join(lines)


def slot_table_dict(
    fn_name: str,
    table: dict[str, list[int]],
) -> dict[str, object]:
    """Return a JSON-serialisable slot table for a single function.

    *fn_name* is the function's qualified name — ``parent.helper`` for a
    ``where``-block helper (#1217) — because a helper may share its bare name
    with a helper of another function, and a consumer keying on ``function``
    would silently collapse the two.
    """
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
    """The last-resort name for a ``State<T>`` / ``Exn<E>`` cell FAMILY.

    The family itself resolves — :func:`vera.naming.family_name` names the
    CELL the checker typed, so every spelling that resolves to one cell
    mangles to one import and one tag (#1209).  What is left for here is the
    residue that resolution cannot name: a type expression whose resolution
    is a function type or ``UnknownType`` (an ``FnType``-bodied alias as
    ``State<F>``, an arity-mismatched alias application, a removed alias).
    Those have no cell type to name, so the family falls back on the
    alias-OPAQUE syntactic spelling — distinct per spelling, which is the
    conservative direction: it can only ever split a family the checker
    already refuses to type, never merge two the checker keeps apart.

    Total, because a family must always have a name to mangle.  Derived here
    rather than passed in by each of the eight call sites: the fallback and
    the resolution are one decision about one type expression, and the two
    `_family_name` methods that make it are the only places allowed to make
    it.
    """
    return type_expr_slot_name(te) or "?"
