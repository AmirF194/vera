"""Test-side construction of a :class:`~vera.naming.AliasEnv` from an AST.

Every PRODUCTION consumer builds its naming environment from a namespace it
already holds — the checker and the verifier from a live
:class:`~vera.environment.TypeEnv` (``naming.alias_env_from_environment``),
codegen from its own flat alias maps (``_sync_alias_env``).  None of them
walks a declaration list to build one, and #1208 review removed the
``vera.naming.alias_env_from_declarations`` that had no reader: a second
implementation of "assign declaration indices while walking decls" is exactly
the hand-maintained twin the consolidation exists to retire.

The TEST suite still wants the short form — a parsed program in, an env out,
with no checker to run first — so it lives here, where it is unambiguously a
fixture constructor and can never become a second production source of truth.
The :class:`~vera.naming.AliasEnv` it returns is the production dataclass, so
its field contract is still enforced by the module under test.
"""
from __future__ import annotations

from collections.abc import Iterable

from vera import ast
from vera.naming import AliasEnv


def alias_env_from_declarations(
    decls: Iterable[object],
    base: AliasEnv | None = None,
) -> AliasEnv:
    """Build a naming env by walking declarations, in source order.

    Accepts either ``TopLevelDecl`` wrappers or bare ``Decl`` nodes.  *base*
    layers an outer environment UNDER these declarations — prelude aliases
    first, then the module's — preserving the declaration order the
    alias-visibility rule needs.

    Declared ADTs are collected too, and stamped with the SAME shared
    declaration index the aliases get (#1208) — a walk in source order is
    exactly the order the checker's registration pass allocates them in.  The
    BUILT-IN ADTs (``Option``, ``Result``, ``Json``, …) are deliberately not
    seeded: data-type membership only changes a rendering for a name the
    resolver treats specially (``Decimal``, a ``REMOVED_ALIASES`` entry), and
    no built-in ADT takes one of those names — every other ADT reaches the
    same opaque ``AdtType`` either way.
    """
    aliases: dict[str, ast.TypeExpr] = dict(base.aliases) if base else {}
    alias_params: dict[str, tuple[str, ...] | None] = (
        dict(base.alias_params) if base else {})
    data_types: dict[str, int] = dict(base.data_types) if base else {}
    order: dict[str, int] = dict(base._order) if base else {}
    # Layered declarations continue the base's index space rather than
    # restarting it, so "the prelude was declared first" survives the merge.
    idx = max((*order.values(), *data_types.values(), -1)) + 1
    for item in decls:
        decl = getattr(item, "decl", item)
        if isinstance(decl, ast.TypeAliasDecl):
            aliases[decl.name] = decl.type_expr
            alias_params[decl.name] = decl.type_params
            order[decl.name] = idx
            idx += 1
        elif isinstance(decl, ast.DataDecl):
            data_types[decl.name] = idx
            idx += 1
    return AliasEnv(
        aliases=aliases,
        alias_params=alias_params,
        type_params=base.type_params if base else frozenset(),
        data_types=data_types,
        _order=order,
    )
