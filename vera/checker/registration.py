"""Pass 1 registration mixin — forward-declares all top-level names."""

from __future__ import annotations

import dataclasses
import functools

from vera import ast
from vera.environment import (
    AbilityInfo,
    AdtInfo,
    ConstructorInfo,
    EffectInfo,
    OpInfo,
    TypeAliasInfo,
)
from vera.types import TypeVar


@functools.lru_cache(maxsize=1)
def _builtin_reject_names() -> frozenset[str]:
    """Built-in function names a user/module ``fn`` must not redefine (E151).

    The full built-in registry minus the prelude-injected combinators, which
    the prelude lets the user override soundly (see
    :func:`vera.prelude.overridable_builtin_names`).  Cached: the built-in
    set is static.  Drives the #815 "one canonical form" check — redefining
    an opaque, verifier-modelled built-in (``abs`` / ``min`` / ``max`` / …)
    is the silent verifier↔runtime unsoundness that motivates the error.
    """
    from vera.environment import TypeEnv
    from vera.prelude import overridable_builtin_names

    # #854: apply_fn is a checker special form (variadic and
    # effect-polymorphic — see CallsMixin._check_apply_fn), not a
    # registry row, so it is absent from TypeEnv().functions; add it
    # explicitly.  Codegen unconditionally translates the name to
    # call_indirect (vera/wasm/calls.py), so a user redefinition is the
    # same checker↔codegen desync #815 guards against.
    return (frozenset(TypeEnv().functions)
            | {"apply_fn"}) - overridable_builtin_names()


def _strip_rejected_where_fns(decl: ast.FnDecl) -> ast.FnDecl:
    """Return ``decl`` with any where-helper named after a built-in removed,
    recursively (#815).

    A rejected helper must not overwrite the canonical built-in entry in
    ``env.functions`` (the shared ``register_fn`` registers every where-fn by
    name).  Its E151 is emitted separately in
    :meth:`RegistrationMixin._check_builtin_redefinition`; this only prevents
    its registration so a sibling call still resolves to the built-in.
    """
    if not decl.where_fns:
        return decl
    reject = _builtin_reject_names()
    kept = tuple(
        _strip_rejected_where_fns(wfn)
        for wfn in decl.where_fns
        if wfn.name not in reject
    )
    return dataclasses.replace(decl, where_fns=kept or None)


class RegistrationMixin:
    """Methods that register top-level declarations into the type environment."""

    def _register_all(self, program: ast.Program) -> None:
        """Register all top-level declarations (forward reference support)."""
        for tld in program.declarations:
            # C7c: require explicit visibility on fn/data declarations
            if (tld.visibility is None
                    and isinstance(tld.decl, (ast.FnDecl, ast.DataDecl))):
                name = tld.decl.name
                kind = "fn" if isinstance(tld.decl, ast.FnDecl) else "data"
                self._error(
                    tld.decl,
                    f"Missing visibility on '{name}'. "
                    f"Add 'public' or 'private' before '{kind}'.",
                    rationale=(
                        "Every top-level function and data type must have "
                        "an explicit visibility annotation."
                    ),
                    fix=f"private {kind} {name}(...) or public {kind} {name}(...)",
                    spec_ref='Chapter 8, Section 8.4 "Visibility"',
                )
            # #815: redefining a built-in is a one-canonical-form violation
            # (and a silent verifier↔runtime unsoundness for the
            # verifier-modelled built-ins).  Covers top-level and module
            # functions and their where-helpers; prelude combinators exempt.
            if (isinstance(tld.decl, ast.FnDecl)
                    and self._check_builtin_redefinition(tld.decl)):
                # Rejected built-in redefinition — do not register it over the
                # canonical entry in ``env.functions`` (#815); leave the
                # built-in in scope so later references resolve to it, not the
                # invalid user definition.
                continue
            self._register_decl(tld.decl, visibility=tld.visibility)

        # Post-registration cycle detection on type aliases (#648).
        # `_register_alias` resolves each alias's target one at a time;
        # when `type A = B` is processed before `B` is registered, the
        # forward-ref fallback in `_resolve_type` returns a placeholder
        # rather than chasing the chain, so `A = B; B = A` reaches the
        # post-loop state with no observable cycle in the resolved
        # types.  Codegen later stores the raw AST `type_expr` and
        # `_type_expr_to_wasm_type` chases the chain through the AST,
        # producing a `RecursionError` instead of a clean diagnostic.
        # Fix: walk the alias chain in the AST after all aliases have
        # registered, emit `[E132]` for any cycle we find.
        self._check_alias_cycles(program)

    def _check_builtin_redefinition(self, decl: ast.FnDecl) -> bool:
        """Emit E151 if ``decl`` (or a nested where-helper) redefines a
        built-in (#815).

        Returns ``True`` if ``decl`` itself redefines a built-in, so the
        caller can skip registering it over the canonical entry.  Recurses
        into ``where_fns`` so a helper named after a built-in is caught too —
        otherwise the verifier models the call with the built-in's idealized
        model while codegen runs the where-body, the exact
        verify-proves / run-violates desync one scope deeper.  The
        prelude-injected combinators are exempt (see
        :func:`_builtin_reject_names`).
        """
        rejected = decl.name in _builtin_reject_names()
        if rejected:
            self._rejected_builtin_redefs.add(id(decl))
            bn = decl.name
            self._error(
                decl,
                f"Function '{bn}' redefines a built-in.",
                rationale=(
                    f"'{bn}' is a built-in function (spec §9.6) — it is "
                    f"always in scope as the single canonical '{bn}'. "
                    f"Vera provides exactly one way to express each "
                    f"operation, so re-declaring a built-in is not "
                    f"allowed: there is nothing to gain by rolling your "
                    f"own, and a second definition is a second way to say "
                    f"the same thing. For the verifier-modelled built-ins "
                    f"it is also silently unsound — the verifier reasons "
                    f"about every call using the built-in's model while "
                    f"codegen runs your body, so a postcondition can be "
                    f"proved against the built-in yet violated at runtime "
                    f"by your version."
                ),
                fix=(
                    f"Delete this definition and call the built-in '{bn}' "
                    f"directly — it needs no import. If you intend "
                    f"genuinely different behaviour, give the function a "
                    f"distinct name (e.g. '{bn}_custom')."
                ),
                spec_ref='Chapter 9, Section 9.6 "Built-in Functions"',
                error_code="E151",
            )
        nested_rejected = False
        for wfn in decl.where_fns or ():
            if self._check_builtin_redefinition(wfn):
                nested_rejected = True
        # #815: a rejected nested helper is stripped from registration, so if
        # the parent body calls it the call resolves against the canonical
        # built-in and cascades bogus arity/type errors. Mark the parent so its
        # body is skipped in the check phase too. The return value still
        # reflects only whether ``decl``'s own name shadows a built-in, so the
        # parent itself is still registered under its (legitimate) name.
        if nested_rejected:
            self._rejected_builtin_redefs.add(id(decl))
        return rejected

    def _check_alias_cycles(self, program: ast.Program) -> None:
        """Detect cyclic type aliases and emit `[E132]`.

        A type alias abbreviates a *finite* type, so its expansion must
        terminate.  This walks the directed graph whose nodes are the
        program's aliases and whose edges run from an alias to every
        other alias its target *structurally* references — the target's
        own `NamedType` head, every `type_arg` at any nesting depth, and
        the base of any `RefinementType` wrapper.  A cycle in that graph
        is an alias whose expansion never terminates: `type F =
        Future<F>`, `type A = Future<B>; type B = Future<A>`, `type L =
        Array<L>`.  Such a type is uninhabitable and has no underlying
        representation, and where the cycle threads a `type_arg` position
        that `_type_expr_to_wasm_type` recurses through (`Future<T>`) it
        crashes codegen with a `RecursionError` (#1059).

        Descending into `type_args` is the #1059 extension.  The original
        #648 pass mirrored codegen's alias walker exactly — bare
        `type A = B` references and `RefinementType` bases only — and so
        followed no `type_arg` edge, silently admitting every
        through-`type_arg` cycle (`Array<L>` compiles to a stuck i32_pair
        rather than crashing, but it is no more inhabitable than the
        `Future` spellings, so all three are rejected uniformly).

        A generic alias's own type *parameters* are excluded from the
        reference set: in `type Box<T> = Array<T>` the `T` is bound
        locally and never counts as a reference to a same-named alias,
        so a parameterised abbreviation is not mistaken for a self-cycle.
        """
        alias_decls: dict[str, ast.TypeAliasDecl] = {}
        for tld in program.declarations:
            if isinstance(tld.decl, ast.TypeAliasDecl):
                alias_decls.setdefault(tld.decl.name, tld.decl)

        # Standard three-colour DFS: `on_stack` (grey) holds the current
        # path so a back-edge into it is a cycle; `safe` (black) holds
        # aliases fully explored with no cycle reachable; `reported`
        # suppresses a second diagnostic for aliases already named in an
        # emitted cycle (one E132 per cycle is enough to act on).
        safe: set[str] = set()
        reported: set[str] = set()

        def visit(name: str, path: list[str], on_stack: set[str]) -> None:
            decl = alias_decls[name]
            exclude = set(decl.type_params or ())
            for ref in self._referenced_aliases(
                decl.type_expr, alias_decls, exclude
            ):
                if ref in on_stack:
                    cycle = path[path.index(ref):] + [ref]
                    if not any(n in reported for n in cycle):
                        self._error(
                            alias_decls[cycle[0]],
                            f"Cyclic type alias `{cycle[0]}`: "
                            f"{' -> '.join(cycle)}.",
                            rationale=(
                                "Type aliases must eventually resolve to a "
                                "concrete type.  A cycle leaves the alias "
                                "with no underlying representation and "
                                "would crash codegen with unbounded "
                                "recursion."
                            ),
                            fix=(
                                "Replace one alias in the cycle with a "
                                "concrete type, or with an `ADT` declared "
                                "via `data` (which can be self-referential "
                                "because the indirection is a heap "
                                "pointer)."
                            ),
                            spec_ref='Chapter 2, Section 2.6.3 "Type Aliases with Refinements"',
                            error_code="E132",
                        )
                        reported.update(cycle)
                    continue
                if ref in safe or ref in reported:
                    continue
                path.append(ref)
                on_stack.add(ref)
                visit(ref, path, on_stack)
                on_stack.discard(ref)
                path.pop()
            safe.add(name)

        for name in alias_decls:
            if name in safe or name in reported:
                continue
            visit(name, [name], {name})

    @staticmethod
    def _referenced_aliases(
        te: ast.TypeExpr,
        aliases: dict[str, ast.TypeAliasDecl],
        exclude: set[str],
    ) -> list[str]:
        """Alias names `te` structurally references, outer-to-inner and
        left-to-right so the reported cycle path is deterministic.

        Recurses into `NamedType.type_args` (so a self-reference buried
        in `Future<F>` / `Array<L>` is seen — the #1059 extension) and
        `RefinementType.base_type` (so a cycle hidden behind a refinement
        wrapper is seen — #648).  `exclude` holds the enclosing alias's
        own type parameters, which are locally bound and never count as a
        reference to a like-named alias.
        """
        out: list[str] = []

        def walk(t: ast.TypeExpr) -> None:
            if isinstance(t, ast.NamedType):
                if t.name in aliases and t.name not in exclude:
                    out.append(t.name)
                for arg in t.type_args or ():
                    walk(arg)
            elif isinstance(t, ast.RefinementType):
                walk(t.base_type)

        walk(te)
        return out

    def _register_decl(
        self, decl: ast.Decl, visibility: str | None = None,
    ) -> None:
        """Register a single declaration's signature."""
        if isinstance(decl, ast.DataDecl):
            self._register_data(decl, visibility=visibility)
        elif isinstance(decl, ast.TypeAliasDecl):
            self._register_alias(decl)
        elif isinstance(decl, ast.EffectDecl):
            self._register_effect(decl)
        elif isinstance(decl, ast.FnDecl):
            self._register_fn(decl, visibility=visibility)
        elif isinstance(decl, ast.AbilityDecl):
            self._register_ability(decl)

    def _register_data(
        self, decl: ast.DataDecl, visibility: str | None = None,
    ) -> None:
        """Register an ADT and its constructors."""
        # Set up type params for resolving constructor field types
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ctors: dict[str, ConstructorInfo] = {}
        for ctor in decl.constructors:
            field_types = None
            if ctor.fields is not None:
                field_types = tuple(
                    self._resolve_type(f) for f in ctor.fields)
            ci = ConstructorInfo(
                name=ctor.name,
                parent_type=decl.name,
                parent_type_params=decl.type_params,
                field_types=field_types,
            )
            ctors[ctor.name] = ci
            self.env.constructors[ctor.name] = ci

        self.env.data_types[decl.name] = AdtInfo(
            name=decl.name,
            type_params=decl.type_params,
            constructors=ctors,
            visibility=visibility,
        )

        self.env.type_params = saved_params

    def _register_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Register a type alias."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        resolved = self._resolve_type(decl.type_expr)
        self.env.type_aliases[decl.name] = TypeAliasInfo(
            name=decl.name,
            type_params=decl.type_params,
            resolved_type=resolved,
        )

        self.env.type_params = saved_params

    def _register_effect(self, decl: ast.EffectDecl) -> None:
        """Register an effect and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,
            )

        self.env.effects[decl.name] = EffectInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_ability(self, decl: ast.AbilityDecl) -> None:
        """Register an ability and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(
                self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,  # stores ability name
            )

        self.env.abilities[decl.name] = AbilityInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_fn(
        self, decl: ast.FnDecl, visibility: str | None = None,
    ) -> None:
        """Register a function signature."""
        from vera.registration import register_fn
        # #815: drop where-helpers named after a built-in before registering,
        # so a rejected helper can't overwrite the canonical entry (its E151 is
        # emitted in _check_builtin_redefinition).
        register_fn(
            self.env, _strip_rejected_where_fns(decl),
            self._resolve_type, self._resolve_effect_row,
            visibility=visibility,
        )
