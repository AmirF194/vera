"""Mixin for cross-module registration (C7b/C7c).

Extracted from ``core.py`` so that import-related logic lives in its
own file while the main :class:`TypeChecker` stays focused on
single-module checking.
"""

from __future__ import annotations

from dataclasses import replace

from vera import ast
from vera.environment import TypeEnv
from vera.resolver import ResolvedModule


class ModulesMixin:
    """Methods for registering declarations from resolved modules."""

    def _register_modules(self, program: ast.Program) -> None:
        """Register declarations from resolved modules (C7b/C7c).

        1. Build an import-name filter from the program's ``import``
           declarations (selective vs wildcard).
        2. For each resolved module, run the registration pass in an
           isolated TypeChecker to populate its ``TypeEnv``, then
           harvest the declarations into per-module dicts.
        3. C7c: filter to public declarations only.  Store unfiltered
           dicts for better "is private" error messages.
        4. C7c: emit errors when selective imports reference private names.
        5. Inject selectively imported *public* names into ``self.env`` so
           bare calls (``abs(42)`` after ``import vera.math(abs)``)
           resolve through the normal ``_check_call_with_args`` path.
        """
        from vera.checker.core import TypeChecker

        # 1. Build import filter
        for imp in program.imports:
            self._import_names[imp.path] = (
                set(imp.names) if imp.names is not None else None
            )

        # Snapshot builtin names (TypeEnv registers builtins in __post_init__)
        _builtins = TypeEnv()
        builtin_fn_names = set(_builtins.functions)
        builtin_data_names = set(_builtins.data_types)
        builtin_ctor_names = set(_builtins.constructors)

        # 2. Register each module in isolation, harvest declarations
        for mod in self._resolved_modules:
            # Pass the module's file path so any harvested diagnostic (e.g. the
            # E151 below) carries `location.file`, matching every other
            # diagnostic; `temp` is built with the module's own source/path.
            temp = TypeChecker(source=mod.source, file=str(mod.file_path))
            temp._register_all(mod.program)

            # #815: surface E151 (a module fn redefining a built-in) into the
            # importer.  ``temp`` is built with the module's own source, so
            # these diagnostics already carry the correct module-file location
            # and source line.  Without this, a module imported but never
            # checked standalone would let the redefinition through silently —
            # the importer's verifier reasons with the built-in's model while
            # the module's body runs (verify proves, run violates).
            # #1149: E152 (a module redeclaring a built-in EFFECT) is surfaced
            # on the same grounds — the block is invisible to codegen, which
            # routes the qualified call to the host import regardless, so an
            # unchecked module would miscompile the importer.
            # #1181/#1187: E153 (a module fn named after a contract state form
            # or a grammar keyword) likewise — a module imported but never
            # checked standalone would otherwise carry a declaration no
            # importer could ever bare-call.
            self.errors.extend(
                e for e in temp.errors
                if e.error_code in ("E151", "E152", "E153", "E154")
            )

            # #1244: and CHECK the module's bodies, under ITS OWN import
            # filter.  Registration alone says what a module declares; it
            # says nothing about whether the module's bodies resolve, so a
            # name a module never imported was accepted whenever the module
            # was reached AS AN IMPORT and rejected when the same file was
            # checked directly — one program, two verdicts by entry point,
            # with the lenient one leaking names across a module boundary
            # the spec draws (§8.5.1).  The verifier has honoured the
            # module-local rule regardless of entry point since #1225; this
            # is the checker catching up.
            self._check_module_bodies(mod)

            # All module-declared names (exclude builtins)
            all_fns = {
                k: v for k, v in temp.env.functions.items()
                if k not in builtin_fn_names or v.span is not None
            }
            all_data = {
                k: v for k, v in temp.env.data_types.items()
                if k not in builtin_data_names
            }

            # C7c: keep unfiltered dicts for "is private" error messages
            self._module_all_functions[mod.path] = all_fns
            self._module_all_data_types[mod.path] = all_data

            # 3. C7c: filter to public only
            mod_fns = {
                k: v for k, v in all_fns.items()
                if self._is_public(v.visibility)
            }
            mod_data = {
                k: v for k, v in all_data.items()
                if self._is_public(v.visibility)
            }
            # Constructors: include only from public ADTs
            public_adt_ctors: set[str] = set()
            for dt_info in mod_data.values():
                public_adt_ctors.update(dt_info.constructors)
            mod_ctors = {
                k: v for k, v in temp.env.constructors.items()
                if k not in builtin_ctor_names
                and k in public_adt_ctors
            }

            self._module_functions[mod.path] = mod_fns
            self._module_data_types[mod.path] = mod_data
            self._module_constructors[mod.path] = mod_ctors

            # 4. C7c: check selective imports for private names
            name_filter = self._import_names.get(mod.path)
            mod_label = ".".join(mod.path)
            if name_filter is not None:
                imp_node = self._find_import_decl(program, mod.path)
                for name in sorted(name_filter):
                    priv_fn = all_fns.get(name)
                    priv_dt = all_data.get(name)
                    if (priv_fn is not None
                            and not self._is_public(priv_fn.visibility)):
                        self._error(
                            imp_node,
                            f"Cannot import '{name}' from module "
                            f"'{mod_label}': it is private.",
                            rationale=(
                                "Only public declarations can be imported."
                            ),
                            fix=(
                                f"Mark '{name}' as public in the module, "
                                f"or remove it from the import list."
                            ),
                            spec_ref=(
                                'Chapter 8, Section 8.4 '
                                '"Visibility"'
                            ),
                            error_code="E150",
                        )
                    elif (priv_dt is not None
                            and not self._is_public(priv_dt.visibility)):
                        self._error(
                            imp_node,
                            f"Cannot import '{name}' from module "
                            f"'{mod_label}': it is private.",
                            rationale=(
                                "Only public declarations can be imported."
                            ),
                            fix=(
                                f"Mark '{name}' as public in the module, "
                                f"or remove it from the import list."
                            ),
                            spec_ref=(
                                'Chapter 8, Section 8.4 '
                                '"Visibility"'
                            ),
                            error_code="E150",
                        )

            # 5. Inject public names into main env for bare calls.
            #
            # #890: only a DIRECTLY-imported module's public declarations are
            # visible to the top-level importer (spec §8.6.4 — a transitive
            # module reached only through another module's imports is *not*
            # transitively visible here).  A transitive module is still in
            # ``self._resolved_modules`` so codegen can compile the bodies that
            # call into it, but its names must not enter the importer's bare
            # namespace, and its qualified-call registries above stay unset for
            # it — ``main`` can neither bare-call nor ``base::``-call it.
            if not mod.direct:
                continue
            for fn_name, fn_info in mod_fns.items():
                if name_filter is None or fn_name in name_filter:
                    self.env.functions.setdefault(fn_name, fn_info)
            for dt_name, dt_info in mod_data.items():
                if name_filter is None or dt_name in name_filter:
                    self.env.data_types.setdefault(dt_name, dt_info)
            for ct_name, ct_info in mod_ctors.items():
                parent = ct_info.parent_type
                if name_filter is None or parent in name_filter:
                    self.env.constructors.setdefault(ct_name, ct_info)

    def _check_module_bodies(self, mod: ResolvedModule) -> None:
        """Type-check *mod*'s bodies as *mod* itself would be checked (#1244).

        A fresh checker over the module's own program, given the module's own
        imports — so every name its bodies mention is resolved against the
        namespace ITS file declares and imports, not the entry program's.  Its
        diagnostics are surfaced here, deduplicated against what this program
        has already reported (the E151/E152/E153/E154 harvest above re-derives
        some of them), so a module reached from two importers, or reported at
        registration and again here, is still described once.

        Kept OFF the ``temp`` used for the harvest above on purpose: checking
        a program injects its imports into its own ``env.functions``, and the
        harvest reads that dict to decide what the module EXPORTS — reusing
        one checker for both would re-export every name the module imported.

        Each module is checked once per top-level run, memoised by path
        through the nested checkers.  The memo is entered BEFORE the check, so
        an import cycle terminates here rather than recursing (the resolver's
        own E011 cycle diagnostic is what reports it).
        """
        from vera.checker.core import TypeChecker

        memo: set[tuple[str, ...]] | None = self._module_body_check_memo
        if memo is None:
            memo = set()
            self._module_body_check_memo = memo
        if mod.path in memo:
            return
        memo.add(mod.path)
        checker = TypeChecker(
            source=mod.source,
            file=str(mod.file_path),
            resolved_modules=self._modules_visible_to(mod),
        )
        checker._module_body_check_memo = memo
        checker.check_program(mod.program)
        seen = {
            (e.error_code, str(e.location.file), e.location.line,
             e.location.column, e.severity, e.description)
            for e in self.errors
        }
        for err in checker.errors:
            key = (err.error_code, str(err.location.file), err.location.line,
                   err.location.column, err.severity, err.description)
            if key in seen:
                continue
            seen.add(key)
            self.errors.append(err)

    def _modules_visible_to(
        self, mod: ResolvedModule,
    ) -> list[ResolvedModule]:
        """The resolved modules *mod* imports, re-scoped to *mod* (#1244).

        The same objects this program resolved, with ``direct`` recomputed
        against ``mod``'s own import list: what is transitive from here may be
        a direct import there, and §8.6.4 visibility is a property of the
        importer, not of the module.  A path this program never resolved is
        skipped — the resolver reaches every transitive import, so a missing
        one means the module was unreachable, and the name then misses loudly
        in the check below rather than binding something else.
        """
        by_path = {m.path: m for m in self._resolved_modules}
        direct = {tuple(imp.path) for imp in mod.program.imports}
        out: list[ResolvedModule] = []
        seen: set[tuple[str, ...]] = set()
        frontier = [p for p in direct if p in by_path]
        while frontier:
            path = frontier.pop()
            if path in seen:
                continue
            seen.add(path)
            dep = by_path[path]
            out.append(replace(dep, direct=path in direct))
            frontier.extend(
                tuple(imp.path) for imp in dep.program.imports
                if tuple(imp.path) in by_path
            )
        return out

    @staticmethod
    def _find_import_decl(
        program: ast.Program, path: tuple[str, ...],
    ) -> ast.Node:
        """Find the ImportDecl node for a given module path."""
        for imp in program.imports:
            if imp.path == path:
                return imp
        return program  # fallback
