"""Mixin for function compilability checks.

Determines whether a function can be compiled to WASM based on its
effects, parameter types, and return type.  Also scans function bodies
for State handler expressions.
"""

from __future__ import annotations

from collections.abc import Iterator, Sequence

from vera import ast
from vera.wasm.async_fusion import await_needs_check, fused_async_target


def contract_exprs(
    contracts: Sequence[ast.Contract],
) -> Iterator[ast.Expr]:
    """Every predicate expression carried by a function's contracts.

    One enumeration shared by both import pre-scans (#1210 round 2), because
    a contract is LOWERED code: `requires` / `ensures` become runtime checks
    and `decreases` becomes the termination guard's measure, so anything in
    one that needs a host import or a State/Exn family needs it registered.

    `Decreases` is why this is a function rather than a `getattr(c, "expr")`:
    it carries `exprs` (a tuple — a lexicographic measure is several
    expressions), so the attribute-name shortcut silently skipped it and a
    `handle[State<Nat>]` in a `decreases` measure emitted `state_push_Nat`
    against an import that was never declared.
    """
    for contract in contracts:
        expr = getattr(contract, "expr", None)
        if expr is not None:
            yield expr
        for sub in getattr(contract, "exprs", ()):
            yield sub


class CompilabilityMixin:
    """Methods for checking if functions are compilable to WASM."""

    def _is_compilable(self, decl: ast.FnDecl) -> bool:
        """Check if a function can be compiled to WASM.

        Accepts pure functions, IO effects, and State<T> where T is
        a compilable primitive type (Int, Nat, Bool, Float64).
        """
        # Check effect: must be pure, <IO>, or <State<T>>
        effect = decl.effect
        if isinstance(effect, ast.PureEffect):
            pass  # OK
        elif isinstance(effect, ast.EffectSet):
            for eff in effect.effects:
                if isinstance(eff, ast.EffectRef):
                    if eff.name == "IO":
                        self._needs_memory = True
                    elif eff.name == "State":
                        # State<T> — T must be a compilable primitive
                        if not self._check_state_type(decl, eff):
                            return False
                    elif eff.name == "Exn":
                        # Exn<E> — E must be a compilable type
                        if not self._check_exn_type(decl, eff):
                            return False
                    elif eff.name == "Http":
                        self._needs_memory = True
                    elif eff.name == "Async":
                        pass  # Sequential execution, no host imports
                    elif eff.name == "HttpServer":
                        # #305 — marker effect; the accept loop lives in
                        # the host `vera serve` driver.  The handler
                        # touches Request/Response heap values.
                        self._needs_memory = True
                    elif eff.name == "Inference":
                        self._needs_memory = True
                    elif eff.name == "DB":
                        # #229 — host-import SQL effect; the ops read
                        # Option<String> params and return row grids on
                        # the heap.
                        self._needs_memory = True
                    elif eff.name == "Random":
                        # #465 — host-import effect, no memory need
                        # (no allocations or heap returns).
                        pass
                    else:
                        self._warning(
                            decl,
                            f"Function '{decl.name}' uses unsupported "
                            f"effect '{eff.name}' — skipped.",
                            rationale="Only pure, IO, Http, Inference, DB, "
                            "Random, State<T>, Exn<E>, and Async "
                            "effects are compilable.",
                            error_code="E603",
                        )
                        return False
                else:
                    return False
        else:
            return False

        # Check parameter types
        for p in decl.params:
            wt = self._type_expr_to_wasm_type(p)
            if wt == "unsupported":
                self._warning(
                    decl,
                    f"Function '{decl.name}' has unsupported parameter type "
                    f"— skipped.",
                    rationale=(
                        "WASM code generation supports a fixed set of "
                        "parameter types; this parameter's type is not among "
                        "them, so the function is skipped rather than "
                        "miscompiled."
                    ),
                    error_code="E604",
                )
                return False

        # Check return type
        ret_wt = self._type_expr_to_wasm_type(decl.return_type)
        if ret_wt == "unsupported":
            self._warning(
                decl,
                f"Function '{decl.name}' has unsupported return type "
                f"— skipped.",
                rationale=(
                    "WASM code generation supports a fixed set of return "
                    "types; this function's return type is not among them, "
                    "so the function is skipped rather than miscompiled."
                ),
                error_code="E605",
            )
            return False

        return True

    def _check_state_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate a State<T> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses State without "
                f"a type argument — skipped.",
                rationale="State<T> requires exactly one type argument.",
                error_code="E606",
            )
            return False
        type_arg = eff.type_args[0]
        if not self._register_state_cell(type_arg):
            self._warn_unsupported_state_cell(decl, decl.name)
            return False
        return True

    def _register_state_cell(self, type_arg: ast.TypeExpr) -> bool:
        """Register the `State<type_arg>` host-cell family; False if it has none.

        The ONE place a State cell's compilability is decided and its family
        recorded, shared by the declared-effect gate (`_check_state_type`)
        and the handler walk (`_scan_expr_for_handlers`) — the two paths must
        accept exactly the same cell types, or a handler discharging the
        effect inside a `pure` function registers nothing while its lowering
        emits the calls anyway (#1210: `handle[State<String>]` was
        check-green invalid WASM).

        The import FAMILY is the cell the CHECKER typed (#1209), so every
        alias spelling that resolves to it — scalar (#1205), composite,
        parameterised — registers ONE family.  `wt` is derived from the
        RESOLVED type, so registering an unresolved name split the family
        (`state_put_Count` typed i64) from the name the per-function lowering
        derives; resolving both keeps them one.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt in ("unsupported", "i32_pair"):
            return False
        type_name = self._family_name_te(type_arg)
        if type_name and (type_name, wt) not in self._state_types:
            self._state_types.append((type_name, wt))
        return True

    def _warn_unsupported_state_cell(
        self, node: ast.Node, fn_name: str,
    ) -> None:
        """The E607 both State-cell paths emit — one wording, one code."""
        self._warning(
            node,
            f"Function '{fn_name}' uses State with "
            "unsupported type — skipped.",
            rationale="State<T> requires a compilable primitive type "
            "(Int, Nat, Bool, Float64).",
            error_code="E607",
        )

    def _check_exn_type(
        self, decl: ast.FnDecl, eff: ast.EffectRef
    ) -> bool:
        """Validate an Exn<E> effect and register its type.

        Returns True if compilable, False otherwise.
        """
        if not eff.type_args or len(eff.type_args) != 1:
            self._warning(
                decl,
                f"Function '{decl.name}' uses Exn without "
                f"a type argument — skipped.",
                rationale="Exn<E> requires exactly one type argument.",
                error_code="E611",
            )
            return False
        type_arg = eff.type_args[0]
        if not self._register_exn_tag(type_arg):
            self._warn_unsupported_exn_tag(decl, decl.name)
            return False
        return True

    def _warn_unsupported_exn_tag(
        self, node: ast.Node, fn_name: str,
    ) -> None:
        """The E612 both Exn-tag paths emit — one wording, one code.

        The `_warn_unsupported_state_cell` twin.  Both registration paths
        (the declared-effect gate and the handler walk) must reach the same
        verdict on the same payload type, or a handler discharging `Exn<E>`
        inside a `pure` function registers no tag while its lowering emits
        `throw $exn_E` / `catch $exn_E` regardless — `unknown tag $exn_Unit`
        at whole-module WAT compilation, from a check-green program (#1210).
        """
        self._warning(
            node,
            f"Function '{fn_name}' uses Exn with "
            f"unsupported type — skipped.",
            rationale="Exn<E> requires a compilable type "
            "(Int, Nat, Bool, Float64, String).",
            error_code="E612",
        )

    def _register_exn_tag(self, type_arg: ast.TypeExpr) -> bool:
        """Register the `Exn<type_arg>` WASM tag; False if it has none.

        The State twin (`_register_state_cell`): one derivation shared by the
        declared-effect gate and the handler walk, so a tag reached only from
        a handler nested in a clause body is declared rather than emitted
        undeclared (#1210).

        The tag FAMILY resolves exactly like the State import family —
        `Exn<Code>` with `type Code = Int` otherwise declares an i64 tag the
        i32-typed catch sites of the unresolved-name derivation cannot match,
        and `Exn<Payload>` with `type Payload = Option<Int>` declares a
        second tag beside the `Option<Int>` one its throw sites target
        (#1209).  Unlike a State cell, an `i32_pair` payload IS compilable:
        the tag takes two i32 params.
        """
        wt = self._type_expr_to_wasm_type(type_arg)
        if wt is None or wt == "unsupported":
            return False
        wasm_tag_t = "i32 i32" if wt == "i32_pair" else wt
        type_name = self._family_name_te(type_arg)
        if type_name and (type_name, wasm_tag_t) not in self._exn_types:
            self._exn_types.append((type_name, wasm_tag_t))
        return True

    _MD_BUILTINS = frozenset({
        "md_parse", "md_render", "md_has_heading",
        "md_has_code_block", "md_extract_code_blocks",
    })

    _REGEX_BUILTINS = frozenset({
        "regex_match", "regex_find", "regex_find_all", "regex_replace",
    })

    _MAP_BUILTINS = frozenset({
        "map_new", "map_insert", "map_get", "map_contains",
        "map_remove", "map_size", "map_keys", "map_values",
    })

    _SET_BUILTINS = frozenset({
        "set_new", "set_add", "set_contains",
        "set_remove", "set_size", "set_to_array",
    })

    _DECIMAL_BUILTINS = frozenset({
        "decimal_from_int", "decimal_from_float", "decimal_from_string",
        "decimal_to_string", "decimal_to_float",
        "decimal_add", "decimal_sub", "decimal_mul", "decimal_div",
        "decimal_neg", "decimal_compare", "decimal_eq",
        "decimal_round", "decimal_abs",
    })

    _JSON_BUILTINS = frozenset({
        "json_parse", "json_stringify",
    })

    _HTML_BUILTINS = frozenset({
        "html_parse", "html_to_string", "html_query", "html_text",
    })

    # Math host-imported builtins (#467).  Only the log/trig ops —
    # pi/e and sign/clamp/float_clamp are inlined as WAT, no
    # host import needed.
    _MATH_BUILTINS = frozenset({
        "log", "log2", "log10",
        "sin", "cos", "tan", "asin", "acos", "atan", "atan2",
    })

    def _scan_io_ops(self, node: ast.Node) -> None:
        """Walk a function body looking for IO, Markdown, and Regex builtins.

        Registers each distinct IO operation name (print, read_line, etc.)
        into ``_io_ops_used`` for per-operation import emission.  Also
        registers Markdown host-import builtins into ``_md_ops_used``
        and regex host-import builtins into ``_regex_ops_used``.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (recurses into sub-exprs that may contain registrable calls):
        #   QualifiedCall     → registers IO/Http/Inference/Random op
        #                       then recurses into args
        #   FnCall            → registers Markdown/Regex/Map/Set/Decimal/
        #                       Json/Html/Math builtin then recurses args
        #   Block             → recurses into each stmt + trailing expr
        #   ConstructorCall   → recurses into each arg
        #   BinaryExpr        → recurses into left + right
        #   UnaryExpr         → recurses into operand
        #   IfExpr            → recurses into cond + then + else
        #   MatchExpr         → recurses into scrutinee + arm bodies
        #   HandleExpr        → recurses into body
        #   IndexExpr         → recurses into collection + index
        #                       (defensive add #597 — masked today by
        #                       type checker rejecting IO in index
        #                       positions, but plugs the gap if a
        #                       host-imported Int-returning builtin
        #                       lands in the future)
        #   ArrayLit          → recurses into each element (defensive
        #                       add #597 — masked today by the [E602]
        #                       path dropping IO-in-ArrayLit functions)
        #   InterpolatedString → recurses into each Expr part
        #                       (defensive add #597 — same masking as
        #                       ArrayLit)
        #   AnonFn            → recurses into body (defensive add
        #                       #597 — IS the primary defence: pr-
        #                       review of #668 surfaced that
        #                       `_compile_lifted_closure` in
        #                       `vera/codegen/closures.py` does NOT
        #                       call this scanner on lifted bodies,
        #                       so without this branch IO ops
        #                       inside a closure body would silently
        #                       miss their host-import registration)
        #   AssertExpr        → recurses into the condition (#1210
        #                       round 2 — pure ≠ host-import-free: an
        #                       `md_*` / `regex_*` builtin, or a
        #                       handler clause reached through one,
        #                       registers its import only here)
        #   AssumeExpr        → recurses into the condition
        #   ForallExpr        → recurses into domain + predicate
        #   ExistsExpr        → recurses into domain + predicate
        #
        # Intentionally ignored (leaves — no sub-exprs to recurse into):
        #   IntLit            → leaf
        #   FloatLit          → leaf
        #   BoolLit           → leaf
        #   StringLit         → leaf
        #   UnitLit           → leaf
        #   SlotRef           → leaf
        #   ResultRef         → leaf
        #   NullaryConstructor → zero-arg, no sub-exprs
        #   ModuleCall        → cross-module IO tracked separately
        #                       via the imported module's own scan
        #   OldExpr           → names an EffectRef, not an expression
        #   NewExpr           → names an EffectRef, not an expression
        #
        # Cannot occur:
        #   HoleExpr          → parser placeholder, check-time rejects
        """
        if isinstance(node, ast.QualifiedCall):
            if node.qualifier == "IO":
                self._io_ops_used.add(node.name)
            elif node.qualifier == "Http":
                self._http_ops_used.add(f"http_{node.name}")
            elif node.qualifier == "Inference":
                self._inference_ops_used.add(f"inference_{node.name}")
            elif node.qualifier == "DB":
                self._db_ops_used.add(f"db_{node.name}")  # #229
            elif node.qualifier == "Random":
                # #465 — op names already begin with `random_`
                # (`random_int`/`random_float`/`random_bool`), which
                # both reads naturally at the call site and prevents
                # collision with bare `int`/`float`/`bool` user
                # effect ops.  Track the name directly.
                self._random_ops_used.add(node.name)
            for arg in node.args:
                self._scan_io_ops(arg)
            return
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._scan_io_ops(stmt.value)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_io_ops(stmt.expr)
            self._scan_io_ops(node.expr)
        elif isinstance(node, ast.FnCall):
            # #841: fused-async interception — must agree exactly with
            # the WasmContext translation (shared predicates in
            # vera/wasm/async_fusion.py).  A fused async(Http.get(...))
            # registers the async_http_* import INSTEAD of the sync
            # http_* the QualifiedCall branch would register when the
            # walk reached the inner call; an await that needs the
            # fused-handle runtime check additionally registers
            # async_await (its argument is still scanned normally).
            fused = fused_async_target(node)
            if fused is not None:
                self._async_ops_used.add(fused)
                inner = node.args[0]
                assert isinstance(inner, ast.QualifiedCall)  # noqa: S101
                for arg in inner.args:
                    self._scan_io_ops(arg)
                return
            # NOTE: this pre-scan registration is redundant-but-benign for
            # await — the WasmContext translation's single registration
            # site in calls_markup.py already guarantees the import ⟺
            # check ⟺ host coherence.  It is kept so the two passes call
            # the shared predicate with identical inputs (the module
            # docstring's "both passes MUST agree" invariant) rather
            # than one of them silently drifting.
            if (
                node.name == "await"
                and len(node.args) == 1
                and await_needs_check(
                    node.args[0],
                    self._future_ret_fns,
                    self._future_ret_module_fns,
                    self._type_aliases,
                    self._type_alias_params,
                )
            ):
                self._async_ops_used.add("async_await")
            if node.name in self._MD_BUILTINS:
                self._md_ops_used.add(node.name)
            if node.name in self._REGEX_BUILTINS:
                self._regex_ops_used.add(node.name)
            if node.name in self._MAP_BUILTINS:
                self._map_ops_used.add(node.name)
            if node.name in self._SET_BUILTINS:
                self._set_ops_used.add(node.name)
            if node.name in self._DECIMAL_BUILTINS:
                self._decimal_ops_used.add(node.name)
            if node.name in self._JSON_BUILTINS:
                self._json_ops_used.add(node.name)
            if node.name in self._HTML_BUILTINS:
                self._html_ops_used.add(node.name)
            if node.name in self._MATH_BUILTINS:
                self._math_ops_used.add(node.name)
            for arg in node.args:
                self._scan_io_ops(arg)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_io_ops(arg)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_io_ops(node.left)
            self._scan_io_ops(node.right)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_io_ops(node.operand)
        elif isinstance(node, ast.IfExpr):
            self._scan_io_ops(node.condition)
            self._scan_io_ops(node.then_branch)
            if node.else_branch:
                self._scan_io_ops(node.else_branch)
        elif isinstance(node, ast.MatchExpr):
            self._scan_io_ops(node.scrutinee)
            for arm in node.arms:
                self._scan_io_ops(arm.body)
        elif isinstance(node, ast.HandleExpr):
            # All four sub-expression positions, matching
            # `_scan_expr_for_handlers` (#1210): a host-imported builtin
            # reached only from a state-init expression, a clause body, or a
            # clause's `with` update would otherwise emit an orphaned
            # `call $vera.<name>` with no import declaration.
            if node.state is not None:
                self._scan_io_ops(node.state.init_expr)
            for clause in node.clauses:
                self._scan_io_ops(clause.body)
                if clause.state_update is not None:
                    self._scan_io_ops(clause.state_update[1])
            self._scan_io_ops(node.body)
        # Defensive sub-expr recursion (#597) — three of the four
        # branches below (IndexExpr, ArrayLit, InterpolatedString)
        # are masked today by type-checker rules and the [E602]
        # codegen-skip path; the AnonFn branch is the PRIMARY
        # defence — the closure compile pipeline does not call
        # this scanner on lifted bodies (verified by pr-review
        # audit on #668), so IO ops inside a closure body would
        # silently miss their host-import registration without
        # this branch.
        elif isinstance(node, ast.IndexExpr):
            self._scan_io_ops(node.collection)
            self._scan_io_ops(node.index)
        elif isinstance(node, ast.ArrayLit):
            for elem in node.elements:
                self._scan_io_ops(elem)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                # Parts are str (literal) or Expr (interpolated).
                if not isinstance(part, str):
                    self._scan_io_ops(part)
        elif isinstance(node, ast.AnonFn):
            self._scan_io_ops(node.body)
        # #1210 round 2 — symmetrical with `_scan_expr_for_handlers`.  The
        # handler walk now descends these positions, so a handler reached
        # through one is lowered; anything its clause bodies call has to be
        # registered from here or the module references an undeclared import.
        elif isinstance(node, (ast.AssertExpr, ast.AssumeExpr)):
            self._scan_io_ops(node.expr)
        elif isinstance(node, (ast.ForallExpr, ast.ExistsExpr)):
            self._scan_io_ops(node.domain)
            self._scan_io_ops(node.predicate)

    def _scan_body_for_state_handlers(
        self, node: ast.Node, decl: ast.FnDecl | None = None,
    ) -> bool:
        """Walk a function registering every handler's State/Exn family.

        The ENTRY POINT for the handler walk — ``_scan_expr_for_handlers``
        does the recursion, this owns the per-function verdict.

        Covers the body AND every contract predicate (``requires`` /
        ``ensures`` / ``decreases``), which ``contract_exprs`` enumerates.
        Runtime-checked contracts are lowered into the function like any
        other code, so a ``handle[State<Nat>]`` written in a ``requires``
        predicate emits ``call $vera.state_push_Nat`` — the body-only walk
        registered nothing for it and the module failed to compile with
        ``unknown func``, from a check-green, verify-clean program (#1210
        round 2).

        Returns ``False`` when a ``handle[State<T>]`` / ``handle[Exn<E>]``
        reached from *node* names a cell or payload type the backend cannot
        compile, having emitted the same ``E607`` / ``E612`` the
        declared-effect gate emits; the caller drops the function.  Both used
        to be skipped in SILENCE while the lowering emitted ``state_push_…``
        / ``throw $exn_…`` for them regardless.
        """
        self._unregistrable_state_cells: list[ast.TypeExpr] = []
        self._unregistrable_exn_tags: list[ast.TypeExpr] = []
        self._scan_expr_for_handlers(node)
        if decl is not None:
            for pred in contract_exprs(decl.contracts):
                self._scan_expr_for_handlers(pred)
        fn_name = decl.name if decl is not None else "<unknown>"
        if self._unregistrable_state_cells:
            offender = self._unregistrable_state_cells[0]
            self._warn_unsupported_state_cell(
                offender if getattr(offender, "span", None)
                else (decl or offender),
                fn_name,
            )
            return False
        if self._unregistrable_exn_tags:
            offender = self._unregistrable_exn_tags[0]
            self._warn_unsupported_exn_tag(
                offender if getattr(offender, "span", None)
                else (decl or offender),
                fn_name,
            )
            return False
        return True

    def _register_scanned_handler(self, node: ast.HandleExpr) -> None:
        """Register the State/Exn family of one ``handle`` expression.

        Shares `_register_state_cell` / `_register_exn_tag` with the
        declared-effect gate, so both registration paths key ONE family
        (#1209) and accept exactly one set of cell types (#1210) — a handler
        declared in a body must not register an import its own lowering never
        calls, nor emit calls to one it never registered.

        The two arms are symmetric on purpose: each records the type it could
        NOT register so the entry point can emit the declared-effect gate's
        own diagnostic and drop the function.  The Exn arm used to discard the
        verdict, so `handle[Exn<Unit>]` in a `pure` function registered no tag
        and still compiled — `unknown tag $exn_Unit` at WAT, where the
        declared-row twin was a clean E612 function drop.
        """
        if not isinstance(node.effect, ast.EffectRef):
            return
        if not node.effect.type_args or len(node.effect.type_args) != 1:
            # Arity is the checker's E337; nothing to register either way.
            return
        type_arg = node.effect.type_args[0]
        if node.effect.name == "State":
            if not self._register_state_cell(type_arg):
                self._unregistrable_state_cells.append(type_arg)
        elif node.effect.name == "Exn":
            if not self._register_exn_tag(type_arg):
                self._unregistrable_exn_tags.append(type_arg)

    def _scan_expr_for_handlers(self, node: ast.Node) -> None:
        """Recurse into expressions looking for HandleExpr nodes.

        # WALKER_COVERAGE: (#597 — every Expr subclass below has a
        # disposition; check_walker_coverage.py enforces completeness.)
        #
        # Handled (recurses into sub-exprs that may contain HandleExpr):
        #   HandleExpr        → registers State<T>/Exn<E> types, then
        #                       recurses into ALL FOUR sub-expression
        #                       positions: the state-init expression, each
        #                       clause body, each clause's `with` update,
        #                       and the handled body.  The walk used to
        #                       descend the body ALONE (#1210), so a family
        #                       reached only from one of the other three was
        #                       never registered while the lowering emitted
        #                       its calls — `unknown func
        #                       $vera.state_push_Nat` at whole-module WAT
        #                       compilation, from a check-green program.
        #   Block             → recurses into stmts + trailing expr
        #   FnCall            → recurses into each arg
        #   ConstructorCall   → recurses into each arg
        #   BinaryExpr        → recurses into left + right
        #   UnaryExpr         → recurses into operand
        #   IfExpr            → recurses into cond + then + else
        #   MatchExpr         → recurses into scrutinee + arm bodies
        #   QualifiedCall     → recurses into args (defensive add #597)
        #   IndexExpr         → recurses into collection + index
        #                       (defensive add #597)
        #   ArrayLit          → recurses into each element
        #                       (defensive add #597)
        #   InterpolatedString → recurses into each Expr part
        #                       (defensive add #597)
        #   AnonFn            → recurses into body (defensive add #597 —
        #                       IS the primary defence: the closure
        #                       compile pipeline does not run its own
        #                       handler scan on lifted bodies, so
        #                       without this branch HandleExprs inside
        #                       a closure body would silently miss
        #                       their State/Exn host-import
        #                       registration)
        #   AssertExpr        → recurses into the condition (#1210
        #                       round 2 — "pure" is not "handler-free":
        #                       `assert(handle[State<Nat>] … > 0)` is
        #                       check-green and LOWERED, so refusing to
        #                       descend left `state_push_Nat` undeclared)
        #   AssumeExpr        → recurses into the condition (same shape;
        #                       verifier-only today, kept symmetric so
        #                       the two cannot drift)
        #   ForallExpr        → recurses into domain + predicate
        #   ExistsExpr        → recurses into domain + predicate
        #
        # Intentionally ignored (leaves — no sub-exprs to walk):
        #   IntLit            → leaf
        #   FloatLit          → leaf
        #   BoolLit           → leaf
        #   StringLit         → leaf
        #   UnitLit           → leaf
        #   SlotRef           → leaf
        #   ResultRef         → leaf
        #   NullaryConstructor → zero-arg, no sub-exprs
        #   ModuleCall        → handlers in imported module tracked
        #                       by that module's own scan
        #   OldExpr           → names an EffectRef, not an expression
        #   NewExpr           → names an EffectRef, not an expression
        #
        # Cannot occur:
        #   HoleExpr          → parser placeholder, check-time rejects
        """
        if isinstance(node, ast.HandleExpr):
            self._register_scanned_handler(node)
            if node.state is not None:
                self._scan_expr_for_handlers(node.state.init_expr)
            for clause in node.clauses:
                self._scan_expr_for_handlers(clause.body)
                if clause.state_update is not None:
                    self._scan_expr_for_handlers(clause.state_update[1])
            self._scan_expr_for_handlers(node.body)
            return
        if isinstance(node, ast.Block):
            for stmt in node.statements:
                if isinstance(stmt, ast.LetStmt):
                    self._scan_expr_for_handlers(stmt.value)
                elif isinstance(stmt, ast.ExprStmt):
                    self._scan_expr_for_handlers(stmt.expr)
            self._scan_expr_for_handlers(node.expr)
        elif isinstance(node, ast.FnCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.ConstructorCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.BinaryExpr):
            self._scan_expr_for_handlers(node.left)
            self._scan_expr_for_handlers(node.right)
        elif isinstance(node, ast.UnaryExpr):
            self._scan_expr_for_handlers(node.operand)
        elif isinstance(node, ast.IfExpr):
            self._scan_expr_for_handlers(node.condition)
            self._scan_expr_for_handlers(node.then_branch)
            if node.else_branch:
                self._scan_expr_for_handlers(node.else_branch)
        elif isinstance(node, ast.MatchExpr):
            self._scan_expr_for_handlers(node.scrutinee)
            for arm in node.arms:
                self._scan_expr_for_handlers(arm.body)
        # Defensive sub-expr recursion (#597) — symmetrical with
        # `_scan_io_ops`.  The QualifiedCall / IndexExpr / ArrayLit
        # / InterpolatedString branches are masked today by type-
        # checker rules and the [E602] codegen-skip path.  The
        # AnonFn branch is the PRIMARY defence — the closure
        # compile pipeline does not call this scanner on lifted
        # bodies, so HandleExprs inside a closure body would
        # silently miss their State/Exn host-import registration
        # without this branch.
        elif isinstance(node, ast.QualifiedCall):
            for arg in node.args:
                self._scan_expr_for_handlers(arg)
        elif isinstance(node, ast.IndexExpr):
            self._scan_expr_for_handlers(node.collection)
            self._scan_expr_for_handlers(node.index)
        elif isinstance(node, ast.ArrayLit):
            for elem in node.elements:
                self._scan_expr_for_handlers(elem)
        elif isinstance(node, ast.InterpolatedString):
            for part in node.parts:
                if not isinstance(part, str):
                    self._scan_expr_for_handlers(part)
        elif isinstance(node, ast.AnonFn):
            self._scan_expr_for_handlers(node.body)
        # #1210 round 2 — the contract-predicate positions.  These are not
        # "cannot occur": a handle expression is an ordinary Bool-valued
        # expression, so it type-checks inside an `assert` condition or a
        # quantifier predicate, and codegen lowers it there.  Refusing to
        # descend registered nothing while the lowering emitted the calls.
        elif isinstance(node, (ast.AssertExpr, ast.AssumeExpr)):
            self._scan_expr_for_handlers(node.expr)
        elif isinstance(node, (ast.ForallExpr, ast.ExistsExpr)):
            self._scan_expr_for_handlers(node.domain)
            self._scan_expr_for_handlers(node.predicate)
