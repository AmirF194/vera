"""Synthetic-AST tests for the defensive `isinstance` branches
added by #597 to compiler walker functions.

These branches are unreachable via end-to-end programs today —
every flow is masked by an upstream guard (type checker
rejection, `[E602]` codegen-skip, etc.).  Without these tests,
a future refactor that breaks a defensive branch would land
silently (no production path exercises them).

Strategy: construct synthetic AST nodes directly and invoke the
walker, asserting the defensive branch produces the correct
result.  Pins each branch's behaviour against future regression.

The 11 defensive branches:

- ``_scan_io_ops`` (compilability.py): IndexExpr, ArrayLit,
  InterpolatedString, AnonFn → recurses into sub-exprs to find
  IO/host-import builtins.
- ``_scan_expr_for_handlers`` (compilability.py): QualifiedCall,
  IndexExpr, ArrayLit, InterpolatedString, AnonFn → recurses
  into sub-exprs to find HandleExpr nodes.
- ``_infer_expr_wasm_type`` (inference.py): AnonFn → "i32",
  ModuleCall → None.
- ``_infer_vera_type`` (inference.py): Block / MatchExpr /
  HandleExpr / AssertExpr / AssumeExpr / AnonFn / QualifiedCall /
  ModuleCall.

The file also carries the FIELD-coverage gate for the two
``compilability.py`` pre-scans (``TestPreScanWalkerFieldCoverage``,
#1210 round 5).  ``scripts/check_walker_coverage.py`` already audits
every walker carrying a ``# WALKER_COVERAGE:`` marker, but its
canonical set is the ``Expr`` subclasses and its verdict is
"the class is NAMED" — a class named in the checklist with an
"intentionally ignored" disposition counts as covered whether or
not it carries live sub-expressions.  Both of round 5's holes slipped
through exactly there: ``LetDestruct`` is a ``Stmt``, invisible to
that canonical set, and ``ModuleCall`` was named with a disposition
that was true of the callee and false of its arguments.  The gate
below closes both, and is a test rather than an extension of the
script because the script's set would then force a ``Stmt``
disposition onto all thirteen marked walkers.
"""

from __future__ import annotations

import dataclasses
import importlib.util
import inspect
import re
import sys
import typing
from pathlib import Path

import pytest

from vera import ast
from vera.codegen import compilability
from vera.codegen.core import CodeGenerator
from vera.wasm.context import WasmContext
from vera.wasm.helpers import StringPool


# =====================================================================
# Helpers
# =====================================================================


def _make_cg() -> CodeGenerator:
    """Build a fresh CodeGenerator for compilability scans."""
    return CodeGenerator()


def _make_ctx() -> WasmContext:
    """Build a fresh WasmContext for inference helpers."""
    return WasmContext(string_pool=StringPool())


def _io_print(arg: ast.Expr = ast.UnitLit()) -> ast.QualifiedCall:
    return ast.QualifiedCall(qualifier="IO", name="print", args=(arg,))


def _slot(type_name: str = "Int", index: int = 0) -> ast.SlotRef:
    return ast.SlotRef(
        type_name=type_name, type_args=None, index=index)


# =====================================================================
# `_scan_io_ops` defensive branches (#597)
# =====================================================================


class TestScanIoOpsDefensiveBranches:
    """Each branch recurses into a sub-expression position so IO/
    host-import builtins buried inside are still registered."""

    def test_indexexpr_collection_recursion(self) -> None:
        cg = _make_cg()
        # `coll[0]` where coll is an IO call (purely synthetic —
        # type checker would reject this construction at the source
        # level, but the scanner must still find it for the defensive
        # branch to be testable).
        node = ast.IndexExpr(
            collection=_io_print(), index=ast.IntLit(value=0))
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_indexexpr_index_recursion(self) -> None:
        cg = _make_cg()
        node = ast.IndexExpr(
            collection=_slot("Array"), index=_io_print())
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_arraylit_elements_recursion(self) -> None:
        cg = _make_cg()
        node = ast.ArrayLit(elements=(_io_print(),))
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_interpolated_string_parts_recursion(self) -> None:
        cg = _make_cg()
        # InterpolatedString.parts is `tuple[Expr | str, ...]` —
        # string fragments are bare ``str`` and Expr parts are AST
        # nodes.  The defensive branch must skip the str parts and
        # recurse into the Expr parts.
        node = ast.InterpolatedString(
            parts=("prefix: ", _io_print(), " suffix"))
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used

    def test_anonfn_body_recursion(self) -> None:
        cg = _make_cg()
        # The AnonFn defensive branch is the PRIMARY defence —
        # `_compile_lifted_closure` does NOT call `_scan_io_ops`
        # on lifted bodies.  Without this branch, IO ops inside
        # a closure body would silently miss their host-import
        # registration.
        body = ast.Block(statements=(), expr=_io_print())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        cg._scan_io_ops(node)
        assert "print" in cg._io_ops_used


# =====================================================================
# `_scan_expr_for_handlers` defensive branches (#597)
# =====================================================================


def _handle_expr() -> ast.HandleExpr:
    """Build a minimal HandleExpr for State<Int>."""
    return ast.HandleExpr(
        effect=ast.EffectRef(
            name="State",
            type_args=(ast.NamedType(name="Int", type_args=None),)),
        state=None,
        clauses=(),
        body=ast.Block(statements=(), expr=ast.UnitLit()),
    )


class TestScanExprForHandlersDefensiveBranches:
    """Each branch recurses into a sub-expression position so
    HandleExprs buried inside are still discovered for type
    registration."""

    def test_qualifiedcall_args_recursion(self) -> None:
        cg = _make_cg()
        node = ast.QualifiedCall(
            qualifier="IO", name="print", args=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        # State<Int> registered
        assert ("Int", "i64") in cg._state_types

    def test_indexexpr_recursion(self) -> None:
        cg = _make_cg()
        node = ast.IndexExpr(
            collection=_handle_expr(), index=ast.IntLit(value=0))
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types

    def test_arraylit_recursion(self) -> None:
        cg = _make_cg()
        node = ast.ArrayLit(elements=(_handle_expr(),))
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types

    def test_interpolated_string_recursion(self) -> None:
        cg = _make_cg()
        node = ast.InterpolatedString(parts=("x: ", _handle_expr()))
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types

    def test_anonfn_body_recursion(self) -> None:
        cg = _make_cg()
        body = ast.Block(statements=(), expr=_handle_expr())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        cg._scan_expr_for_handlers(node)
        assert ("Int", "i64") in cg._state_types


# =====================================================================
# `_infer_expr_wasm_type` defensive branches (#597)
# =====================================================================


class TestInferExprWasmTypeDefensiveBranches:
    """AnonFn → "i32" (closure handle), ModuleCall → None (path
    field can't be threaded through bare-name FnCall dispatch)."""

    def test_anonfn_returns_i32(self) -> None:
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_expr_wasm_type(node) == "i32"

    def test_modulecall_returns_none(self) -> None:
        """ModuleCall carries `expr.path` that the bare-name FnCall
        dispatcher can't consume.  Returning None surfaces the
        unknown-type cleanly rather than masking with a wrong same-
        name lookup."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_expr_wasm_type(node) is None


# =====================================================================
# `_infer_vera_type` defensive branches (#597)
# =====================================================================


class TestInferVeraTypeDefensiveBranches:
    """Block / MatchExpr / HandleExpr → trailing-expr type;
    AssertExpr / AssumeExpr → "Unit"; AnonFn / QualifiedCall /
    ModuleCall → None (path/qualifier fields can't be threaded
    through the bare-name FnCall dispatcher)."""

    def test_block_returns_trailing_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.Block(statements=(), expr=ast.IntLit(value=42))
        assert ctx._infer_vera_type(node) == "Int"

    def test_matchexpr_returns_first_arm_body_type(self) -> None:
        ctx = _make_ctx()
        arm = ast.MatchArm(
            pattern=ast.WildcardPattern(),
            body=ast.BoolLit(value=True),
        )
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=(arm,))
        assert ctx._infer_vera_type(node) == "Bool"

    def test_matchexpr_no_arms_returns_none(self) -> None:
        ctx = _make_ctx()
        node = ast.MatchExpr(
            scrutinee=ast.IntLit(value=0), arms=())
        assert ctx._infer_vera_type(node) is None

    def test_handleexpr_returns_body_expr_type(self) -> None:
        ctx = _make_ctx()
        node = ast.HandleExpr(
            effect=ast.EffectRef(name="State", type_args=()),
            state=None,
            clauses=(),
            body=ast.Block(statements=(), expr=ast.FloatLit(value=1.5)),
        )
        assert ctx._infer_vera_type(node) == "Float64"

    def test_assertexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssertExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_assumeexpr_returns_unit(self) -> None:
        ctx = _make_ctx()
        node = ast.AssumeExpr(expr=ast.BoolLit(value=True))
        assert ctx._infer_vera_type(node) == "Unit"

    def test_anonfn_returns_none(self) -> None:
        """Closure handle has no simple Vera-type name suitable
        for call rewriting; None lets callers handle the unknown
        case explicitly (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        body = ast.Block(statements=(), expr=ast.UnitLit())
        node = ast.AnonFn(
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            effect=ast.PureEffect(),
            body=body,
        )
        assert ctx._infer_vera_type(node) is None

    def test_qualifiedcall_returns_none(self) -> None:
        """`qualifier` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.QualifiedCall(
            qualifier="IO", name="read_line", args=(ast.UnitLit(),))
        assert ctx._infer_vera_type(node) is None

    def test_modulecall_returns_none(self) -> None:
        """`path` can't be threaded through bare-name FnCall
        dispatch (post-#597-pr-review fix)."""
        ctx = _make_ctx()
        node = ast.ModuleCall(
            path=("some_module",), name="some_fn", args=())
        assert ctx._infer_vera_type(node) is None


# =====================================================================
# Pre-scan walker FIELD coverage (#1210 round 5)
# =====================================================================

_SCRIPT_PATH = (
    Path(__file__).resolve().parent.parent
    / "scripts" / "check_walker_coverage.py"
)

# A field is "descendable" when its declared type can carry an expression the
# walkers must reach.  Matched on the RESOLVED annotation text, so
# `tuple[Expr, ...]`, `Expr | None` and `tuple[TypeExpr, Expr] | None` all
# count while `tuple[str, ...]` and `Span | None` do not.
_DESCENDABLE = ("Expr", "Block", "AnonFn", "Stmt")

# The two pre-scans under audit.  Both are in `vera/codegen/compilability.py`
# and both carry a `# WALKER_COVERAGE:` checklist.
_PRE_SCANS = ("_scan_io_ops", "_scan_expr_for_handlers")

# Classes that carry a descendable field and are deliberately NOT dispatched
# on by the recursion.  One line each, saying where the field IS reached —
# an entry whose reason is "we do not need it" is the shape that produced
# both round-5 holes, so each of these names a concrete other route.
_JUSTIFIED_IGNORES: dict[str, str] = {
    "FnDecl":
        "`decl.body` IS the entry point — `emit_function` hands it to both "
        "pre-scans; the recursion never meets a FnDecl.",
    "Requires":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point (#1210 round 2), not by the recursion.",
    "Ensures":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point (#1210 round 2), not by the recursion.",
    "Decreases":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point; carries `exprs`, which is why that helper exists.",
    "Invariant":
        "contract predicate — enumerated by `contract_exprs()` at the entry "
        "point, same as the other three clause kinds.",
    "RefinementType":
        "signature refinement predicate — enumerated by "
        "`_signature_refinement_predicates()` at the entry point (#1210 "
        "round 5); reached through the alias table, so no structural walk "
        "can find it.",
    "HandlerState":
        "reached through the HandleExpr branch, which walks "
        "`node.state.init_expr`.",
    "HandlerClause":
        "reached through the HandleExpr branch, which walks `clause.body` "
        "and `clause.state_update[1]` for every clause.",
    "MatchArm":
        "reached through the MatchExpr branch, which walks every "
        "`arm.body`.",
    "DataDecl":
        "a data-type `invariant(...)` is verifier-only — no code in "
        "`vera/codegen/` or `vera/wasm/` reads `DataDecl.invariant`, so "
        "nothing written in one is lowered.",
}


def _descendable_fields(cls: type) -> list[str]:
    """Field names of *cls* whose type can carry a walkable expression."""
    if not dataclasses.is_dataclass(cls):
        return []
    hints = typing.get_type_hints(cls, vars(ast))
    out = []
    for f in dataclasses.fields(cls):
        text = str(hints.get(f.name, f.type)).replace("vera.ast.", "")
        if any(re.search(rf"\b{d}\b", text) for d in _DESCENDABLE):
            out.append(f.name)
    return out


def _canonical_classes() -> dict[str, list[str]]:
    """Every `vera.ast` node class carrying at least one descendable field.

    Derived from the dataclass schema, not from a hand-kept list, so a new
    AST class — or a new expression-carrying field on an existing one —
    enters the canonical set the moment it is declared.
    """
    out: dict[str, list[str]] = {}
    for name in sorted(dir(ast)):
        cls = getattr(ast, name)
        if not (inspect.isclass(cls) and issubclass(cls, ast.Node)):
            continue
        fields = _descendable_fields(cls)
        if fields:
            out[name] = fields
    return out


@pytest.fixture(scope="module")
def coverage_script() -> object:
    """`scripts/check_walker_coverage.py` imported as a module.

    Its extractors are reused rather than re-implemented so the two
    instruments cannot disagree about what a walker "names".
    """
    spec = importlib.util.spec_from_file_location(
        "check_walker_coverage_for_prescans", _SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules["check_walker_coverage_for_prescans"] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def pre_scan_walkers(coverage_script: object) -> dict[str, tuple[set, set]]:
    """`{walker name: (isinstance-dispatched, checklist-named)}`."""
    path = Path(inspect.getfile(compilability))
    found = coverage_script.find_walker_functions(path)  # type: ignore[attr-defined]
    by_name = {node.name: (node, src) for node, src in found}
    missing = set(_PRE_SCANS) - set(by_name)
    assert not missing, (
        f"{sorted(missing)} no longer carry a `# WALKER_COVERAGE:` marker in "
        f"{path.name} — either the marker was dropped (restore it: "
        "scripts/check_walker_coverage.py audits by marker) or the walker "
        "was renamed and this gate must follow it"
    )
    return {
        name: (
            coverage_script.extract_isinstance_classes(by_name[name][0]),  # type: ignore[attr-defined]
            coverage_script.extract_checklist_classes(by_name[name][1]),  # type: ignore[attr-defined]
        )
        for name in _PRE_SCANS
    }


class TestPreScanWalkerFieldCoverage:
    """Every expression-carrying AST class is walked, or justified here.

    The corpus-anchored differential in
    `tests/test_state_exn_registration.py` can only see a hole a corpus
    program contains; round 5's two holes had no corpus instance, so they
    survived a green suite for as long as nobody wrote the shape.  This gate
    is schema-driven instead: it reads the dataclass fields of `vera/ast.py`,
    so a new class or a new expression-carrying field is a loud failure at
    the commit that adds it, whether or not anyone writes a program using it.

    Deliberately STRONGER than `scripts/check_walker_coverage.py`: a
    checklist disposition alone does not count as coverage here, only an
    actual `isinstance` branch or an entry in `_JUSTIFIED_IGNORES`.  That is
    the exact distinction `ModuleCall` was hiding behind — named in both
    checklists as "tracked by the imported module's own scan", which was true
    of the callee and false of the arguments the walkers never reached.
    """

    def test_every_expression_carrying_class_is_walked_or_justified(
        self, pre_scan_walkers: dict[str, tuple[set, set]],
    ) -> None:
        canonical = _canonical_classes()
        assert len(canonical) > 20, (
            f"only {len(canonical)} AST classes carry a descendable field — "
            "the schema scan has stopped matching, and this gate would pass "
            "vacuously"
        )
        for walker, (dispatched, _checklist) in pre_scan_walkers.items():
            holes = sorted(
                set(canonical) - dispatched - set(_JUSTIFIED_IGNORES))
            assert not holes, (
                f"`{walker}` never descends into "
                + ", ".join(
                    f"{name}.{'/'.join(canonical[name])}" for name in holes)
                + " — add an `isinstance` branch, or add the class to "
                "`_JUSTIFIED_IGNORES` with the route its expressions ARE "
                "reached by.  A class carrying live sub-expressions that no "
                "pass walks is the #1210 bug: the registration pass misses "
                "it while the lowering emits its calls anyway."
            )

    def test_the_ignore_table_cannot_rot(self) -> None:
        """Every justified entry still exists and still carries a field.

        Without this, a class removed from `vera/ast.py` (or one that loses
        its last expression-carrying field) leaves a stale exemption behind
        that would silently cover a LATER class of the same name.
        """
        canonical = _canonical_classes()
        stale = sorted(set(_JUSTIFIED_IGNORES) - set(canonical))
        assert not stale, (
            f"{stale} are exempted in `_JUSTIFIED_IGNORES` but no longer "
            "carry any expression-carrying field — delete the entries"
        )
        for name, reason in _JUSTIFIED_IGNORES.items():
            assert len(reason) > 30 and reason.rstrip().endswith("."), (
                f"the `{name}` exemption needs a reason naming where its "
                f"expressions ARE reached, got: {reason!r}"
            )

    def test_the_checklist_comments_stay_truthful(
        self, pre_scan_walkers: dict[str, tuple[set, set]],
    ) -> None:
        """Every dispatched class is documented in the walker's checklist.

        `scripts/check_walker_coverage.py` accepts EITHER the branch or the
        comment; this asserts the comment keeps up with the branches, so a
        reader of the checklist sees the walk that actually happens.  It is
        what would have caught `ModuleCall`'s stale "intentionally ignored"
        line the moment its branch landed.
        """
        canonical = _canonical_classes()
        for walker, (dispatched, checklist) in pre_scan_walkers.items():
            undocumented = sorted(
                (dispatched & set(canonical)) - checklist)
            assert not undocumented, (
                f"`{walker}` dispatches on {undocumented} but its "
                "`# WALKER_COVERAGE:` checklist does not mention them — the "
                "comment is the thing reviewers read"
            )

    def test_the_gate_can_go_red(self) -> None:
        """Drop a real branch from the canonical set and the gate must fire.

        Proves the comparison is doing work: `LetDestruct` — one of the two
        classes round 5 added — must be reported as a hole the moment it is
        not among the dispatched classes.  Without this, an extraction that
        silently returned every class name would leave the gate green
        forever.
        """
        canonical = _canonical_classes()
        assert "LetDestruct" in canonical and "ModuleCall" in canonical, (
            "the two round-5 classes must still carry descendable fields"
        )
        pretend_dispatched = set(canonical) - {"LetDestruct", "ModuleCall"}
        holes = sorted(
            set(canonical) - pretend_dispatched - set(_JUSTIFIED_IGNORES))
        assert holes == ["LetDestruct", "ModuleCall"], holes


# =====================================================================
# `contract_exprs` dispatches explicitly (#1210 round 5)
# =====================================================================


class TestContractExprsDispatch:
    """Every contract kind is enumerated, and an unknown one is loud.

    The helper started as `getattr(c, "expr", None)`, which treats an
    unrecognised contract kind as "carries no predicates" — the silent skip it
    was written to fix, since `Decreases` carries `exprs` and was dropped
    exactly that way.  Explicit dispatch turns the next new `ast.Contract`
    subclass into a failure at the commit that adds it, and lets mypy see the
    field accesses.
    """

    @staticmethod
    def _lit(n: int) -> ast.IntLit:
        return ast.IntLit(value=n)

    def test_single_predicate_kinds_are_yielded(self) -> None:
        contracts = (
            ast.Requires(expr=self._lit(1)),
            ast.Ensures(expr=self._lit(2)),
            ast.Invariant(expr=self._lit(3)),
        )
        assert [e.value for e in compilability.contract_exprs(contracts)] == [
            1, 2, 3]

    def test_decreases_yields_every_measure_component(self) -> None:
        """A lexicographic measure is SEVERAL expressions, in `exprs`."""
        contracts = (ast.Decreases(exprs=(self._lit(7), self._lit(8))),)
        assert [e.value for e in compilability.contract_exprs(contracts)] == [
            7, 8]

    def test_an_unknown_contract_kind_raises(self) -> None:
        """A new `ast.Contract` subclass must fail loud, not enumerate empty.

        Constructed synthetically because every kind that exists today is
        handled — which is the point: this pins what happens to the NEXT one.
        """

        class _FutureContract(ast.Contract):
            pass

        with pytest.raises(TypeError, match="_FutureContract"):
            list(compilability.contract_exprs((_FutureContract(),)))
