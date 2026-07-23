"""Check-time SQL literal-provenance resolution (#309).

The ``<DB>`` effect (#229) runs ``query`` / ``execute`` against a host database.
The soundness layer #309 makes SQL injection a **compile-time** error: the SQL
(first) argument of a built-in ``DB`` SQL op must be *literal-provenance* — a
value assembled entirely from string literals, never from a runtime slot, a
function result, or a ``\\(expr)`` interpolation of a runtime value.  A
non-literal SQL string is the injection vector, so the checker rejects it
outright (E207) — deterministic, solver-free, and effective even inside handled
code where Z3-based claims cannot reach.

:func:`resolve_literal_string` is the core: it returns the compile-time value of
a ``String`` expression **iff** that value is provably literal, else ``None``.
The default for any expression shape it does not explicitly assemble is
``None`` — *conservative reject*.  That asymmetry is the soundness guarantee: a
missing or unhandled case can only false-**reject** a valid program (annoying,
never unsafe), never wrong-**accept** a runtime-derived string (an injection).
``WALKER_COVERAGE`` (#597) forces every future ``Expr`` subclass to be given a
disposition here rather than silently defaulting.

The mechanism is *eager*: a ``let`` binding records its resolved literal (if
any) as ``Binding.literal_str`` at the moment it is checked (before ``bind()``),
so a slot referenced later reads a value resolved in *its own* scope — the
De Bruijn-safe way to follow a ``let`` chain without re-walking a shifted
environment.  :func:`resolve_literal_string` therefore only has to read the
stored ``literal_str`` when it reaches a :class:`~vera.ast.SlotRef`.

:func:`count_placeholders` counts positional ``?`` placeholders quote-aware
(a ``?`` inside a SQL string literal is data, not a placeholder), the count the
E208 arity check compares against a statically-sized params array.  Its verdict
MUST agree with what the sqlite3 host binds; that lockstep is pinned by the
differential ``tests/test_sql_provenance_309.py`` against sqlite3 itself.
"""
from __future__ import annotations

from vera import ast

# ``TypeEnv`` is imported lazily inside the function signature via TYPE_CHECKING
# to avoid a runtime import cycle (environment -> checker -> sql -> environment).
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera.environment import TypeEnv


def resolve_literal_string(expr: ast.Expr, env: TypeEnv) -> str | None:
    """Return the compile-time value of ``expr`` iff it is literal-provenance.

    Returns the resolved ``str`` for a string literal, an interpolation whose
    every embedded expression itself resolves, a ``string_concat`` of two
    resolving operands, or a slot whose binding carries a ``literal_str``.
    Returns ``None`` for anything else — the conservative reject that keeps the
    gate sound: ``None`` means "not provably literal", so the caller rejects.

    # WALKER_COVERAGE: (#597 — every Expr subclass has a disposition; a new
    # subclass added to vera/ast.py trips check_walker_coverage.py until it is
    # given one here.  The default disposition is None = "not literal
    # provenance", which is always SOUND: it can only false-reject.)
    #
    #   StringLit          → Handled: the literal value.
    #   InterpolatedString → Handled: join fragments + recursively-resolved
    #                        embedded exprs; any non-resolving embed → None
    #                        (a runtime \\(expr) is the injection vector).
    #   FnCall             → Handled: string_concat(a, b) of two resolving
    #                        operands; every other builtin/user call → None.
    #   SlotRef            → Handled: the binding's eager literal_str (or None).
    #   BinaryExpr         → None: no String-producing binary operator exists.
    #   UnaryExpr          → None: no String-producing unary operator exists.
    #   IndexExpr          → None: an indexed element is a runtime value.
    #   IntLit             → None: not a String.
    #   FloatLit           → None: not a String.
    #   BoolLit            → None: not a String.
    #   UnitLit            → None: not a String.
    #   HoleExpr           → None: cannot occur post-typecheck; reject anyway.
    #   ResultRef          → None: @T.result is a runtime value.
    #   ConstructorCall    → None: a constructor value is not a bare String.
    #   NullaryConstructor → None: likewise (None / a nullary ctor).
    #   QualifiedCall      → None: a module-qualified call is a runtime result.
    #   ModuleCall         → None: a module call is a runtime result.
    #   AnonFn             → None: a closure is not a String.
    #   IfExpr             → None: conservative — even two literal arms reject
    #                        in v1 (safe; extendable later).
    #   MatchExpr          → None: conservative, as IfExpr.
    #   Block              → None: conservative — a block result is not walked.
    #   HandleExpr         → None: a handled expression is a runtime result.
    #   OldExpr            → None: contract-only; cannot occur in op-arg pos.
    #   NewExpr            → None: contract-only.
    #   AssertExpr         → None: yields Unit; not a String source.
    #   AssumeExpr         → None: yields Unit.
    #   ForallExpr         → None: Bool, contract-only.
    #   ExistsExpr         → None: Bool, contract-only.
    #   ArrayLit           → None: an array is not a String.
    """
    if isinstance(expr, ast.StringLit):
        return expr.value

    if isinstance(expr, ast.InterpolatedString):
        out: list[str] = []
        for part in expr.parts:
            if isinstance(part, str):
                out.append(part)
                continue
            sub = resolve_literal_string(part, env)
            if sub is None:
                return None
            out.append(sub)
        return "".join(out)

    if isinstance(expr, ast.FnCall):
        if expr.name == "string_concat" and len(expr.args) == 2:
            left = resolve_literal_string(expr.args[0], env)
            right = resolve_literal_string(expr.args[1], env)
            if left is None or right is None:
                return None
            return left + right
        return None

    if isinstance(expr, ast.SlotRef):
        binding = env.resolve_slot_binding(expr.type_name, expr.index)
        return binding.literal_str if binding is not None else None

    # Every other Expr subclass: not literal-provenance (see WALKER_COVERAGE).
    return None


def count_placeholders(sql: str) -> int:
    """Count positional ``?`` placeholders in ``sql``, quote-aware.

    A ``?`` inside a SQL string literal (``'...'`` or ``"..."``) is data, not a
    placeholder, and is not counted; SQL's doubled-quote escape (``''`` / ``""``
    inside a like-quoted string) is handled, and a ``?`` inside a ``--`` line
    comment or a ``/* ... */`` block comment is skipped as well.  The result is
    what the sqlite3 host binds the positional params against, so it is the
    count the E208 arity check compares to a statically-sized params array.
    """
    count = 0
    quote: str | None = None
    i = 0
    n = len(sql)
    while i < n:
        c = sql[i]
        if quote is not None:
            if c == quote:
                # A doubled quote ('' or "") is an escaped quote, still inside
                # the string literal — skip both characters.
                if i + 1 < n and sql[i + 1] == quote:
                    i += 2
                    continue
                quote = None
            i += 1
            continue
        # Outside a string literal, skip SQL comments whole so their contents
        # (apostrophes, ? marks) affect neither quote tracking nor the count —
        # sqlite3 ignores them too.
        if c == "-" and i + 1 < n and sql[i + 1] == "-":
            nl = sql.find("\n", i + 2)          # line comment: to end of line
            i = n if nl == -1 else nl + 1
            continue
        if c == "/" and i + 1 < n and sql[i + 1] == "*":
            end = sql.find("*/", i + 2)         # block comment: to closing */
            i = n if end == -1 else end + 2
            continue
        if c in ("'", '"'):
            quote = c
        elif c == "?":
            count += 1
        i += 1
    return count
