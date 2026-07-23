"""Tests for the SQL literal-provenance checker (#309) — SQL injection as a
compile-time error.

The ``<DB>`` effect (#229) executes ``query`` / ``execute`` against the host
database.  #309 is the verification layer: the **first** (SQL) argument of a
built-in ``DB`` SQL op must be *literal-provenance* — a string literal, a
``string_concat`` of literals, or a ``let`` chain of those — never a value
derived from a runtime slot, a function result, or a ``\\(expr)`` interpolation
of a runtime value.  A non-literal SQL string is the injection vector, so it is
a **compile-time** error (E207), deterministic and solver-free.  When the SQL
*and* the params array are both statically sized, a placeholder/param count
mismatch is E208; when the params length is dynamic, the count check defers to
the runtime (sqlite3 raises, surfacing as ``Result.Err``).

The gate keys on ``env.is_db_sql_op`` (OpInfo **identity**, not the op name),
so a user ``effect DB { op query(...) }`` look-alike is never gated.
"""
from __future__ import annotations

import sqlite3

import pytest

from vera.checker.sql import count_placeholders

from tests.checker_helpers import _check_err, _check_ok


def _check_code(source: str, code: str) -> None:
    """Assert the source produces at least one error with ``error_code``."""
    errs = _check_err(source, "")  # collect all errors (empty substring)
    assert any(e.error_code == code for e in errs), (
        f"Expected an error with code {code}, got: "
        f"{[(e.error_code, e.description) for e in errs]}"
    )


# A DB function skeleton: one @String param, <DB> effect, body supplied.
def _db_fn(body: str, param: str = "@String") -> str:
    return f"""
public fn run({param} -> @Result<Array<Array<Option<String>>>, String>)
  requires(true) ensures(true) effects(<DB>)
{{
{body}
}}
"""


class TestSqlProvenanceReject309:
    """E207 — a non-literal SQL argument is a compile-time error."""

    def test_bare_param_slot_sql_rejected(self) -> None:
        # The SQL string is the guest-controlled @String param — the textbook
        # injection vector.  Must be E207, not accepted.
        _check_code(_db_fn('  DB.query(@String.0, [])'), "E207")

    def test_fn_result_sql_rejected(self) -> None:
        # SQL built by a helper function is not literal-provenance.
        src = """
private fn build(-> @String)
  requires(true) ensures(true) effects(pure)
{ "SELECT * FROM users" }

public fn run(-> @Result<Array<Array<Option<String>>>, String>)
  requires(true) ensures(true) effects(<DB>)
{ DB.query(build(), []) }
"""
        _check_code(src, "E207")

    def test_interpolation_with_runtime_value_rejected(self) -> None:
        # Interpolating a runtime slot into the SQL text is exactly the hole
        # the feature closes.
        _check_code(
            _db_fn('  DB.query("SELECT * FROM u WHERE id = \\(@String.0)", [])'),
            "E207",
        )

    def test_concat_with_nonliteral_operand_rejected(self) -> None:
        # string_concat is allowed only when BOTH operands are literal; a
        # runtime operand taints the whole string.
        _check_code(
            _db_fn('  DB.query(string_concat("SELECT * FROM u WHERE id = ", '
                   '@String.0), [])'),
            "E207",
        )

    def test_let_bound_nonliteral_slot_rejected(self) -> None:
        # A let whose value is a runtime slot has no literal provenance, so a
        # later DB.query on that slot is rejected.
        _check_code(
            _db_fn('  let @String = @String.1;\n  DB.query(@String.0, [])'),
            "E207",
        )


class TestSqlProvenanceAccept309:
    """Literal-provenance SQL (the safe, intended form) type-checks."""

    def test_direct_literal_accepted(self) -> None:
        _check_ok(_db_fn('  DB.query("SELECT * FROM users", [])'))

    def test_concat_of_literals_accepted(self) -> None:
        _check_ok(_db_fn(
            '  DB.query(string_concat("SELECT * ", "FROM users"), [])'))

    def test_let_bound_literal_accepted(self) -> None:
        _check_ok(_db_fn(
            '  let @String = "SELECT * FROM users";\n'
            '  DB.query(@String.0, [])'))

    def test_let_chain_with_shadowing_accepted(self) -> None:
        # The De Bruijn-safe case: the second let's value reads @String.0 =
        # the FIRST binding ("SELECT "), so its own literal_str is
        # "SELECT * FROM users"; the DB.query then reads the SECOND (shadowing)
        # binding.  Eager bind-time resolution is what makes this sound.
        _check_ok(_db_fn(
            '  let @String = "SELECT ";\n'
            '  let @String = string_concat(@String.0, "* FROM users");\n'
            '  DB.query(@String.0, [])'))

    def test_execute_spelling_accepted(self) -> None:
        # Both SQL ops (query AND execute) are gated identically.
        src = """
public fn run(-> @Result<Int, String>)
  requires(true) ensures(true) effects(<DB>)
{ DB.execute("CREATE TABLE t (name TEXT)", []) }
"""
        _check_ok(src)

    def test_execute_nonliteral_rejected(self) -> None:
        # ... and execute rejects a non-literal too (hooking only query leaks).
        src = """
public fn run(@String -> @Result<Int, String>)
  requires(true) ensures(true) effects(<DB>)
{ DB.execute(@String.0, []) }
"""
        _check_code(src, "E207")


class TestSqlPlaceholderCount309:
    """E208 — placeholder/param count mismatch when both are statically sized."""

    def test_placeholder_param_mismatch_rejected(self) -> None:
        # 2 placeholders, 1 param → E208 (both statically known).
        _check_code(
            _db_fn('  DB.query("SELECT * FROM u WHERE a = ? AND b = ?", '
                   '[Some("x")])'),
            "E208",
        )

    def test_placeholder_param_match_accepted(self) -> None:
        _check_ok(_db_fn(
            '  DB.query("SELECT * FROM u WHERE a = ?", [Some("x")])'))

    def test_quote_aware_placeholder_count(self) -> None:
        # The '?' inside a SQL string literal is not a placeholder: 1 real
        # placeholder, 1 param → OK.  A naive count would see 2 and wrongly
        # E208.
        _check_ok(_db_fn(
            '  DB.query("SELECT \'?\' AS q FROM u WHERE a = ?", [Some("x")])'))

    def test_dynamic_params_defers_count_to_runtime(self) -> None:
        # A literal SQL (no E207) with a dynamically-sized params slot: the
        # count is not statically decidable, so NO E208 — sqlite3 enforces it
        # at run time.
        _check_ok(_db_fn(
            '  DB.query("SELECT * FROM u WHERE a = ?", @Array<Option<String>>.0)',
            param="@Array<Option<String>>"))


class TestCountPlaceholdersMatchesSqlite309:
    """The checker↔runtime lockstep: ``count_placeholders`` MUST agree with
    what sqlite3 actually binds, or the E208 arity check would disagree with the
    host on some program.  Pinned differentially against sqlite3 itself: binding
    exactly ``count_placeholders(sql)`` params is accepted, one more is
    rejected — which brackets sqlite3's own count to equal ours."""

    CASES = [
        "SELECT 1",                    # 0
        "SELECT ?",                    # 1
        "SELECT ?, ?",                 # 2
        "SELECT ? + ?",                # 2
        "SELECT '?', ?",               # 1 — quoted ? is data
        'SELECT "?", ?',               # 1 — double-quoted ? is data
        "SELECT 'a''b', ?",            # 1 — doubled-quote escape in a string
        "SELECT ? WHERE 1 = ?",        # 2
        "SELECT '? ? ?', ?, ?",        # 2 — three ? inside a literal, two real
    ]

    @pytest.mark.parametrize("sql", CASES)
    def test_count_matches_sqlite(self, sql: str) -> None:
        n = count_placeholders(sql)
        conn = sqlite3.connect(":memory:")
        # Exactly n bindings: accepted (no bindings-count error).
        conn.execute(sql, [None] * n)
        # One too many: sqlite3 rejects — proving it counts exactly n, as we do.
        with pytest.raises(sqlite3.ProgrammingError):
            conn.execute(sql, [None] * (n + 1))


class TestSqlGateScoping309:
    """The gate fires only where it should — not on a mistyped SQL arg, and not
    on a user ``effect DB`` look-alike (identity keying)."""

    def test_non_string_sql_arg_does_not_cascade_e207(self) -> None:
        # A non-String SQL arg is E204 (type mismatch); the provenance gate is
        # skipped so E207 does not pile on.
        src = """
public fn run(-> @Result<Array<Array<Option<String>>>, String>)
  requires(true) ensures(true) effects(<DB>)
{ DB.query(42, []) }
"""
        errs = _check_err(src, "expected String")
        assert not any(e.error_code == "E207" for e in errs), (
            "E207 should not cascade onto a non-String SQL argument (E204)"
        )

    def test_unrelated_effect_query_op_not_gated(self) -> None:
        # A user effect with its own `query` op is a DISTINCT OpInfo, so
        # is_db_sql_op is False (identity, not name): the provenance gate never
        # fires, and a non-literal arg to the user's op is accepted.  Keying on
        # the op name instead would wrongly reject this.
        src = """
effect Analytics {
  op query(String -> String);
}

public fn run(@String -> @String)
  requires(true) ensures(true) effects(<Analytics>)
{ Analytics.query(@String.0) }
"""
        _check_ok(src)
