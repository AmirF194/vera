"""Tests for the ``<DB>`` effect (#229) — contract-verified SQL via host imports.

Phase 1 (positional ``Option<String>`` rows):

    DB.query(sql, params)   -> Result<Array<Array<Option<String>>>, String>
    DB.execute(sql, params) -> Result<Int, String>

``params`` and every result cell are ``Option<String>``: ``Some`` is a
bound / returned value, ``None`` is SQL ``NULL``.  DESIGN principle 2
(explicitness, no implicit behaviour) forbids collapsing ``NULL`` to ``""`` —
absence is a distinct value the caller must ``match``.  The effect is
host-backed via the standard-library ``sqlite3`` module (configured by
``VERA_DB_URL``; hermetic tests use ``sqlite::memory:``) and is un-mockable
like ``Http`` / ``Inference`` (``handle[DB]`` is #372's class).  The
literal-provenance checker that makes non-literal SQL a compile-time error
(#309) lands separately.
"""
from __future__ import annotations

from tests.checker_helpers import _check_err, _check_ok


class TestDbEffectChecker229:
    """S1: the type checker recognises the built-in ``<DB>`` effect + its ops."""

    def test_db_query_typechecks_under_db_effect(self) -> None:
        # DB.query is Array<Option<String>> params in, a nullable row grid out.
        _check_ok("""
public fn find(@String -> @Result<Array<Array<Option<String>>>, String>)
  requires(true) ensures(true) effects(<DB>)
{
  DB.query("SELECT name FROM users WHERE id = ?", [Some(@String.0)])
}
""")

    def test_db_execute_typechecks_under_db_effect(self) -> None:
        # DB.execute returns the affected-row count (Int; -1 when sqlite can't
        # report it) or an Err message.
        _check_ok("""
public fn ins(@String -> @Result<Int, String>)
  requires(true) ensures(true) effects(<DB>)
{
  DB.execute("INSERT INTO users(name) VALUES (?)", [Some(@String.0)])
}
""")

    def test_db_op_requires_db_effect(self) -> None:
        # Using DB.query without <DB> in the effect row is an effect error —
        # the effect system tracks database access explicitly (E122).  Before
        # the effect is registered the unknown qualifier is silently permitted,
        # so this both proves registration and pins the effect discipline.
        _check_err("""
public fn find(-> @Result<Array<Array<Option<String>>>, String>)
  requires(true) ensures(true) effects(pure)
{
  DB.query("SELECT name FROM users WHERE id = ?", [Some("1")])
}
""", "DB")

    def test_db_query_rejects_non_string_sql(self) -> None:
        # The SQL argument is typed String — a non-String first argument is a
        # type error (E204) once the op signature is registered.  Discriminates
        # "DB registered with the real signature" from "unknown qualifier
        # silently skipped" (which type-checks nothing).
        _check_err("""
public fn find(-> @Result<Array<Array<Option<String>>>, String>)
  requires(true) ensures(true) effects(<DB>)
{
  DB.query(42, [])
}
""", "expected String")


class TestDbSqlOpIdentity309:
    """The ``db_sql_ops`` stash + ``is_db_sql_op`` are the soundness hinge the
    #309 literal-provenance gate keys on.  It MUST be object-identity, not the
    (value-equal, user-shadowable) op name — otherwise a user
    ``effect DB { op query(...) }`` look-alike would either trip the gate on
    its unrelated op or, worse, leave a real DB call ungated."""

    def test_builtin_ops_match_by_identity(self) -> None:
        from vera.environment import TypeEnv
        env = TypeEnv()
        q = env.effects["DB"].operations["query"]
        e = env.effects["DB"].operations["execute"]
        assert env.is_db_sql_op(q)
        assert env.is_db_sql_op(e)

    def test_value_equal_lookalike_does_not_match(self) -> None:
        # A different OpInfo object with IDENTICAL field values — exactly what a
        # user `effect DB { op query(...) }` override would construct — is
        # value-equal but must NOT be treated as the built-in.  Pins that the
        # check is `is`, not `==`/name: a regression to either flips this RED.
        from vera.environment import OpInfo, TypeEnv
        env = TypeEnv()
        q = env.effects["DB"].operations["query"]
        lookalike = OpInfo("query", q.param_types, q.return_type, "DB")
        assert lookalike == q                       # value-equal ...
        assert not env.is_db_sql_op(lookalike)      # ... yet identity-distinct

    def test_unrelated_query_named_op_does_not_match(self) -> None:
        # An unrelated effect's op that merely shares the name "query".
        from vera.environment import OpInfo, STRING, TypeEnv
        env = TypeEnv()
        other = OpInfo("query", (STRING,), STRING, "Analytics")
        assert not env.is_db_sql_op(other)
