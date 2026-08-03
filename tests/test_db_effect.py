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
(#309) is a separate layer; the gate's op-selection predicate ``is_db_sql_op``
is exercised by ``TestDbSqlOpGating309`` below.
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


class TestDbSqlOpGating309:
    """``is_db_sql_op`` decides which calls the #309 literal-provenance gate
    checks.  It MUST gate exactly the set codegen lowers to the host database —
    any ``DB.query`` / ``DB.execute``, keyed on ``parent_effect == "DB"`` + op
    name (``DB_SQL_OP_NAMES``), the SAME axis ``wasm/calls.py`` routes on.  NOT
    built-in ``OpInfo`` identity: ``DB`` is a reserved host qualifier, so a user
    ``effect DB { op query(...) }`` shadow constructs a *distinct* ``OpInfo``
    that still reaches ``conn.execute``.  An identity key left that shadow
    ungated — a silent SQL-injection bypass (#309 review).  The shadow is now
    also rejected at its declaration (E152, #1149); the op-name keying stays as
    defence in depth, so the predicate is asserted here directly rather than
    through a source program."""

    def test_builtin_sql_ops_are_gated(self) -> None:
        from vera.environment import TypeEnv
        env = TypeEnv()
        q = env.effects["DB"].operations["query"]
        e = env.effects["DB"].operations["execute"]
        assert env.is_db_sql_op(q)
        assert env.is_db_sql_op(e)

    def test_user_effect_db_shadow_is_gated(self) -> None:
        # A DISTINCT OpInfo object with parent_effect "DB" and a SQL op name —
        # exactly what a user `effect DB { op query(...) }` shadow constructs —
        # routes to the host by qualifier name, so it MUST be gated even though
        # it is a different object from the built-in.  The old identity key
        # returned False here, leaving the injection hole; a regression back to
        # identity flips this RED.
        from vera.environment import OpInfo, TypeEnv
        env = TypeEnv()
        q = env.effects["DB"].operations["query"]
        shadow = OpInfo("query", q.param_types, q.return_type, "DB")
        assert shadow is not q                       # distinct object ...
        assert env.is_db_sql_op(shadow)              # ... yet still gated

    def test_unrelated_effect_query_op_not_gated(self) -> None:
        # An op merely NAMED "query" on a different effect has parent_effect
        # "Analytics", so it routes to the user's handler, not the host, and is
        # NOT gated.  Keying on the bare op name would wrongly gate it.
        from vera.environment import OpInfo, STRING, TypeEnv
        env = TypeEnv()
        other = OpInfo("query", (STRING,), STRING, "Analytics")
        assert not env.is_db_sql_op(other)

    def test_non_sql_db_op_name_not_gated(self) -> None:
        # A hypothetical non-SQL op on the DB effect (name not in
        # DB_SQL_OP_NAMES) is not a host SQL executor, so it is not gated.  Pins
        # the name-membership half of the predicate.
        from vera.environment import OpInfo, STRING, TypeEnv
        env = TypeEnv()
        misc = OpInfo("ping", (STRING,), STRING, "DB")
        assert not env.is_db_sql_op(misc)

    def test_gated_set_matches_builtin_db_ops_differential(self) -> None:
        # Checker<->codegen lockstep: the gated op-name set MUST equal the
        # built-in DB effect's declared ops — the exact ops codegen lowers to
        # `$vera.db_*` host imports.  If a DB op is added/removed without
        # updating DB_SQL_OP_NAMES, the gate would desync from what actually
        # reaches the database (the CLAUDE.md cross-component-soundness rule).
        from vera.environment import DB_SQL_OP_NAMES, TypeEnv
        env = TypeEnv()
        assert DB_SQL_OP_NAMES == set(env.effects["DB"].operations)
