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

The gate keys on ``env.is_db_sql_op`` (``parent_effect == "DB"`` **and** the op
name — the same axis codegen routes to the host database on), so it gates the
built-in ``DB`` ops AND a user ``effect DB { op query(...) }`` shadow (which
still routes to the host), but never an unrelated effect's own ``query`` op.
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
        # A let whose value is a runtime slot (the @String parameter) has no
        # literal provenance, so a later DB.query on that let is rejected.
        _check_code(
            _db_fn('  let @String = @String.0;\n  DB.query(@String.0, [])'),
            "E207",
        )

    def test_conditional_sql_rejected(self) -> None:
        # An `if` expression is conservatively rejected even when both arms are
        # string literals — resolve_literal_string does not walk conditionals in
        # v1.  This pins the soundness asymmetry: an unhandled shape can only
        # false-REJECT a valid program, never wrong-ACCEPT one.  (A bare `if`
        # does not parse as a call argument, so the let-bound form carries the
        # IfExpr into the gate.)
        _check_code(
            _db_fn('  let @String = if true then { "SELECT 1" } '
                   'else { "SELECT 2" };\n  DB.query(@String.0, [])'),
            "E207",
        )


class TestSqlProvenanceAccept309:
    """Literal-provenance SQL (the safe, intended form) type-checks."""

    def test_direct_literal_accepted(self) -> None:
        _check_ok(_db_fn('  DB.query("SELECT * FROM users", [])'))

    def test_empty_string_literal_accepted(self) -> None:
        # The empty string is a genuine literal (0 placeholders), so it is
        # accepted.  This is the distinguishing input for the gate's central
        # ``literal_str is None`` invariant: a regression to a truthiness test
        # (``if not sql`` / ``if binding.literal_str``) would misroute "" to
        # E207 and still pass every other test — so pin it explicitly.
        _check_ok(_db_fn('  DB.query("", [])'))

    def test_let_bound_empty_string_accepted(self) -> None:
        # The empty literal round-trips through ``Binding.literal_str`` (which is
        # "" here, NOT None): the slot resolves to "" and is accepted.
        _check_ok(_db_fn(
            '  let @String = "";\n  DB.query(@String.0, [])'))

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

    def test_let_bound_array_literal_mismatch_rejected(self) -> None:
        # #1160 — the params array is written literally but bound through a
        # ``let``.  It is exactly as statically sized as the inline form, so it
        # gets the same E208.  E207 already follows ``let`` chains; before
        # #1160 E208 looked only at the call-site syntax and let this through.
        _check_code(
            _db_fn(
                '  let @Array<Option<String>> = [Some("x")];\n'
                '  DB.query("SELECT * FROM u WHERE a = ? AND b = ?", '
                '@Array<Option<String>>.0)'
            ),
            "E208",
        )

    def test_let_bound_array_literal_match_accepted(self) -> None:
        # The positive control for the case above: resolving the length through
        # the ``let`` must accept a program whose counts agree, not merely
        # reject more.  Without this, a resolver that returned a wrong length
        # would still look "fixed".
        _check_ok(_db_fn(
            '  let @Array<Option<String>> = [Some("x")];\n'
            '  DB.query("SELECT * FROM u WHERE a = ?", '
            '@Array<Option<String>>.0)'))

    def test_let_chain_of_array_literals_resolves(self) -> None:
        # A chain: the second ``let`` re-binds the first slot.  The length must
        # follow to the innermost binding, the array-side analogue of the
        # literal-string let chain.
        _check_code(
            _db_fn(
                '  let @Array<Option<String>> = [Some("x"), Some("y")];\n'
                '  let @Array<Option<String>> = [Some("z")];\n'
                '  DB.query("SELECT * FROM u WHERE a = ? AND b = ?", '
                '@Array<Option<String>>.0)'
            ),
            "E208",
        )

    def test_let_bound_runtime_array_still_defers(self) -> None:
        # A ``let`` whose value is NOT an array literal has no statically known
        # length, so the count still defers to the driver.  This is the
        # conservative direction: resolution failure must never invent a length.
        _check_ok(_db_fn(
            '  let @Array<Option<String>> = @Array<Option<String>>.0;\n'
            '  DB.query("SELECT * FROM u WHERE a = ? AND b = ?", '
            '@Array<Option<String>>.0)',
            param="@Array<Option<String>>"))

    def test_dynamic_params_defers_count_to_runtime(self) -> None:
        # A literal SQL (no E207) with a dynamically-sized params slot: the
        # count is not statically decidable, so NO E208 — sqlite3 enforces it
        # at run time.
        _check_ok(_db_fn(
            '  DB.query("SELECT * FROM u WHERE a = ?", @Array<Option<String>>.0)',
            param="@Array<Option<String>>"))

    def test_named_params_rejected_e209(self) -> None:
        # Named placeholders (:name / @name / $name) bind against a mapping, not
        # Vera's positional Array<Option<String>>, so they always fail at run
        # time.  Vera supports only anonymous `?` (one canonical form), so the
        # gate rejects them at compile time: E209.
        _check_code(_db_fn(
            '  DB.query("SELECT * FROM u WHERE a = :a AND b = :b", '
            '[Some("x")])'), "E209")

    def test_numbered_params_rejected_e209(self) -> None:
        # Numbered placeholders (?NNN) — Cortex flagged `SELECT ?2` with one
        # param as a statically-knowable mismatch the None-deferral hid.  Vera
        # supports only anonymous `?`, so reject at compile time (E209) rather
        # than defer to a runtime binding-count error.
        _check_code(_db_fn('  DB.query("SELECT ?2", [Some("x")])'), "E209")

    def test_dollar_in_identifier_not_named_param(self) -> None:
        # #1147 adversarial workflow (over-rejection): `a$b` is a valid SQLite
        # identifier — `$` is a legit mid-token identifier char — NOT a $name
        # placeholder.  sqlite3 binds `SELECT a$b` with zero params, so literal
        # SQL using such an identifier must NOT be rejected E209 (or E208).
        _check_ok(_db_fn('  DB.query("SELECT a$b FROM t", [])'))


class TestCountPlaceholdersMatchesSqlite309:
    """The checker↔runtime lockstep: for anonymous ``?`` placeholders,
    ``count_placeholders`` MUST agree with what sqlite3 actually binds, or the
    E208 arity check would disagree with the host on some program.  Pinned
    differentially against sqlite3 itself: binding exactly
    ``count_placeholders(sql)`` params is accepted, one more is rejected — which
    brackets sqlite3's own count to equal ours.  (Named/numbered placeholders
    are out of this differential's scope: ``count_placeholders`` returns ``None``
    for them and the gate defers — see ``test_named_and_numbered_params_defer``.)
    """

    CASES = [
        "",                            # 0 — empty statement binds nothing
        "SELECT 1",                    # 0
        "SELECT ?",                    # 1
        "SELECT ?, ?",                 # 2
        "SELECT ? + ?",                # 2
        "SELECT '?', ?",               # 1 — quoted ? is data
        'SELECT "?", ?',               # 1 — double-quoted ? is data
        "SELECT 'a''b', ?",            # 1 — doubled-quote escape in a string
        "SELECT 1 AS `a?b`, ?",        # 1 — ? inside a backtick identifier
        "SELECT 1 AS [a?b], ?",        # 1 — ? inside a bracket identifier
        "SELECT 1 AS a$b, ?",          # 1 — $ mid-identifier is NOT a $name param
        "SELECT ? WHERE 1 = ?",        # 2
        "SELECT '? ? ?', ?, ?",        # 2 — three ? inside a literal, two real
        "SELECT ?, ? -- ? ' trailing", # 2 — line comment ? / ' ignored
        "SELECT ? /* ' ? */, ?",       # 2 — block comment ' / ? ignored
        "SELECT ?\n-- ?\n, ?",         # 2 — line comment on its own line
    ]

    @pytest.mark.parametrize("sql", CASES)
    def test_count_matches_sqlite(self, sql: str) -> None:
        n = count_placeholders(sql)
        assert n is not None, "CASES are all anonymous-? SQL (int count)"
        conn = sqlite3.connect(":memory:")
        # Exactly n bindings: accepted (no bindings-count error).
        conn.execute(sql, [None] * n)
        # One too many: sqlite3 rejects — proving it counts exactly n, as we do.
        with pytest.raises(sqlite3.ProgrammingError):
            conn.execute(sql, [None] * (n + 1))

    # Named (:name / @name / $name) and numbered (?NNN) placeholders: the
    # positional count is not the bound-parameter count, so count_placeholders
    # returns None and the gate defers the arity check to the sqlite3 host.
    DEFER_CASES = [
        "SELECT ?1, ?1",               # numbered, one bound param
        "SELECT ?5",                   # numbered
        "SELECT :a AND :b",            # named, two bound params, zero ?
        "SELECT @x, ?",                # named @ mixed with anonymous ?
        "SELECT $y",                   # named $
    ]

    @pytest.mark.parametrize("sql", DEFER_CASES)
    def test_named_and_numbered_params_defer(self, sql: str) -> None:
        # Returning None is what makes the gate defer E208 rather than
        # false-reject: a naive `?`-count would disagree with sqlite here.
        assert count_placeholders(sql) is None

    # #1147 adversarial workflow: sqlite3's IdChar rule accepts ANY byte >= 0x80
    # (non-ASCII) and `$` as a bind-parameter name character, but the checker's
    # named-param detection used Python `str.isalnum()`, which is False for
    # high-byte SYMBOL chars (£ U+00A3, € U+20AC) and for `$` — so
    # `count_placeholders` returned an int instead of None, the gate emitted no
    # E209 (or a wrong E208), and a query sqlite binds by name passed `check`
    # then failed at run time.  Each of these IS a named parameter to sqlite3.
    HIGH_BYTE_NAMED = [
        "SELECT :€x",       # named, first name-char is € (U+20AC, non-ASCII)
        "SELECT :£x",       # named, first name-char is £ (U+00A3, a symbol)
        "SELECT ?, :€x",    # anonymous ? MIXED with a high-byte named param
        "SELECT $$x",            # $-prefixed param whose first name-char is '$'
        "SELECT @¥v",       # @-named, first name-char is ¥ (U+00A5)
    ]

    @pytest.mark.parametrize("sql", HIGH_BYTE_NAMED)
    def test_high_byte_named_params_defer_matching_sqlite(self, sql: str) -> None:
        # Pin sqlite3 itself: it prepares each as having >= 1 NAMED parameter,
        # so an empty positional bind is a ProgrammingError (missing binding).
        conn = sqlite3.connect(":memory:")
        with pytest.raises(sqlite3.ProgrammingError):
            conn.execute(sql, [])
        # The checker MUST agree: defer (None) so the gate emits E209, never a
        # positional int that would disagree with the host's real param count.
        assert count_placeholders(sql) is None


class TestSqlGateScoping309:
    """The gate fires only where it should — not on a mistyped SQL arg, and not
    on an unrelated effect's own ``query`` op (a different ``parent_effect``,
    routed to the user's handler rather than the host database)."""

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
        # A user effect NOT named `DB` (here `Analytics`) has `parent_effect ==
        # "Analytics"`, so it is NOT a DB SQL op and the provenance gate never
        # fires: a non-literal arg to the user's own op is accepted.  This is
        # sound because codegen routes such an op to the user's handler, not to
        # the host database — only qualifier `DB` reaches `$vera.db_*`.
        src = """
effect Analytics {
  op query(String -> String);
}

public fn run(@String -> @String)
  requires(true) ensures(true) effects(<Analytics>)
{ Analytics.query(@String.0) }
"""
        _check_ok(src)


class TestDbEffectShadowGated309:
    """The gate MUST fire on a user-declared ``effect DB`` shadow, not only the
    ambient built-in — because codegen routes *any* ``DB.query`` / ``DB.execute``
    to the host database by qualifier **name** (``wasm/calls.py``), regardless of
    whether the ``DB`` effect is the built-in or a user redefinition.

    The original #309 gate keyed on built-in ``OpInfo`` **identity**, which gated
    a strict *subset* of what codegen sends to the database: a user
    ``effect DB { op query(...) }`` type-checked clean, compiled to
    ``call $vera.db_query``, and executed an attacker-controlled string — a
    silent SQL-injection bypass of the flagship guarantee.  Declaring a host
    effect is the *idiomatic* way to use it (every example declares ``effect IO
    { ... }``), so this shadow is the common path, not an exotic one.

    The fix keys the gate on the same axis codegen routes on — ``parent_effect
    == "DB"`` and the op name is a host-routed SQL op — so the checker gates
    *exactly* the set codegen emits (the CLAUDE.md cross-component invariant;
    DESIGN.md principle 2, no implicit behaviour)."""

    _SHADOW = (
        "effect DB {\n"
        "  op query(String, Array<Option<String>> -> "
        "Result<Array<Array<Option<String>>>, String>);\n"
        "  op execute(String, Array<Option<String>> -> Result<Int, String>);\n"
        "}\n"
    )

    def test_user_effect_db_shadow_query_still_gated(self) -> None:
        # The exact injection vector: a user redeclares `effect DB` and passes
        # the runtime @String param straight to DB.query.  Must be E207 — this
        # call compiles to `call $vera.db_query` and reaches conn.execute.
        _check_code(
            self._SHADOW
            + "public fn run(@String -> "
            "@Result<Array<Array<Option<String>>>, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ DB.query(@String.0, []) }\n",
            "E207",
        )

    def test_user_effect_db_shadow_execute_still_gated(self) -> None:
        # The write path (execute) routes to the host identically, so a runtime
        # SQL string is arbitrary DDL/DML — must also be E207.
        _check_code(
            self._SHADOW
            + "public fn run(@String -> @Result<Int, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ DB.execute(@String.0, []) }\n",
            "E207",
        )

    def test_user_effect_db_shadow_literal_still_accepted(self) -> None:
        # The gate rejects runtime-derived SQL, not the `effect DB` declaration
        # itself: a literal query through the shadow is still accepted.
        _check_ok(
            self._SHADOW
            + "public fn run(-> "
            "@Result<Array<Array<Option<String>>>, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            '{ DB.query("SELECT * FROM users", []) }\n'
        )

    def test_unresolved_db_query_spelling_still_gated(self) -> None:
        # Cortex Finding 1: a user `effect DB` that does NOT declare `query`.
        # Op resolution FAILS (E220 warning), so the resolved-op gate never runs
        # — but codegen routes the `DB.query` SPELLING to `$vera.db_query`
        # regardless, so a runtime SQL string still reaches the host.  The gate
        # must fire on the spelling: E207.
        _check_code(
            "effect DB {\n  op ping(Unit -> Unit);\n}\n"
            "public fn run(@String -> "
            "@Result<Array<Array<Option<String>>>, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ DB.query(@String.0, []) }\n",
            "E207",
        )

    def test_unresolved_db_execute_spelling_still_gated(self) -> None:
        # Same for the write path (execute) — arbitrary DDL/DML otherwise.
        _check_code(
            "effect DB {\n  op ping(Unit -> Unit);\n}\n"
            "public fn run(@String -> @Result<Int, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ DB.execute(@String.0, []) }\n",
            "E207",
        )

    def test_generic_effect_db_unbound_arity_still_gated(self) -> None:
        # #1147 adversarial workflow: a GENERIC ``effect DB<T>`` referenced at
        # UNBOUND arity ``effects(<DB>)`` leaves the op's first param a raw
        # TypeVar.  Codegen routes DB.query to the host by qualifier name
        # regardless, so the gate must too: it runs whenever the call is an
        # ``is_db_sql_op`` (parent_effect == "DB" + op name), independent of the
        # arg's static type — so a runtime @String param is E207.
        _check_code(
            "effect DB<T> {\n  op query(T, Array<Option<String>> -> "
            "Result<Array<Array<Option<String>>>, String>);\n}\n"
            "public fn run(@String -> "
            "@Result<Array<Array<Option<String>>>, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ DB.query(@String.0, []) }\n",
            "E207",
        )

    def test_typevar_laundered_sql_arg_still_gated(self) -> None:
        # #1147 adversarial workflow (SEVERE): the runtime SQL string is
        # laundered through a generic function parameter so its STATIC type at
        # the DB.query call site is a raw TypeVar (@T), not String.  The old
        # ``is_subtype(arg, String)`` guard was False for a TypeVar arg, so the
        # gate skipped — yet monomorphization binds T = String and codegen routes
        # to ``$vera.db_query``, executing attacker SQL (` OR '1'='1` tautologies
        # ran; runtime `DROP TABLE` executed).  The `@T.0` slot argument is not
        # literal-provenance, so the gate — now keyed on the codegen routing axis
        # alone — must reject it (E207).
        _check_code(
            "effect DB<T> {\n"
            "  op query(T, Array<Option<String>> -> "
            "Result<Array<Array<Option<String>>>, String>);\n"
            "  op execute(String, Array<Option<String>> -> "
            "Result<Int, String>);\n"
            "}\n"
            "private forall<T> fn runq(@T -> "
            "@Result<Array<Array<Option<String>>>, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ DB.query(@T.0, []) }\n"
            "public fn attack(@String -> "
            "@Result<Array<Array<Option<String>>>, String>)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{ runq(@String.0) }\n",
            "E207",
        )

    def test_user_effect_db_shadow_nonstring_int_param_rejected(self) -> None:
        # #1147 adversarial workflow: a user `effect DB` shadow declares the SQL
        # op's first param as `Int` (not String).  `DB.query(42, ...)` then
        # type-checks against the user's Int param (no E204) — but codegen still
        # routes it to the host by qualifier name, marshalling the i64 where the
        # host expects an (i32 ptr, i32 len), yielding INVALID WASM from a
        # check-clean program.  The gate must run regardless of the declared
        # param type (a non-String param does not fire the E204 that would make
        # E207 a cascade), so the non-literal `42` is rejected (E207).
        _check_code(
            "effect DB {\n"
            "  op query(Int, Array<Option<String>> -> "
            "Result<Array<Array<Option<String>>>, String>);\n"
            "}\n"
            "public fn main(-> @Int)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{\n"
            "  let @Array<Option<String>> = [];\n"
            "  match DB.query(42, @Array<Option<String>>.0) {\n"
            "    Err(@String) -> 1,\n"
            "    Ok(@Array<Array<Option<String>>>) -> 0\n"
            "  }\n"
            "}\n",
            "E207",
        )

    def test_user_effect_db_shadow_nonstring_array_param_rejected(self) -> None:
        # Sibling of the Int case: a user `effect DB` shadow whose SQL op takes
        # an `Array<Option<String>>` first param.  A runtime array slot passes
        # check against the user's declared param but reaches the SQL host
        # ungated (its bytes marshalled as the SQL (ptr,len)).  The slot is not
        # literal-provenance, so the gate must reject it (E207).
        _check_code(
            "effect DB {\n"
            "  op query(Array<Option<String>>, Array<Option<String>> -> "
            "Result<Array<Array<Option<String>>>, String>);\n"
            "}\n"
            "public fn main(-> @Int)\n"
            "  requires(true) ensures(true) effects(<DB>)\n"
            "{\n"
            "  let @Array<Option<String>> = [Some(\"SELECT 1\")];\n"
            "  let @Array<Option<String>> = [];\n"
            "  match DB.query(@Array<Option<String>>.1, "
            "@Array<Option<String>>.0) {\n"
            "    Err(@String) -> 1,\n"
            "    Ok(@Array<Array<Option<String>>>) -> 0\n"
            "  }\n"
            "}\n",
            "E207",
        )
