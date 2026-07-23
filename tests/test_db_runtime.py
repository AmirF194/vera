"""Tests for the ``<DB>`` host binding (#229, S3) — ``vera/runtime/db.py``.

The DB effect's host functions execute SQL against the standard-library
``sqlite3`` module and marshal results back through the S2 helpers.  These drive
the impls directly against an in-memory database — create / insert / select
round-trips, ``NULL`` cells, the affected-row count, parameter binding, and the
error path (an ``Err`` value, never a crash).  The end-to-end path through
codegen routing and a real Vera program lands in S4.

``_open_connection`` is also covered: the ``VERA_DB_URL`` config surface and the
hermetic ``sqlite::memory:`` default.
"""
from __future__ import annotations

import sqlite3

import pytest

from vera.runtime.db import _db_execute, _db_query, _open_connection
from vera.runtime.heap import _read_i32, _read_wasm_string

# Reuse the S2 InstanceCaller harness + the row-grid decoder (helpers, not
# tests — the ``test_``-prefix collection rule leaves them alone).
from tests.test_db_marshalling import _decode_result_ok_rows, _gc_caller


def _decode_result_ok_i64(caller, adt_ptr: int) -> int:
    assert _read_i32(caller, adt_ptr) == 0, "expected Ok tag"
    lo = _read_i32(caller, adt_ptr + 8)
    hi = _read_i32(caller, adt_ptr + 12)
    got = (hi << 32) | lo
    return got - 2 ** 64 if got >= 2 ** 63 else got


def _decode_result_err(caller, adt_ptr: int) -> str:
    assert _read_i32(caller, adt_ptr) == 1, "expected Err tag"
    s_ptr = _read_i32(caller, adt_ptr + 4)
    s_len = _read_i32(caller, adt_ptr + 8)
    return _read_wasm_string(caller, s_ptr, s_len)


class TestDbRuntime229:
    def test_create_insert_select_roundtrip(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        _db_execute(caller, conn, "CREATE TABLE t (id INTEGER, name TEXT)", [])
        _db_execute(caller, conn, "INSERT INTO t VALUES (?, ?)", ["1", "alice"])
        _db_execute(caller, conn, "INSERT INTO t VALUES (?, ?)", ["2", None])
        result = _db_query(caller, conn, "SELECT id, name FROM t ORDER BY id", [])
        # id is an INTEGER column: "1" is stored/returned as 1 and stringified;
        # the NULL name comes back as None (not "").
        assert _decode_result_ok_rows(caller, result) == [
            ["1", "alice"], ["2", None],
        ]

    def test_parameterised_where_binds_safely(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        _db_execute(caller, conn, "CREATE TABLE u (name TEXT)", [])
        for n in ("alice", "bob", "eve"):
            _db_execute(caller, conn, "INSERT INTO u VALUES (?)", [n])
        # A param that looks like an injection is bound as a literal value, so
        # it matches nothing rather than altering the query.
        result = _db_query(
            caller, conn, "SELECT name FROM u WHERE name = ?", ["bob'; DROP TABLE u--"],
        )
        assert _decode_result_ok_rows(caller, result) == []
        # ... and the table is intact.
        still = _db_query(caller, conn, "SELECT name FROM u ORDER BY name", [])
        assert _decode_result_ok_rows(caller, still) == [["alice"], ["bob"], ["eve"]]

    def test_execute_returns_rowcount(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        _db_execute(caller, conn, "CREATE TABLE t (n INTEGER)", [])
        for i in range(3):
            _db_execute(caller, conn, "INSERT INTO t VALUES (?)", [str(i)])
        deleted = _db_execute(caller, conn, "DELETE FROM t WHERE n >= ?", ["1"])
        assert _decode_result_ok_i64(caller, deleted) == 2  # rows 1 and 2

    def test_query_error_is_err_not_crash(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        result = _db_query(caller, conn, "SELECT * FROM nonexistent", [])
        msg = _decode_result_err(caller, result)
        assert "nonexistent" in msg.lower() or "no such table" in msg.lower()

    def test_execute_error_is_err_not_crash(self) -> None:
        caller = _gc_caller()
        conn = sqlite3.connect(":memory:")
        result = _db_execute(caller, conn, "NOT VALID SQL", [])
        assert _read_i32(caller, result) == 1  # Err tag

    def test_open_connection_defaults_to_memory(self) -> None:
        # No VERA_DB_URL → a hermetic in-memory database (no config needed).
        conn = _open_connection({})
        assert isinstance(conn, sqlite3.Connection)
        conn.execute("CREATE TABLE t (x)")  # usable

    @pytest.mark.parametrize("url", ["sqlite::memory:", ":memory:", "sqlite://:memory:"])
    def test_open_connection_memory_urls(self, url: str) -> None:
        conn = _open_connection({"VERA_DB_URL": url})
        assert isinstance(conn, sqlite3.Connection)

    def test_open_connection_file_url(self, tmp_path) -> None:
        db_path = tmp_path / "t.db"
        conn = _open_connection({"VERA_DB_URL": f"sqlite:///{db_path.as_posix()}"})
        conn.execute("CREATE TABLE t (x)")
        conn.commit()
        assert db_path.exists()

    def test_register_db_noop_when_unused(self) -> None:
        # No DB op in the program → nothing bound, no connection opened.
        import wasmtime

        from vera.runtime.db import register_db
        linker = wasmtime.Linker(wasmtime.Engine())
        register_db(linker, set(), {})  # must not raise

    def test_register_db_binds_requested_ops(self) -> None:
        # Binding succeeds (opens the connection, defines the host funcs); the
        # end-to-end link against a compiled module lands in S4.
        import wasmtime

        from vera.runtime.db import register_db
        linker = wasmtime.Linker(wasmtime.Engine())
        register_db(
            linker, {"db_query", "db_execute"},
            {"VERA_DB_URL": "sqlite::memory:"},
        )
