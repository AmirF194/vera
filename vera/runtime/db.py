"""``<DB>`` effect host bindings (#229) — SQL execution via the standard-library
``sqlite3`` module.

The DB effect exposes two operations, both taking a SQL string and a parameter
array (``Array<Option<String>>``) and returning a ``Result``:

  - ``DB.query(sql, params)   -> Result<Array<Array<Option<String>>>, String>``
    runs a row-returning statement and marshals the grid back, each cell a
    ``str`` (value) or ``None`` (SQL ``NULL``);
  - ``DB.execute(sql, params) -> Result<Int, String>`` runs a non-row statement
    and returns the affected-row count (``sqlite3``'s ``cursor.rowcount`` — ``-1``
    when it cannot report one, e.g. ``CREATE TABLE``).

Parameters are bound through ``?`` placeholders (``sqlite3`` parameterisation), so
a parameter value is never interpreted as SQL — combined with the #309 checker
gate that requires the SQL string itself to be a compile-time literal, injection
is impossible by construction.  Phase 1 is stringly-typed: a parameter binds as
TEXT / NULL and a returned cell is stringified (``None`` for NULL); numeric and
BLOB columns come back as their ``str`` form.

Like ``Http`` / ``Inference`` this is host-backed and not user-handleable
(``handle[DB]`` is #372's class); one connection is opened per program run and
shared across the ops, so ``sqlite::memory:`` persists across calls within a run.
Configured by ``VERA_DB_URL`` (default: a hermetic in-memory database).
"""

from __future__ import annotations

import os
import sqlite3

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _alloc_result_ok_i64,
    _alloc_result_ok_rows,
    _read_wasm_array_of_options_of_string,
    _read_wasm_string,
)


def _open_connection(
    env_vars: dict[str, str] | None,
) -> sqlite3.Connection:
    """Open the sqlite3 connection named by ``VERA_DB_URL``.

    Accepted forms: unset / empty and the ``:memory:`` spellings
    (``sqlite::memory:``, ``:memory:``, ``sqlite://:memory:``) open a hermetic
    in-memory database; ``sqlite:///<path>`` (or a bare filesystem path) opens a
    file database.  The default (no config) is in-memory, so a program using
    ``<DB>`` runs offline with no setup — persistence is opt-in via the file URL.
    """
    env = env_vars if env_vars is not None else os.environ
    url = env.get("VERA_DB_URL", "").strip()
    if url in ("", "sqlite::memory:", ":memory:",
               "sqlite://:memory:", "sqlite:///:memory:"):
        return sqlite3.connect(":memory:")
    for prefix in ("sqlite:///", "sqlite://"):
        if url.startswith(prefix):
            return sqlite3.connect(url[len(prefix):])
    return sqlite3.connect(url)


def _cell(value: object) -> str | None:
    """Marshal one sqlite3 result cell to ``str`` / ``None``.

    SQL ``NULL`` maps to ``None`` (distinct from an empty string — DESIGN
    principle 2).  Text stays text; a ``BLOB`` (``bytes``) is UTF-8 decoded with
    replacement; numeric values are stringified.
    """
    if value is None:
        return None
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return str(value)


def _db_query(
    caller: wasmtime.Caller,
    conn: sqlite3.Connection,
    sql: str,
    params: list[str | None],
) -> int:
    """Run a row-returning statement; marshal ``Result.Ok(rows)`` or
    ``Result.Err(message)`` and return the ADT pointer."""
    try:
        cursor = conn.execute(sql, params)
        rows = [[_cell(v) for v in row] for row in cursor.fetchall()]
        return _alloc_result_ok_rows(caller, rows)
    except sqlite3.Error as exc:
        return _alloc_result_err_string(caller, str(exc))


def _db_execute(
    caller: wasmtime.Caller,
    conn: sqlite3.Connection,
    sql: str,
    params: list[str | None],
) -> int:
    """Run a non-row statement; commit and marshal ``Result.Ok(rowcount)`` or
    ``Result.Err(message)`` and return the ADT pointer."""
    try:
        cursor = conn.execute(sql, params)
        conn.commit()
        return _alloc_result_ok_i64(caller, cursor.rowcount)
    except sqlite3.Error as exc:
        return _alloc_result_err_string(caller, str(exc))


def register_db(
    linker: wasmtime.Linker,
    ops_used: set[str],
    env_vars: dict[str, str] | None,
) -> None:
    """Register the requested DB host functions on ``linker``.

    A single connection is opened per program run (only when a DB op is actually
    used) and captured by the op closures, so state built by one call is visible
    to the next.  Each closure reads its SQL string and parameter array out of
    WASM memory, executes, and returns the marshalled Result pointer.
    """
    if not ({"db_query", "db_execute"} & ops_used):
        return
    conn = _open_connection(env_vars)

    _sig = wasmtime.FuncType(
        [wasmtime.ValType.i32(), wasmtime.ValType.i32(),
         wasmtime.ValType.i32(), wasmtime.ValType.i32()],
        [wasmtime.ValType.i32()],
    )

    if "db_query" in ops_used:
        def host_db_query(
            caller: wasmtime.Caller,
            sql_ptr: int, sql_len: int, params_ptr: int, params_count: int,
        ) -> int:
            sql = _read_wasm_string(caller, sql_ptr, sql_len)
            params = _read_wasm_array_of_options_of_string(
                caller, params_ptr, params_count,
            )
            return _db_query(caller, conn, sql, params)

        linker.define_func(
            "vera", "db_query", _sig, host_db_query, access_caller=True,
        )

    if "db_execute" in ops_used:
        def host_db_execute(
            caller: wasmtime.Caller,
            sql_ptr: int, sql_len: int, params_ptr: int, params_count: int,
        ) -> int:
            sql = _read_wasm_string(caller, sql_ptr, sql_len)
            params = _read_wasm_array_of_options_of_string(
                caller, params_ptr, params_count,
            )
            return _db_execute(caller, conn, sql, params)

        linker.define_func(
            "vera", "db_execute", _sig, host_db_execute, access_caller=True,
        )
