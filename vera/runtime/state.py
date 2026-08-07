"""State<T> effect host bindings (§9.4).

Extracted from `execute()` in `vera/codegen/api.py` (#421).  Each State<T> type
gets get/set/push/pop host functions over a per-type value stack.  `state_store`
is created by `execute()` and passed in — execute() reads each cell's
top-of-stack into `ExecuteResult.state` — and `register_state` populates it.
"""

from __future__ import annotations

import wasmtime

from vera.monomorphize import mangle_type_name
from vera.wasm.helpers import CellNames


def register_state(
    linker: wasmtime.Linker,
    state_types: list[tuple[CellNames, str]],
    initial_state: dict[str, int | float] | None,
    state_store: dict[str, list[int | float]],
) -> None:
    """Register State<T> get/set/push/pop host functions on `linker`."""
    _WASM_VAL_TYPE = {
        "i64": wasmtime.ValType.i64(),
        "i32": wasmtime.ValType.i32(),
        "f64": wasmtime.ValType.f64(),
    }
    _DEFAULT_STATE: dict[str, int | float] = {
        "i64": 0, "i32": 0, "f64": 0.0,
    }

    # Each key maps to a stack of values: push on handler entry, pop on exit.
    # This allows nested handle[State<T>] of the same type to have independent
    # state cells (#417).

    for cell, wasm_t in state_types:
        # State cell key stays the human-readable full name (the
        # `ExecuteResult.state` dict is keyed `State_<type_name>` and is a
        # public surface — tests read `state["State_Int"]`).  The IMPORT field
        # names, however, must match the mangled WAT identifiers emitted by
        # `assembly.py` for composite T (`Tuple<Int, Int>` →
        # `Tuple_LInt_C_Int_R`; #914/#775), so register those mangled.
        state_key = f"State_{cell.family}"
        import_suffix = mangle_type_name(cell.family)
        state_store[state_key] = [_DEFAULT_STATE[wasm_t]]
        val_type = _WASM_VAL_TYPE[wasm_t]

        # Closure factories to capture correct state_key per type
        def _make_host_get(key: str):  # type: ignore[no-untyped-def]
            def host_get() -> int | float:
                return state_store[key][-1]
            return host_get

        def _make_host_put(key: str):  # type: ignore[no-untyped-def]
            def host_put(val: int | float) -> None:
                state_store[key][-1] = val
            return host_put

        def _make_host_push(key: str, default: int | float):  # type: ignore[no-untyped-def]
            def host_push() -> None:
                state_store[key].append(default)
            return host_push

        def _make_host_pop(key: str):  # type: ignore[no-untyped-def]
            def host_pop() -> None:
                if len(state_store[key]) > 1:
                    state_store[key].pop()
            return host_pop

        get_type = wasmtime.FuncType([], [val_type])
        linker.define_func(
            "vera", f"state_get_{import_suffix}", get_type,
            _make_host_get(state_key),
        )

        put_type = wasmtime.FuncType([val_type], [])
        linker.define_func(
            "vera", f"state_put_{import_suffix}", put_type,
            _make_host_put(state_key),
        )

        push_type = wasmtime.FuncType([], [])
        linker.define_func(
            "vera", f"state_push_{import_suffix}", push_type,
            _make_host_push(state_key, _DEFAULT_STATE[wasm_t]),
        )

        pop_type = wasmtime.FuncType([], [])
        linker.define_func(
            "vera", f"state_pop_{import_suffix}", pop_type,
            _make_host_pop(state_key),
        )

    # Apply initial state overrides (for testing)
    if initial_state:
        for key, val in initial_state.items():
            if key in state_store:
                state_store[key][-1] = val
