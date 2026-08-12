"""#1276: a ``handle[Exn]`` whose clause body AND handled body both diverge must
still emit a block WASM accepts in a result-expecting context.

``result_wt`` is inferred from the clause body, then from the handled body.  When
every path out of both is a ``throw``, neither yields a WAT type and the handler
was emitted as a result-LESS ``block`` — dropped into a context that expects a
value.  ``vera check`` and ``vera verify`` pass; the module is rejected at load:

    Invalid input WebAssembly code at offset 88:
    type mismatch: expected i64 but nothing on stack

The distinction the fix turns on is that ``result_wt is None`` means two
different things: **Unit** (the block really does complete with no value) and
**divergence** (the block never completes at all).  Only the second may be
followed by ``unreachable``; doing it for the first would trap a program that
runs fine.  So the tests below come in pairs — a divergent shape that must now
compile and run, and its Unit twin that must keep running and must NOT acquire
an unreachable.

The observable for a both-diverge handler is the OUTER handler's clause value:
``throw(5)`` is caught by the inner clause, which rethrows at the outer's payload
type, and the outer clause answers 1000.
"""

from __future__ import annotations

import os
import tempfile

import pytest
import wasmtime

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast

# The issue's repro: an Int-payload inner handler whose clause rethrows at the
# outer handler's Bool payload, over a body that throws.  Both diverge.
_INT_RETHROW = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      1000
    }
  } in {
    handle[Exn<Int>] {
      throw(@Int) -> {
        throw(true)
      }
    } in {
      throw(5)
    }
  }
}
"""

# The Byte spelling — the payload width #1269 unmasked.  Same divergence, a
# different tag representation (i32), so the fix cannot be width-specific.
_BYTE_RETHROW = """\
type Small = { @Byte | @Byte.0 < 10 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      1000
    }
  } in {
    handle[Exn<Small>] {
      throw(@Small) -> {
        throw(true)
      }
    } in {
      throw(5)
    }
  }
}
"""

# A three-deep chain: the innermost clause rethrows into the middle, whose
# clause rethrows into the outer.  Two nested both-diverge handlers, so the
# fix has to hold when the enclosing context is itself unreachable-typed.
_THREE_DEEP = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      1000
    }
  } in {
    handle[Exn<Float64>] {
      throw(@Float64) -> {
        throw(true)
      }
    } in {
      handle[Exn<Int>] {
        throw(@Int) -> {
          throw(1.5)
        }
      } in {
        throw(5)
      }
    }
  }
}
"""

# The branch spelling: the clause body diverges through BOTH arms of an `if`,
# so divergence has to be recognized structurally rather than only at a bare
# tail call.
_BRANCHING_CLAUSE = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Bool>] {
    throw(@Bool) -> {
      1000
    }
  } in {
    handle[Exn<Int>] {
      throw(@Int) -> {
        if @Int.0 > 3 then {
          throw(true)
        } else {
          throw(false)
        }
      }
    } in {
      throw(5)
    }
  }
}
"""

# The Unit TWIN: `result_wt` is `None` here too, but because the handler
# completes with no value — not because it never completes.  It must keep
# running, and must NOT be given an `unreachable`.
_UNIT_HANDLER = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> {
      ()
    }
  } in {
    ()
  }
}
"""

_DIVERGENT = [
    ("int_rethrow", _INT_RETHROW),
    ("byte_rethrow", _BYTE_RETHROW),
    ("three_deep", _THREE_DEEP),
    ("branching_clause", _BRANCHING_CLAUSE),
]


def _compile(source: str):
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = parse_to_ast(source)
        diags, arts = typecheck_with_artifacts(
            program, source, file=path, collect_module_artifacts=True,
        )
        errors = [d.description for d in diags if d.severity == "error"]
        assert not errors, f"typecheck errors: {errors}"
        result = codegen_compile(
            program, source=source, file=path,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
            module_artifacts=arts.module_artifacts,
        )
    finally:
        os.unlink(path)
    cg_errors = [
        d.description for d in result.diagnostics if d.severity == "error"
    ]
    assert not cg_errors, f"codegen errors: {cg_errors}"
    return result


def _run(result, fn: str = "main"):
    try:
        return "ok", execute(result, fn_name=fn).value
    except (wasmtime.WasmtimeError, wasmtime.Trap, RuntimeError) as exc:
        return "trap", str(exc)


@pytest.mark.parametrize(
    ("label", "source"),
    [pytest.param(lbl, s, id=lbl) for lbl, s in _DIVERGENT],
)
def test_both_diverge_handler_is_valid_wasm(label: str, source: str) -> None:
    """Valid WASM, and the OUTER handler's clause value at run."""
    result = _compile(source)
    kind, payload = _run(result)
    assert kind == "ok", (
        f"{label}: check-green source produced a module the engine rejects — "
        f"{payload}"
    )
    assert payload == 1000, (
        f"{label}: the observable is the outer handler's clause value 1000, "
        f"got {payload}"
    )


def test_unit_handler_still_completes() -> None:
    """The Unit twin: `result_wt is None` for a handler that DOES complete.
    It must keep running — an unconditional `unreachable` on the None case
    would trap here rather than returning."""
    result = _compile(_UNIT_HANDLER)
    kind, payload = _run(result)
    assert kind == "ok", (
        f"a completing Unit-typed handler must not be given a divergence "
        f"terminator — {payload}"
    )


def test_unit_handler_wat_has_no_unreachable() -> None:
    """The positional half of the twin: no divergence terminator is attached to
    a completing handler, whatever the runtime happens to do."""
    wat = _compile(_UNIT_HANDLER).wat
    assert "unreachable" not in wat, (
        f"a Unit-typed handler must not be terminated as if it diverged:\n{wat}"
    )
