"""#1212: a `@Byte` literal inside a value-position join lowers at i32.

`@Byte` is i32 (spec §11) while an int literal defaults to `i64.const`, so
every write into a Byte boundary needs the literal coerced.  #865 and #1092
coerced a literal that WAS the written value — a top-level `IntLit` and
nothing else.  The checker's bidirectional coercion is happy to type a
BRANCH literal as `@Byte` too, so each of

    let @Byte = if c then { 1 } else { 2 }
    handle[State<Byte>](@Byte = if c then { 1 } else { 2 }) …
    put(if c then { 1 } else { 2 })
    resume(if c then { 1 } else { 2 })     -- the E602 skip message's advice
    … with @Byte = if c then { 1 } else { 2 }
    byte_id(if c then { 1 } else { 2 })
    MkB(if c then { 200 } else { 3 })      -- at Box<Byte>
    let @Byte = match … { Some(@Byte) -> @Byte.0, None -> 0 }

was a check-green program that failed WASM validation with `type mismatch:
expected i32, found i64`.  Loud at run, never silent corruption, but eight
arms of one defect.

The fix is ONE branch descent — `WasmContext._mark_byte_literal_leaves`,
driven through `_mark_byte_write_value` — marking the literal LEAVES of a
join before the value is translated, so the `IntLit` lowering and the two
join result-type deciders (`_infer_block_result_type`,
`_infer_match_result_type` via `_infer_expr_wasm_type`) all read the same
marks and the `(result i32)` annotation agrees with its arms.  Marking
before translation, rather than overwriting an already-translated i64
lowering, is also what keeps each written value translated exactly once.

Every test carries a VALUE oracle, not merely "it runs": an i32/i64 width
defect that happened to validate would still read back the wrong number.
The controls are the load-bearing half — a plain `@Int` join must stay i64
(asserted on a value above 2^32, which an i32 lowering cannot represent),
and a Byte join with no literal arm must keep working untouched.
"""

from __future__ import annotations

import pytest

from tests.checker_helpers import _check_ok
from tests.codegen_helpers import _run

# =====================================================================
# The eight write boundaries
# =====================================================================

_LET_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = if @Bool.0 then { 200 } else { 3 };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The Block-tail leg of the descent: the branch is not the literal, it
# CONTAINS the literal as its trailing expression.
_LET_IF_BLOCK_TAIL = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = if @Bool.0 then {
    let @Int = 1;
    200
  } else {
    3
  };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The multi-arm MATCH leg: `@Byte.0` in the first arm is already i32, and
# the literal in the second is what used to be i64 — a mixed join, which is
# why the arms and the `(result …)` annotation have to be decided together.
# This is the shape of the `p4a_int_in_byte` review probe.
_LET_MATCH_ARM = """
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = match int_to_byte(@Int.0) {
    Some(@Byte) -> @Byte.0,
    None -> 0
  };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(200)
}
"""

_STATE_INIT_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = if @Bool.0 then { 200 } else { 3 }) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_PUT_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) }
  } in {
    put(if @Bool.0 then { 200 } else { 3 });
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# The bare-dispatch twin of `_PUT_IF`: no `put` clause, so the write goes
# through the host intrinsic rather than an inlined clause body.
_BARE_PUT_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(@Byte.0) }
  } in {
    put(if @Bool.0 then { 200 } else { 3 });
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_RESUME_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(if @Bool.0 then { 200 } else { 3 }) },
    put(@Byte) -> { resume(()) }
  } in {
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_WITH_IF = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Byte>](@Byte = 7) {
    get(@Unit) -> { resume(@Byte.0) },
    put(@Byte) -> { resume(()) } with @Byte = if @Bool.0 then { 200 } else { 3 }
  } in {
    put(1);
    byte_to_int(get(()))
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

_CALL_ARG_IF = """
public fn byte_id(@Byte -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Byte.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(byte_id(if true then { 200 } else { 3 }))
}
"""


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        pytest.param(_LET_IF, 200, id="let_if"),
        pytest.param(_LET_IF_BLOCK_TAIL, 200, id="let_if_block_tail"),
        pytest.param(_LET_MATCH_ARM, 200, id="let_match_arm"),
        pytest.param(_STATE_INIT_IF, 200, id="state_init_if"),
        pytest.param(_PUT_IF, 200, id="put_if"),
        pytest.param(_BARE_PUT_IF, 200, id="bare_put_if"),
        pytest.param(_RESUME_IF, 200, id="resume_if"),
        pytest.param(_WITH_IF, 200, id="with_update_if"),
        pytest.param(_CALL_ARG_IF, 200, id="call_arg_if"),
    ],
)
def test_a_byte_literal_in_a_join_reaches_the_boundary(
    source: str, expected: int,
) -> None:
    """Each #865 arm, spelled with the literal inside a branch.

    200 rather than a small number on purpose: it is representable in a
    Byte and distinguishable from every other constant in the fixture, so a
    wrong branch or a truncated store shows up as a wrong VALUE and not just
    as a validation failure.
    """
    _check_ok(source)
    assert _run(source) == expected


def test_the_other_branch_is_reachable_and_also_a_byte() -> None:
    """The join is a real join: the else arm's literal is coerced too.

    A fix that marked only the `then` branch would validate (the `if`'s
    result type is read off `then`) and then push an i64 from `else`.
    """
    assert _run(_LET_IF.replace("f(true)", "f(false)")) == 3
    assert _run(_PUT_IF.replace("f(true)", "f(false)")) == 3
    assert _run(_RESUME_IF.replace("f(true)", "f(false)")) == 3


# =====================================================================
# Controls — the marking must not spread
# =====================================================================

# Above 2^32, so an i32 lowering cannot represent it: if a plain `@Int`
# join were ever marked at the Byte width, this returns a truncated number
# rather than merely failing to validate.
_INT_JOIN_STAYS_I64 = """
public fn f(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = if @Bool.0 then { 5000000000 } else { 3 };
  @Int.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true)
}
"""

# A Byte join with NO literal arm was already correct — both arms are i32
# Byte values — and must stay so: the marking claims nothing about it.
_BYTE_JOIN_WITHOUT_LITERALS = """
public fn f(@Bool, @Byte, @Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Byte = if @Bool.0 then { @Byte.1 } else { @Byte.0 };
  byte_to_int(@Byte.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(true, 200, 3)
}
"""

# A Byte-RETURNING function whose body is a literal join: the return path
# has its own #865 coercion (`_infer_block_result_type` + `i32.wrap_i64`),
# which must keep working whichever width the body settles on.
_BYTE_RETURN_JOIN = """
public fn pick(@Bool -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Bool.0 then { 200 } else { 3 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  byte_to_int(pick(true))
}
"""


def test_an_int_join_still_lowers_at_i64() -> None:
    """The value cannot survive an i32 store, so this is not a mere
    validation check."""
    assert _run(_INT_JOIN_STAYS_I64) == 5000000000


def test_a_byte_join_with_no_literal_arm_is_untouched() -> None:
    assert _run(_BYTE_JOIN_WITHOUT_LITERALS) == 200
    assert _run(
        _BYTE_JOIN_WITHOUT_LITERALS.replace(
            "f(true, 200, 3)", "f(false, 200, 3)")) == 3


def test_a_byte_returning_literal_join_still_runs() -> None:
    assert _run(_BYTE_RETURN_JOIN) == 200
    assert _run(_BYTE_RETURN_JOIN.replace("pick(true)", "pick(false)")) == 3


# =====================================================================
# The constructor-field arm (#1092), which needs the checker's tables
# =====================================================================

_CTOR_FIELD_IF = """\
private data Box<T> { MkB(T) }

public fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Byte> = MkB(if @Bool.0 then { 200 } else { 3 });
  match @Box<Byte>.0 {
    MkB(@Byte) -> byte_to_int(@Byte.0)
  }
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  f(true)
}
"""


def _run_checked(source: str, fn: str | None = None) -> int:
    """Compile through the REAL pipeline (checker tables threaded) and run.

    The #1092 constructor-field width keys on the checker-recorded TARGET
    type (`_target_codegen_type_full`, the #820 side-table), so this arm is
    only observable when those artifacts are threaded — exactly as the CLI
    threads them.  Mirrors the helper of the same name in
    `tests/test_codegen_alias_of_adt_eq_show_1085.py`, which pins the
    top-level-literal half of the same boundary.
    """
    import tempfile
    from pathlib import Path

    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile, execute
    from vera.parser import parse_file
    from vera.transform import transform

    f = tempfile.NamedTemporaryFile(  # noqa: SIM115 — Windows fixture; closed + unlinked below
        mode="w", suffix=".vera", delete=False, encoding="utf-8"
    )
    try:
        with f:
            f.write(source)
        tree = parse_file(f.name)
        program = transform(tree)
        diags, arts = typecheck_with_artifacts(
            program, source=source, file=f.name,
        )
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, f"check errors: {errors}"
        result = codegen_compile(
            program, source=source, file=f.name,
            expr_semantic_types=arts.expr_semantic_types,
            expr_target_types=arts.expr_target_types,
        )
        cerrors = [d for d in result.diagnostics if d.severity == "error"]
        assert not cerrors, f"compile errors: {cerrors}"
        exec_result = execute(result, fn_name=fn)
        assert exec_result.value is not None, "Expected a return value"
        return exec_result.value
    finally:
        Path(f.name).unlink(missing_ok=True)


def test_a_byte_field_literal_inside_a_join_is_stored_at_i32() -> None:
    """The #1092 boundary, spelled with the literal in a branch.

    200 is the discriminating value: the field is read back through the
    match, which sizes it from the INSTANTIATED type (Byte -> i32), so an
    i64 store reads back a different number rather than merely failing.
    """
    assert _run_checked(_CTOR_FIELD_IF) == 200
    assert _run_checked(_CTOR_FIELD_IF.replace("f(true)", "f(false)")) == 3
