"""Tests for vera.codegen — arrays (Byte type, array literals/bounds/length/range/concat, compound arrays, array utilities).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_io,
    _run_trap,
)


# =====================================================================
# C6k: Byte type
# =====================================================================


class TestByteType:
    def test_byte_identity(self) -> None:
        src = """
public fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure) {
  @Byte.0
}
"""
        assert _run(src, fn="f", args=[42]) == 42

    def test_byte_zero(self) -> None:
        src = """
public fn f(-> @Byte) requires(true) ensures(true) effects(pure) {
  0
}
"""
        assert _run(src) == 0

    def test_byte_max(self) -> None:
        src = """
public fn f(-> @Byte) requires(true) ensures(true) effects(pure) {
  255
}
"""
        assert _run(src) == 255

    def test_byte_let_binding(self) -> None:
        src = """
public fn f(@Byte -> @Byte) requires(true) ensures(true) effects(pure) {
  let @Byte = @Byte.0;
  @Byte.0
}
"""
        assert _run(src, fn="f", args=[100]) == 100

    def test_byte_eq(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 == @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        assert _run(src, fn="f", args=[5, 6]) == 0

    def test_byte_lt_unsigned(self) -> None:
        # @Byte.0 = second param (de Bruijn 0), @Byte.1 = first param
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 < @Byte.1
}
"""
        # f(200, 10): @Byte.0=10, @Byte.1=200 → 10 < 200 = true
        assert _run(src, fn="f", args=[200, 10]) == 1
        # f(10, 200): @Byte.0=200, @Byte.1=10 → 200 < 10 = false
        assert _run(src, fn="f", args=[10, 200]) == 0

    def test_byte_gt_unsigned(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 > @Byte.1
}
"""
        # f(10, 200): @Byte.0=200, @Byte.1=10 → 200 > 10 = true
        assert _run(src, fn="f", args=[10, 200]) == 1
        # f(200, 10): @Byte.0=10, @Byte.1=200 → 10 > 200 = false
        assert _run(src, fn="f", args=[200, 10]) == 0

    def test_byte_le(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 <= @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        # f(6, 5): @Byte.0=5, @Byte.1=6 → 5 <= 6 = true
        assert _run(src, fn="f", args=[6, 5]) == 1
        # f(5, 6): @Byte.0=6, @Byte.1=5 → 6 <= 5 = false
        assert _run(src, fn="f", args=[5, 6]) == 0

    def test_byte_ge(self) -> None:
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 >= @Byte.1
}
"""
        assert _run(src, fn="f", args=[5, 5]) == 1
        # f(5, 6): @Byte.0=6, @Byte.1=5 → 6 >= 5 = true
        assert _run(src, fn="f", args=[5, 6]) == 1
        # f(6, 5): @Byte.0=5, @Byte.1=6 → 5 >= 6 = false
        assert _run(src, fn="f", args=[6, 5]) == 0

    def test_byte_unsigned_comparison_wat(self) -> None:
        """Byte comparisons should use unsigned i32 ops."""
        src = """
public fn f(@Byte, @Byte -> @Bool) requires(true) ensures(true) effects(pure) {
  @Byte.0 < @Byte.1
}
"""
        result = _compile_ok(src)
        assert "i32.lt_u" in result.wat


# =====================================================================
# C6k: Array literals
# =====================================================================


class TestArrayLit:
    def test_int_array_index_0(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 10

    def test_int_array_index_1(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_int_array_index_2(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_single_element_array(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 42

    def test_bool_array(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Bool> = [true, false, true];
  @Array<Bool>.0[1]
}
"""
        assert _run(src) == 0

    def test_array_wat_has_alloc(self) -> None:
        """Array literal WAT should contain call $alloc."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert "call $alloc" in result.wat

    def test_array_wat_has_bounds_check(self) -> None:
        """Array indexing WAT should contain unreachable for OOB."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[0]
}
"""
        result = _compile_ok(src)
        assert "unreachable" in result.wat


# =====================================================================
# C6k: Array bounds checking
# =====================================================================


class TestArrayBoundsCheck:
    def test_oob_positive_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[3]
}
"""
        _run_trap(src)

    def test_oob_large_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[100]
}
"""
        _run_trap(src)

    def test_last_valid_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_first_valid_index(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 10


# =====================================================================
# C6k: Array length
# =====================================================================


class TestArrayLength:
    def test_length_three(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 3

    def test_length_one(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [42];
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 1

    def test_length_in_comparison(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20, 30];
  array_length(@Array<Int>.0) == 3
}
"""
        assert _run(src) == 1

    def test_length_in_let(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3, 4, 5];
  let @Int = array_length(@Array<Int>.0);
  @Int.0
}
"""
        assert _run(src) == 5

    # --- array_append (#242) ---

    def test_array_append_length(self) -> None:
        """array_append returns an array with length + 1."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_append([1, 2, 3], 4))
}
"""
        assert _run(src) == 4

    def test_array_append_element_value(self) -> None:
        """The appended element is accessible at the last index."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_append([10, 20, 30], 99);
  @Array<Int>.0[3]
}
"""
        assert _run(src) == 99

    def test_array_append_preserves_existing(self) -> None:
        """array_append preserves all existing elements."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_append([10, 20, 30], 99);
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_array_append_empty(self) -> None:
        """array_append onto empty array produces [elem]."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_append([], 42);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 42

    def test_array_fn_param_compiles(self) -> None:
        """Functions with Array params should compile with pair params."""
        src = """
public fn f(@Array<Int> -> @Int) requires(true) ensures(true) effects(pure) {
  @Array<Int>.0[0]
}
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  42
}
"""
        result = _compile_ok(src)
        # Both f and g should compile
        assert "$f" in result.wat
        assert "$g" in result.wat
        # f should have pair params
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat


# =====================================================================
# Array construction builtins (#209)
# =====================================================================


class TestArrayRange:
    """Tests for array_range(start, end) → Array<Int>."""

    def test_range_length(self) -> None:
        """array_range(0, 5) produces an array of length 5."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(0, 5))
}
"""
        assert _run(src) == 5

    def test_range_first_element(self) -> None:
        """First element of array_range(3, 7) is 3."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_range(3, 7);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 3

    def test_range_last_element(self) -> None:
        """Last element of array_range(3, 7) is 6 (end-exclusive)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_range(3, 7);
  @Array<Int>.0[3]
}
"""
        assert _run(src) == 6

    def test_range_empty_reversed(self) -> None:
        """array_range(5, 3) produces an empty array."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(5, 3))
}
"""
        assert _run(src) == 0

    def test_range_empty_equal(self) -> None:
        """array_range(5, 5) produces an empty array."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(5, 5))
}
"""
        assert _run(src) == 0

    def test_range_negative_start(self) -> None:
        """array_range with negative start works correctly."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_range(0 - 2, 2);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == -2

    def test_range_negative_length(self) -> None:
        """array_range with negative start has correct length."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_range(0 - 2, 3))
}
"""
        assert _run(src) == 5


class TestArrayConcat:
    """Tests for array_concat(array_a, array_b) → Array<T>."""

    def test_concat_length(self) -> None:
        """Concatenation has combined length."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_concat([1, 2], [3, 4, 5]))
}
"""
        assert _run(src) == 5

    def test_concat_first_half(self) -> None:
        """Elements from first array are preserved."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([10, 20], [30, 40]);
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 20

    def test_concat_second_half(self) -> None:
        """Elements from second array are at the right offset."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([10, 20], [30, 40]);
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 30

    def test_concat_empty_left(self) -> None:
        """Concatenating empty left with non-empty right works."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([], [1, 2]);
  @Array<Int>.0[0]
}
"""
        assert _run(src) == 1

    def test_concat_empty_right(self) -> None:
        """Concatenating non-empty left with empty right works."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_concat([1, 2], []))
}
"""
        assert _run(src) == 2

    def test_concat_both_empty(self) -> None:
        """Concatenating two empty arrays produces empty."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  array_length(array_concat([], []))
}
"""
        assert _run(src) == 0


# =====================================================================
# Indexing directly on a builtin call result (#1048)
# =====================================================================


class TestIndexBuiltinCallResult:
    """Indexing directly on a builtin call result — `array_concat(...)[i]`
    — must infer the element type and compile, not drop the enclosing
    function via [E602] (#1048).

    Pre-fix, `_infer_index_element_type_expr`'s FnCall arm resolved only
    user-function returns (via `_fn_ret_type_exprs`); a builtin call had
    no entry there, element-type inference returned None, and the whole
    function was skipped.  The let-bound form (the control below) always
    worked — it resolves through the SlotRef arm, not the FnCall arm.
    """

    def test_index_array_concat_result_int(self) -> None:
        """Direct index on array_concat result — Int element (arg-forward
        resolution).  Pre-fix this dropped `g` via [E602] (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_concat([10, 20], [30, 40])[2]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_array_range_result_int(self) -> None:
        """Direct index on array_range result — resolves via the
        `_BUILTIN_PARAMETERIZED_RETURNS` table (Array<Int>), a different
        sub-path from array_concat's arg-forwarding (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_range(10, 20)[3]
}
"""
        assert _run(src, fn="g") == 13

    def test_index_array_slice_result_int(self) -> None:
        """Direct index on array_slice result — 3-arg arg-forward builtin
        (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_slice([10, 20, 30, 40, 50], 1, 4)[1]
}
"""
        assert _run(src, fn="g") == 30

    def test_index_array_concat_result_string(self) -> None:
        """Direct index on array_concat of Array<String>, then
        `string_length` — proves PAIR (pointer+length) elements resolve
        through the new arm, not only scalar Int (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(array_concat(["ab", "cd"], ["efg"])[2])
}
"""
        assert _run(src, fn="g") == 3

    def test_index_builtin_call_no_e602_drop(self) -> None:
        """Structural: the direct-index-on-builtin-call function must be
        emitted, i.e. NO [E602] "function skipped" diagnostic (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  array_concat([10, 20], [30, 40])[2]
}
"""
        result = _compile_ok(src)
        assert not any(d.error_code == "E602" for d in result.diagnostics), \
            "array_concat(...)[i] should not drop the function via E602"

    def test_index_builtin_call_let_bound_control(self) -> None:
        """Control: the let-bound form resolves through the SlotRef arm and
        stays green independently of the FnCall-arm fix (#1048)."""
        src = """
public fn g(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_concat([10, 20], [30, 40]);
  @Array<Int>.0[2]
}
"""
        assert _run(src, fn="g") == 30


# =====================================================================
# C8e: Arrays of compound types (#132)
# =====================================================================


class TestCompoundArrays:
    """Test arrays with compound element types (ADTs, Strings, nested arrays)."""

    def test_option_array_some(self) -> None:
        """Array<Option<Int>> — construct and index Some element."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(10), None, Some(30)];
  match @Array<Option<Int>>.0[0] {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 10

    def test_option_array_none(self) -> None:
        """Array<Option<Int>> — index None element."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(10), None, Some(30)];
  match @Array<Option<Int>>.0[1] {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""
        assert _run(src) == -1

    def test_option_array_index_2(self) -> None:
        """Array<Option<Int>> — index third element."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(10), None, Some(30)];
  match @Array<Option<Int>>.0[2] {
    Some(@Int) -> @Int.0,
    None -> 0 - 1
  }
}
"""
        assert _run(src) == 30

    def test_option_array_length(self) -> None:
        """array_length() on Array<Option<Int>>."""
        src = """
private data Option<T> { None, Some(T) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Option<Int>> = [Some(1), None, Some(3), None];
  array_length(@Array<Option<Int>>.0)
}
"""
        assert _run(src) == 4

    def test_string_array(self) -> None:
        """Array<String> — construct and index, check string_length."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "world", "!"];
  string_length(@Array<String>.0[0])
}
"""
        assert _run(src) == 5

    def test_string_array_index_1(self) -> None:
        """Array<String> — index second element."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "world", "!"];
  string_length(@Array<String>.0[1])
}
"""
        assert _run(src) == 5

    def test_string_array_index_2(self) -> None:
        """Array<String> — index third element."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "world", "!"];
  string_length(@Array<String>.0[2])
}
"""
        assert _run(src) == 1

    def test_string_array_length(self) -> None:
        """array_length() on Array<String>."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["a", "bb", "ccc"];
  array_length(@Array<String>.0)
}
"""
        assert _run(src) == 3

    def test_string_array_io(self) -> None:
        """Array<String> — print indexed element."""
        src = """
effect IO {
  op print(String -> Unit);
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = ["hello", "world"];
  IO.print(@Array<String>.0[1]);
  ()
}
"""
        assert _run_io(src) == "world"

    def test_nested_array(self) -> None:
        """Array<Array<Int>> — construct nested, index outer, then inner."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [10, 20];
  let @Array<Array<Int>> = [@Array<Int>.0, @Array<Int>.0];
  @Array<Array<Int>>.0[0][1]
}
"""
        assert _run(src) == 20

    def test_nested_array_length(self) -> None:
        """array_length() on Array<Array<Int>>."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [1, 2, 3];
  let @Array<Array<Int>> = [@Array<Int>.0, @Array<Int>.0, @Array<Int>.0];
  array_length(@Array<Array<Int>>.0)
}
"""
        assert _run(src) == 3

    def test_nested_alias_array_length_559(self) -> None:
        """#559 — `type Row = Array<Int>; type Grid = Array<Row>;`
        with `array_length(@Grid.0[0])` compiles and runs.

        Pre-fix `_alias_array_element` returned `NamedType("Row")`
        as the element type of `@Grid.0`.  Downstream WASM-type
        lookups treated `Row` as a scalar (it's an alias name, not
        the canonical `Array<Int>` shape) and emitted a load-as-i32
        + ``i64.extend_i32_u`` against what is actually a heap
        pointer to a (ptr, len) pair — WASM validation rejected the
        module with ``type mismatch: expected a type but nothing on
        stack``.  Post-fix the helper canonicalises the returned
        element type, so the chained-indexing branch in
        ``_infer_index_element_type_expr`` and the downstream size
        lookups both see ``NamedType("Array", (Int,))`` and emit
        the correct i32_pair load.
        """
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10]];
  array_length(@Grid.0[0])
}
"""
        assert _run(src) == 1

    def test_nested_alias_2d_index_559(self) -> None:
        """#559 — 2D index through nested aliases.

        Verifies the chained-indexing branch in
        ``_infer_index_element_type_expr`` succeeds for
        ``@Grid.0[0][1]``: the inner IndexExpr's element type must
        be canonicalised to ``Array<Int>`` so the outer's check
        ``inner_te.name == "Array"`` matches.
        """
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Grid = [[10, 20], [30, 40]];
  @Grid.0[1][0]
}
"""
        assert _run(src) == 30

    def test_result_array(self) -> None:
        """Array<Result<Int, String>> — construct and match on indexed element."""
        src = """
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Result<Int, String>> = [Ok(42), Err("bad")];
  match @Array<Result<Int, String>>.0[0] {
    Ok(@Int) -> @Int.0,
    Err(_) -> 0 - 1
  }
}
"""
        assert _run(src) == 42

    def test_result_array_err(self) -> None:
        """Array<Result<Int, String>> — index Err element."""
        src = """
private data Result<T, E> { Ok(T), Err(E) }

public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Result<Int, String>> = [Ok(42), Err("bad")];
  match @Array<Result<Int, String>>.0[1] {
    Ok(@Int) -> @Int.0,
    Err(_) -> 0 - 1
  }
}
"""
        assert _run(src) == -1


class TestFutureElementArrays1045:
    """#1045: `Array<Future<T>>` element representation.

    `Future<T>` is representation-transparent (#841), so an array whose
    element type is `Future<T>` must size/load/store its elements at the
    payload T's width.  Pre-fix the five module-level element helpers in
    `vera/wasm/helpers.py` name-matched only "String" / "Array" / the
    scalar dict with no Future strip, so `Array<Future<Int>>` sized each
    element as a 4-byte i32 and stored the i64 payload with `i32.store`
    (trap "expected i32, found i64"), while `Array<Future<String>>` (a
    pair payload) was treated as a single i32 and left the len half on
    the stack ("values remaining on stack").  The fix strips `Future<…>`
    at the top of each helper via a shared `_strip_future`.
    """

    def test_array_future_int_length(self) -> None:
        """`array_length(Array<Future<Int>>)` — length only.

        RED before the fix: laying out the i64 payloads through the i32
        element path trapped at WASM validation ("expected i32, found
        i64") before the length could be read.
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(10);
  let @Future<Int> = async(20);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  array_length(@Array<Future<Int>>.0)
}
"""
        assert _run(src, "f") == 2

    def test_array_future_int_element_readback(self) -> None:
        """Index an `Array<Future<Int>>` element and await it.

        The distinguishing value 4242 cannot coincide with the i32
        default path's wrong result.  RED before the fix: the same
        i32/i64 store mismatch traps at validation.
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(4242);
  let @Future<Int> = async(1717);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  await(@Array<Future<Int>>.0[0])
}
"""
        assert _run(src, "f") == 4242

    def test_array_future_string_length(self) -> None:
        """`array_length(Array<Future<String>>)` — length only.

        RED before the fix: the pair payload was treated as one i32, so
        the array-literal store left values on the stack ("values
        remaining on stack at end of block").
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("hello");
  let @Future<String> = async("worldwide");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  array_length(@Array<Future<String>>.0)
}
"""
        assert _run(src, "f") == 2

    def test_array_future_string_element_readback(self) -> None:
        """Index an `Array<Future<String>>` element, await, measure it.

        Element [1] is "worldwide" (length 9), distinct from element [0]
        "hello" (length 5) and from the 0/1 wrong-value defaults.  RED
        before the fix: the "values remaining on stack" trap.
        """
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("hello");
  let @Future<String> = async("worldwide");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  string_length(await(@Array<Future<String>>.0[1]))
}
"""
        assert _run(src, "f") == 9

    def test_array_plain_string_control(self) -> None:
        """Control: a plain `Array<String>` (no Future) already worked and
        must stay green — pins that the #1045 strip does not regress the
        bare-pair element path.  Two-element array, element [1] length 9."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<String> = ["hello", "worldwide"];
  string_length(@Array<String>.0[1])
}
"""
        assert _run(src, "f") == 9


class TestFutureCombinatorArrays1057:
    """#1057: array combinators over `Array<Future<T>>` returned garbage.

    `Future<T>` is representation-transparent (#841): its array-element
    width is its payload T's.  The combinators inferred the element type
    through `_infer_concat_elem_type` (or, for `array_append` /
    `array_flatten`, sibling AST walks), all of which returned the bare
    head `"Future"` — the type argument dropped.  `_element_mem_size`
    then could not `_strip_future` a bare `"Future"`, so it collapsed to
    the 4-byte i32 default and the copy loops ran a 4-byte stride over
    8-byte (i64 payload) or two-word (String payload) elements: silent
    wrong values (e.g. concat over `Array<Future<Int>>` returned
    9448928052300 for an expected 1122), a 400-vs-402 half-read for the
    String payload, and an "expected i32, found i64" validation trap for
    `array_append` (whose element local was still typed i32).  All
    check+verify-green.  The fix preserves the full `Future<…>` spelling
    at each inference site and strips the wrapper before choosing the
    append element local's WASM type.

    Every value below is chosen so a packed-half / wrong-stride misread
    cannot coincide with the correct answer.
    """

    def test_array_future_int_concat(self) -> None:
        """`array_concat(Array<Future<Int>>, …)` copies i64 payloads.

        RED before the fix: 4-byte stride over the 8-byte i64 elements
        returned 9448928052300, not 1122 (11*100 + 22)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Future<Int>> = array_concat(@Array<Future<Int>>.1, @Array<Future<Int>>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_int_slice(self) -> None:
        """`array_slice(Array<Future<Int>>, 1, 3)` keeps elements [44, 55].

        RED before the fix: 18897856102400, not 4455 (44*100 + 55)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(33);
  let @Future<Int> = async(44);
  let @Future<Int> = async(55);
  let @Array<Future<Int>> = [@Future<Int>.2, @Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_slice(@Array<Future<Int>>.0, 1, 3);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4455

    def test_array_future_int_append(self) -> None:
        """`array_append(Array<Future<Int>>, Future<Int>)` appends an i64.

        RED before the fix: the appended element local was typed i32
        while the pushed payload was i64 — a "expected i32, found i64"
        WASM validation trap (not a wrong value)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = array_append(@Array<Future<Int>>.0, @Future<Int>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_int_reverse(self) -> None:
        """`array_reverse(Array<Future<Int>>)` swaps [11, 22] to [22, 11].

        Non-palindromic values so a reverse that copied at the wrong
        stride cannot coincide.  RED before the fix: 4724464025600, not
        2211 (22*100 + 11)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_reverse(@Array<Future<Int>>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 2211

    def test_array_future_int_filter_keepall(self) -> None:
        """`array_filter(Array<Future<Int>>, |_| true)` keeps both i64s.

        The predicate is `pure` (an awaiting predicate is a checker
        error — you cannot compare an un-awaited Future), so a keep-all
        filter is the expressible form that still exercises the copy
        loop.  RED before the fix: the wrong-stride copy trapped at
        runtime."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Int>> = array_filter(
    @Array<Future<Int>>.0,
    fn(@Future<Int> -> @Bool) effects(pure) { true }
  );
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_int_flatten(self) -> None:
        """`array_flatten(Array<Array<Future<Int>>>)` copies inner i64s.

        `array_flatten` recovers the inner element type by an AST walk
        (not `_infer_concat_elem_type`), which independently dropped the
        `Future` arg.  RED before the fix: 9448928052300, not 1122."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(11);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Array<Future<Int>>> = [@Array<Future<Int>>.1, @Array<Future<Int>>.0];
  let @Array<Future<Int>> = array_flatten(@Array<Array<Future<Int>>>.0);
  await(@Array<Future<Int>>.0[0]) * 100 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_array_future_string_concat(self) -> None:
        """`array_concat(Array<Future<String>>, …)` copies pair payloads.

        A `Future<String>` element is a two-word (ptr, len) pair like its
        payload.  RED before the fix: treated as a single i32, the concat
        mangled the pair and `string_length` read back 400, not 402
        (len 4 * 100 + len 2)."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("aaaa");
  let @Future<String> = async("bb");
  let @Array<Future<String>> = [@Future<String>.1];
  let @Array<Future<String>> = [@Future<String>.0];
  let @Array<Future<String>> = array_concat(@Array<Future<String>>.1, @Array<Future<String>>.0);
  string_length(await(@Array<Future<String>>.0[0])) * 100
    + string_length(await(@Array<Future<String>>.0[1]))
}
"""
        assert _run(src, "f") == 402

    def test_array_plain_int_concat_control(self) -> None:
        """Control: `array_concat` over a plain `Array<Int>` (no Future)
        already worked and must stay green — pins that the #1057
        full-spelling change does not regress the bare-i64 element
        path.  11*100 + 22 = 1122."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = [11];
  let @Array<Int> = [22];
  let @Array<Int> = array_concat(@Array<Int>.1, @Array<Int>.0);
  @Array<Int>.0[0] * 100 + @Array<Int>.0[1]
}
"""
        assert _run(src, "f") == 1122


class TestAliasFutureArrayElement1058:
    """#1058: an aliased `Future<T>` array-literal element trapped.

    `type FI = Future<Int>; let @Array<FI> = [async(1)]` was check-green
    then trapped "expected i32, found i64".  `_translate_array_lit`
    resolved the element name with the name-only `_resolve_base_type_name`
    (dropping the alias's args, `FI` -> bare `"Future"`), so the i64
    payload was stored with `i32.store`.  The fix canonicalizes the alias
    to its full compound spelling (`Future<Int>`) via
    `_canonicalize_alias_slot_name` before the resolve, mirroring the
    `_is_pair_type_name` order (#1046).
    """

    def test_alias_future_int_array_element(self) -> None:
        """`type FI = Future<Int>; let @Array<FI> = [@FI.1, @FI.0]`.

        RED before the fix: storing the i64 payload through the bare-
        `"Future"` i32 path trapped at WASM validation ("expected i32,
        found i64").  `@FI.1`=7, `@FI.0`=8, so 7*10 + 8 = 78."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(7);
  let @FI = async(8);
  let @Array<FI> = [@FI.1, @FI.0];
  await(@Array<FI>.0[0]) * 10 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 78

    def test_alias_future_string_array_element(self) -> None:
        """An aliased pair-payload `Future<String>` array element.

        `type FS = Future<String>`: the canonicalized `Future<String>`
        must be recognized as a two-word pair.  RED before the fix: bare
        `"Future"` sized it as one i32 and the literal store left the len
        half on the stack ("values remaining on stack").  Element [1] is
        "worldwide" (length 9)."""
        src = """
type FS = Future<String>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FS = async("hello");
  let @FS = async("worldwide");
  let @Array<FS> = [@FS.1, @FS.0];
  string_length(await(@Array<FS>.0[1]))
}
"""
        assert _run(src, "f") == 9

    def test_alias_to_array_element_control(self) -> None:
        """Control: an aliased *Array* element (`type Row = Array<Int>`)
        already worked (bare "Array" is still recognized as a pair) and
        must stay green — pins that adding the canonicalize step does not
        regress the non-Future alias path.  11*100 + 22 = 1122."""
        src = """
type Row = Array<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [11, 22];
  let @Array<Row> = [@Row.0];
  @Array<Row>.0[0][0] * 100 + @Array<Row>.0[0][1]
}
"""
        assert _run(src, "f") == 1122

    def test_direct_future_int_array_element_control(self) -> None:
        """Control: the direct `Future<Int>` spelling (no alias) already
        worked (#1045) and must stay green — pins that #1058's
        canonicalize step leaves the non-alias path unchanged.
        `@Future<Int>.1`=7, `@Future<Int>.0`=8, so 7*10 + 8 = 78."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(7);
  let @Future<Int> = async(8);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  await(@Array<Future<Int>>.0[0]) * 10 + await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 78


class TestAliasElementCombinators1062:
    """#1062: array combinators over alias-spelled element types.

    The alias-spelled sibling of #1057, one layer down: once #1058 made
    `Array<FI>` (`type FI = Future<Int>`) literals buildable, the
    combinators received the ALIAS name as the element type — bare,
    unresolved — from three sites (`_infer_concat_elem_type` for
    concat/slice/reverse/filter, the `array_append` element inference,
    and the `array_flatten` inner-type walk).  The module-level element
    helpers have no alias table, so the raw name fell to the 4-byte i32
    default: silent-wrong values for Future-aliases (e.g. concat
    returned 9448928052300 for an expected 1122), an "expected i32,
    found i64" validation trap for append, and — reachable even before
    #1058 — a wrong element for a scalar alias like `type Flag = Bool`
    (whose 1-byte elements were copied at a 4-byte stride).  Each site
    now canonicalizes a bare alias name to its target's full compound
    spelling (then resolves refinements), mirroring the #1058
    literal-store fix; the index-read path was already alias-clean via
    `_alias_array_element`'s canonical element (#559).
    """

    def test_alias_future_int_concat(self) -> None:
        """`array_concat` over `Array<FI>`, `type FI = Future<Int>`.

        RED before the fix: bare "FI" fell to the 4-byte default and the
        concat returned 9448928052300, not 1122 (11*100 + 22)."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1];
  let @Array<FI> = [@FI.0];
  let @Array<FI> = array_concat(@Array<FI>.1, @Array<FI>.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_alias_future_string_concat(self) -> None:
        """`array_concat` over `Array<FS>`, `type FS = Future<String>`.

        The canonicalized `Future<String>` element is a two-word pair.
        RED before the fix: treated as one i32, the concat mangled the
        pair and read back 400, not 402 (len 4 * 100 + len 2)."""
        src = """
type FS = Future<String>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FS = async("aaaa");
  let @FS = async("bb");
  let @Array<FS> = [@FS.1];
  let @Array<FS> = [@FS.0];
  let @Array<FS> = array_concat(@Array<FS>.1, @Array<FS>.0);
  string_length(await(@Array<FS>.0[0])) * 100
    + string_length(await(@Array<FS>.0[1]))
}
"""
        assert _run(src, "f") == 402

    def test_alias_future_int_reverse(self) -> None:
        """`array_reverse` over `Array<FI>` swaps [11, 22] to [22, 11].

        RED before the fix: 4724464025600, not 2211 (22*100 + 11)."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1, @FI.0];
  let @Array<FI> = array_reverse(@Array<FI>.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 2211

    def test_alias_future_int_append(self) -> None:
        """`array_append(Array<FI>, @FI.0)` appends through the alias.

        The element inference returns the bare alias name for `@FI.0`,
        so the element local was typed i32 while the pushed payload was
        i64.  RED before the fix: "expected i32, found i64" WASM
        validation trap."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1];
  let @Array<FI> = array_append(@Array<FI>.0, @FI.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_alias_future_int_flatten(self) -> None:
        """`array_flatten(Array<Array<FI>>)` copies aliased inner i64s.

        The flatten inner-type AST walk returned the bare alias name.
        RED before the fix: 9448928052300, not 1122."""
        src = """
type FI = Future<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @FI = async(11);
  let @FI = async(22);
  let @Array<FI> = [@FI.1];
  let @Array<FI> = [@FI.0];
  let @Array<Array<FI>> = [@Array<FI>.1, @Array<FI>.0];
  let @Array<FI> = array_flatten(@Array<Array<FI>>.0);
  await(@Array<FI>.0[0]) * 100 + await(@Array<FI>.0[1])
}
"""
        assert _run(src, "f") == 1122

    def test_alias_scalar_bool_concat(self) -> None:
        """`array_concat` over `Array<Flag>`, `type Flag = Bool`.

        Pins that the canonicalizer (not a Future special case) is what
        fixes alias-spelled elements: a scalar alias's 1-byte elements
        were copied at the 4-byte default stride.  Unlike the Future
        cases this was reachable-and-wrong before #1058 (the literal
        never trapped — its elements are Bool literals).  [true, false]
        ++ [true] reads back 100+20+1.  RED before the fix: 122
        (element [2] misread as false)."""
        src = """
type Flag = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Flag> = [true, false];
  let @Array<Flag> = [true];
  let @Array<Flag> = array_concat(@Array<Flag>.1, @Array<Flag>.0);
  let @Int = if @Array<Flag>.0[0] then { 100 } else { 200 };
  let @Int = if @Array<Flag>.0[1] then { 10 } else { 20 };
  let @Int = if @Array<Flag>.0[2] then { 1 } else { 2 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 121

    def test_alias_array_collection_control(self) -> None:
        """Control: an alias naming the COLLECTION (`type Row =
        Array<Int>`, concat of `@Row` slots) was green before #1064 by
        coincidence — the element probe returned None and concat's
        8-byte fallback happened to match Int — and must stay green now
        that the #1064 collection arm resolves it to a principled
        `Int`/8: same value, correct by construction.  11*100 + 22 =
        1122."""
        src = """
type Row = Array<Int>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [11];
  let @Row = [22];
  let @Row = array_concat(@Row.1, @Row.0);
  @Row.0[0] * 100 + @Row.0[1]
}
"""
        assert _run(src, "f") == 1122


class TestAliasCollectionCombinators1064:
    """#1064: combinators over alias-NAMED collections.

    `type Flags = Array<Bool>; array_concat(@Flags.1, @Flags.0)` — the
    collection slot's own name misses the `Array` match in the element
    probe (`_infer_concat_elem_type`), distinct from the alias-spelled
    ELEMENT case (#1062).  The probe returned None, and each consumer
    fell back: concat to an 8-byte default stride — coincidentally
    correct for Int / String / pair elements (which is why the shape
    survived), silently wrong for 1-byte Bool / Byte elements — and
    slice / the map-family to a loud E602 skip.  A literal whose
    elements are alias-typed slots (`array_concat([@Flags.0], …)`) hit
    the sibling literal-branch hole: the bare alias name sized the
    two-word pair elements at 4 bytes and indexing the result trapped
    `unreachable`.  Pre-existing on main (reachable without any of the
    #1057/#1058/#1062 enablers — aliased-collection literals never
    trapped).  The probe now canonicalizes the collection name to its
    target's full spelling, extracts the element spelling, and
    canonicalizes a bare element name in turn; the literal branch
    canonicalizes bare inferred names the same way.
    """

    def test_alias_bool_collection_concat(self) -> None:
        """Concat of `@Flags` slots, 1-byte Bool elements.

        [true, false] ++ [true] reads back 100+20+1 = 121.  RED before
        the fix: 122 — the 8-byte default stride misread element [2]
        as false."""
        src = """
type Flags = Array<Bool>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Flags = [true, false];
  let @Flags = [true];
  let @Flags = array_concat(@Flags.1, @Flags.0);
  let @Int = if @Flags.0[0] then { 100 } else { 200 };
  let @Int = if @Flags.0[1] then { 10 } else { 20 };
  let @Int = if @Flags.0[2] then { 1 } else { 2 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 121

    def test_alias_byte_collection_concat(self) -> None:
        """Concat of `@Bytes` slots, 1-byte Byte elements.

        Byte values enter via host args (Vera has no Byte literal;
        `int_to_byte` returns `Option<Byte>`).  Args [3, 5, 7] build
        [3, 5] ++ [7] and read back 3*100 + 5*10 + 7 = 357.  RED
        before the fix: 350 — element [2] misread as 0."""
        src = """
type Bytes = Array<Byte>;
public fn f(@Byte, @Byte, @Byte -> @Int) requires(true) ensures(true) effects(pure) {
  let @Bytes = [@Byte.2, @Byte.1];
  let @Bytes = [@Byte.0];
  let @Bytes = array_concat(@Bytes.1, @Bytes.0);
  byte_to_int(@Bytes.0[0]) * 100 + byte_to_int(@Bytes.0[1]) * 10
    + byte_to_int(@Bytes.0[2])
}
"""
        assert _run(src, "f", args=[3, 5, 7]) == 357

    def test_alias_bool_collection_slice(self) -> None:
        """`array_slice` over an alias-named collection.

        slice(1, 3) of [true, false, true] keeps [false, true] →
        20 + 1 = 21.  RED before the fix: the None element type was a
        loud CodegenSkip — the enclosing function was dropped and the
        run failed with no exported function (a skip-to-working unlock,
        not a silent-wrong)."""
        src = """
type Flags = Array<Bool>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Flags = [true, false, true];
  let @Flags = array_slice(@Flags.0, 1, 3);
  let @Int = if @Flags.0[0] then { 10 } else { 20 };
  let @Int = if @Flags.0[1] then { 1 } else { 2 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 21

    def test_alias_collection_of_aliased_rows_concat(self) -> None:
        """`type Grid = Array<Row>; type Row = Array<Int>` — the
        collection arm's INNER element canonicalize is load-bearing.

        The target spelling of `Grid` keeps `Row` opaque
        (`"Array<Row>"`), so the extracted element is itself a bare
        alias: without the second canonicalize it would fall to the
        4-byte default and REGRESS this previously-green program (its
        pair elements matched the old 8-byte None-fallback by
        coincidence).  Green before and after — same value, correct by
        construction after.  Row [11, 22] lands at index [1] of the
        concat; [1][0]*100 + [1][1] = 1122."""
        src = """
type Row = Array<Int>;
type Grid = Array<Row>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Row = [11, 22];
  let @Grid = [@Row.0];
  let @Grid = [@Row.0];
  let @Grid = array_concat(@Grid.1, @Grid.0);
  @Grid.0[1][0] * 100 + @Grid.0[1][1]
}
"""
        assert _run(src, "f") == 1122

    def test_array_lit_of_aliased_collection_concat(self) -> None:
        """Literal-branch variant: `array_concat([@Flags.1], [@Flags.0])`.

        The literal's element infers to the bare alias name "Flags",
        which sized the two-word `Array<Bool>` pair elements at 4
        bytes.  RED before the fix: check-green, then the mangled pair
        trapped `unreachable` when indexed.  Element [1][0] is true →
        1."""
        src = """
type Flags = Array<Bool>;
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Flags = [true, false];
  let @Flags = [true];
  let @Array<Array<Bool>> = array_concat([@Flags.1], [@Flags.0]);
  let @Int = if @Array<Array<Bool>>.0[1][0] then { 1 } else { 2 };
  @Int.0
}
"""
        assert _run(src, "f") == 1


class TestFutureAliasPayloadElement1074:
    """#1074: an array element spelled `Future<Alias>` was mis-sized.

    The alias-INSIDE-`Future<…>` sibling of #1062, one layer deeper.
    #1058/#1062 canonicalize an alias whose target IS a `Future<…>`
    (`type FI = Future<Int>`), and #1045/#1057 preserve the full
    `Future<T>` spelling for a direct payload — but neither reaches an
    alias sitting inside the wrapper's type argument
    (`Array<Future<FlagA>>`, `type FlagA = Bool`; or hidden one hop
    further, `type FF = Future<FlagA>; Array<FF>`).  The element-size /
    store-op deciders `_strip_future` the wrapper and hand the bare,
    unresolved alias (`FlagA`) to a name-keyed size dict with no alias
    table, so it fell to the 4-byte i32 default:

      * Bool/Byte payloads → **silent wrong values**: 1-byte-packed data
        read at a 4-byte stride (check+verify+compile all green).
      * Int/Nat/Float64/String payloads → a **WASM-validation trap**
        (`expected i32, found i64` / "values remaining on stack") at
        instantiation, behind an exit-0 compile.

    Pre-existing, not a regression: before this branch's combinator
    commits the Future branch returned bare `"Future"`, whose element
    size is the SAME 4-byte i32 — the identical wrong stride.  The
    branch fixed the non-alias (`Future<Int>` -> 8/i64) and
    alias-of-Future (`type FI = Future<Int>`) payloads; the
    alias-inside-`Future` variant was never within the canonicalizer's
    reach and had no fixture.  Found by the adversarial delta review of
    PR #1041's combinator commits; the fix ships on the same branch.

    The fix extends `_canonicalize_alias_slot_name` to recurse into the
    transparent `Future<…>` payload (`Future<FlagA>` -> `Future<Bool>`)
    and routes the four element-type deciders (`_infer_concat_elem_type`,
    `_translate_array_lit`, the `array_flatten` inner walk, and
    `_infer_index_element_type`) through it uniformly.
    """

    # -- Bool payload: silent wrong values --------------------------------

    def test_future_alias_bool_index_read(self) -> None:
        """Index-read through `Array<Future<FlagA>>`, `type FlagA = Bool`.

        Built at the correct 1-byte stride as `Array<Future<Bool>>`, then
        rebound to the alias spelling and indexed — so the ONLY buggy
        site is the index-read element decider.  [false, true]: [0] ->
        200, [1] -> 10, sum 210.  RED before the fix: 120 (both elements
        misread at the 4-byte stride)."""
        src = """
type FlagA = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<FlagA>> = @Array<Future<Bool>>.0;
  let @Int = if await(@Array<Future<FlagA>>.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<FlagA>>.0[1]) then { 10 } else { 20 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 210

    def test_future_alias_bool_concat(self) -> None:
        """`array_concat` over `Array<Future<FlagA>>`, `type FlagA = Bool`.

        [false, true] ++ itself reads back 2000+100+20+1 = 2121.  RED
        before the fix: 1111 (the 4-byte copy stride over 1-byte elements
        misread every element as true)."""
        src = """
type FlagA = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<FlagA>> = @Array<Future<Bool>>.0;
  let @Array<Future<FlagA>> = array_concat(@Array<Future<FlagA>>.0, @Array<Future<FlagA>>.0);
  let @Int = if await(@Array<Future<FlagA>>.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Array<Future<FlagA>>.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<FlagA>>.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<FlagA>>.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121

    def test_future_alias_bool_append(self) -> None:
        """`array_append` over `Array<Future<FlagA>>`, `type FlagA = Bool`.

        [false, true] then append true reads back 200+10+1 = 211.  RED
        before the fix: 111 (every element misread as true)."""
        src = """
type FlagA = Bool;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<FlagA>> = @Array<Future<Bool>>.0;
  let @Future<FlagA> = async(true);
  let @Array<Future<FlagA>> = array_append(@Array<Future<FlagA>>.0, @Future<FlagA>.0);
  let @Int = if await(@Array<Future<FlagA>>.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<FlagA>>.0[1]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<FlagA>>.0[2]) then { 1 } else { 2 };
  @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 211

    def test_hidden_alias_future_bool_index(self) -> None:
        """Hidden spelling `type FF = Future<FlagA>; type FlagA = Bool`.

        The alias is one hop further out — `Array<FF>` where `FF` itself
        aliases `Future<FlagA>`.  Canonicalizing `FF` lands on
        `Future<FlagA>`, whose `FlagA` payload must then resolve to
        `Bool`.  [false, true]: [0] -> 200, [1] -> 10, sum 210.  RED
        before the fix: 120."""
        src = """
type FlagA = Bool;
type FF = Future<FlagA>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<FF> = @Array<Future<Bool>>.0;
  let @Int = if await(@Array<FF>.0[0]) then { 100 } else { 200 };
  let @Int = if await(@Array<FF>.0[1]) then { 10 } else { 20 };
  @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 210

    # -- Scalar / pair payload: WASM-validation trap before the fix -------

    def test_future_alias_int_literal_store(self) -> None:
        """Literal `Array<Future<Big>>` store, `type Big = Int`, value >2^32.

        The literal-store element decider sized the i64 payload at 4
        bytes and emitted `i32.store`.  RED before the fix: an "expected
        i32, found i64" WASM-validation trap at instantiation, on a
        check+verify+compile-green program.  5000000001 - 22 =
        4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Big> = async(5000000001);
  let @Future<Big> = async(22);
  let @Array<Future<Big>> = [@Future<Big>.1, @Future<Big>.0];
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_future_alias_int_concat(self) -> None:
        """`array_concat` over `Array<Future<Big>>`, `type Big = Int`.

        RED before the fix: the i64 payload sized at 4 bytes trapped at
        WASM validation.  5000000001 - 22 = 4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Big> = async(5000000001);
  let @Future<Big> = async(22);
  let @Array<Future<Big>> = [@Future<Big>.1];
  let @Array<Future<Big>> = [@Future<Big>.0];
  let @Array<Future<Big>> = array_concat(@Array<Future<Big>>.1, @Array<Future<Big>>.0);
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_future_alias_int_rebind_concat(self) -> None:
        """Build direct `Future<Int>`, rebind to `Future<Big>`, concat.

        Isolates the concat element decider: the array is built at the
        correct 8-byte stride, then rebound to the alias spelling before
        concat.  RED before the fix: WASM-validation trap.  5000000001 -
        22 = 4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1, @Future<Int>.0];
  let @Array<Future<Big>> = @Array<Future<Int>>.0;
  let @Array<Future<Big>> = array_concat(@Array<Future<Big>>.0, @Array<Future<Big>>.0);
  await(@Array<Future<Big>>.0[0]) - await(@Array<Future<Big>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_hidden_alias_future_int_index(self) -> None:
        """Hidden spelling `type BigF = Future<Big>; type Big = Int`.

        `Array<BigF>` — `BigF` canonicalizes to `Future<Big>`, whose
        `Big` payload must then resolve to `Int`.  RED before the fix:
        WASM-validation trap.  5000000001 - 22 = 4999999979."""
        src = """
type Big = Int;
type BigF = Future<Big>;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @BigF = async(5000000001);
  let @BigF = async(22);
  let @Array<BigF> = [@BigF.1, @BigF.0];
  await(@Array<BigF>.0[0]) - await(@Array<BigF>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    def test_future_alias_string_concat(self) -> None:
        """`array_concat` over `Array<Future<StrA>>`, `type StrA = String`.

        The canonicalized `Future<String>` element is a two-word pair.
        RED before the fix: sized as one i32, the concat left the len
        half on the stack ("values remaining on stack" validation trap).
        "aaaa"(4) ++ "bb"(2), doubled → [4]*100 + [2] = 402."""
        src = """
type StrA = String;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<String> = async("aaaa");
  let @Future<String> = async("bb");
  let @Array<Future<String>> = [@Future<String>.1, @Future<String>.0];
  let @Array<Future<StrA>> = @Array<Future<String>>.0;
  let @Array<Future<StrA>> = array_concat(@Array<Future<StrA>>.0, @Array<Future<StrA>>.0);
  string_length(await(@Array<Future<StrA>>.0[0])) * 100
    + string_length(await(@Array<Future<StrA>>.0[1]))
}
"""
        assert _run(src, "f") == 402

    def test_future_alias_int_flatten(self) -> None:
        """`array_flatten(Array<Array<Future<Big>>>)`, `type Big = Int`.

        The inner arrays are built at the correct 8-byte stride as
        `Array<Future<Int>>`; only the flatten inner-type walk sees the
        `Big` alias.  The flatten result is read back through the direct
        `Future<Int>` spelling, so this isolates the flatten site.  RED
        before the fix: 95194313217 (the 4-byte copy mangled the i64
        payloads), not 4999999979."""
        src = """
type Big = Int;
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Array<Future<Big>>> = [@Array<Future<Int>>.1, @Array<Future<Int>>.0];
  let @Array<Future<Big>> = array_flatten(@Array<Array<Future<Big>>>.0);
  let @Array<Future<Int>> = @Array<Future<Big>>.0;
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979

    # -- Differential twins: the direct spelling is green before AND after

    def test_direct_future_bool_concat_control(self) -> None:
        """Control twin of `test_future_alias_bool_concat`: the direct
        `Future<Bool>` spelling (no alias) already worked (#1057) and
        must stay green — pins that the #1074 payload canonicalize leaves
        the non-alias path unchanged.  2000+100+20+1 = 2121."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Bool> = async(false);
  let @Future<Bool> = async(true);
  let @Array<Future<Bool>> = [@Future<Bool>.1, @Future<Bool>.0];
  let @Array<Future<Bool>> = array_concat(@Array<Future<Bool>>.0, @Array<Future<Bool>>.0);
  let @Int = if await(@Array<Future<Bool>>.0[0]) then { 1000 } else { 2000 };
  let @Int = if await(@Array<Future<Bool>>.0[1]) then { 100 } else { 200 };
  let @Int = if await(@Array<Future<Bool>>.0[2]) then { 10 } else { 20 };
  let @Int = if await(@Array<Future<Bool>>.0[3]) then { 1 } else { 2 };
  @Int.3 + @Int.2 + @Int.1 + @Int.0
}
"""
        assert _run(src, "f") == 2121

    def test_direct_future_int_flatten_control(self) -> None:
        """Control twin of `test_future_alias_int_flatten`: the direct
        `Future<Int>` spelling already worked and must stay green —
        pins that the flatten-site canonicalize leaves the non-alias
        path unchanged.  5000000001 - 22 = 4999999979."""
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(<Async>) {
  let @Future<Int> = async(5000000001);
  let @Future<Int> = async(22);
  let @Array<Future<Int>> = [@Future<Int>.1];
  let @Array<Future<Int>> = [@Future<Int>.0];
  let @Array<Array<Future<Int>>> = [@Array<Future<Int>>.1, @Array<Future<Int>>.0];
  let @Array<Future<Int>> = array_flatten(@Array<Array<Future<Int>>>.0);
  await(@Array<Future<Int>>.0[0]) - await(@Array<Future<Int>>.0[1])
}
"""
        assert _run(src, "f") == 4999999979


class TestArrayUtilities:
    """#466 phase 1: array_mapi, _reverse, _find, _any, _all,
    _flatten, _sort_by — all iterative WASM, no Eq/Ord dispatch.

    Tests aim to verify *values* not just lengths.  Where Vera lacks a
    direct array-indexing primitive, we fold the result back to a
    single Int (e.g. positional digit packing for ordered sequences,
    or sum for length-preserving ops) so a single ``_run() ==`` check
    pins down the entire output.
    """

    def test_array_mapi_passes_index(self) -> None:
        """array_mapi(range(10,15), |x,i| x + i*100) → [10, 111, 212, 313, 414].

        Sum = 1060.  Uses a non-identity input range so element
        values and indices are distinct: a translator that
        accidentally swapped the (elem, idx) callback arguments
        would compute idx + elem*100 instead, summing to 6010 —
        clearly different from 1060.  The earlier
        ``array_range(0, 5)`` form had element[i] == i, so a
        swapped-args bug would have been masked because both
        orderings produced the same sum.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_mapi(
    array_range(10, 15),
    fn(@Int, @Nat -> @Int) effects(pure) {
      @Int.0 + nat_to_int(@Nat.0) * 100
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        # Elements 10, 11, 12, 13, 14 with indices 0, 1, 2, 3, 4:
        #   10 + 0*100 = 10
        #   11 + 1*100 = 111
        #   12 + 2*100 = 212
        #   13 + 3*100 = 313
        #   14 + 4*100 = 414
        # Sum = 1060.  Swapped (idx, elem) ordering gives:
        #   0 + 10*100 = 1000
        #   1 + 11*100 = 1101
        #   2 + 12*100 = 1202
        #   3 + 13*100 = 1303
        #   4 + 14*100 = 1404
        # Sum = 6010.  Test fails clearly under either bug.
        assert _run(src) == 1060

    def test_array_reverse_preserves_elements(self) -> None:
        """array_reverse([1..5]) sums to 15 — same elements, just reordered."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_reverse(array_range(1, 6));
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 15

    def test_array_reverse_actually_reverses(self) -> None:
        """Pack reversed [1..5] = [5,4,3,2,1] as digits → 54321.

        Catches a no-op implementation that returns the input
        unchanged.  Positional digit packing is order-sensitive.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_reverse(array_range(1, 6));
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 54321

    def test_array_mapi_empty_input(self) -> None:
        """array_mapi on an empty array returns an empty array.

        Exercises the len==0 path: the loop's initial bounds check
        (``idx >= arr_len`` with both 0) must break out immediately,
        no callback invocation, and the $alloc(0) must not trap.
        Folding over the empty result with a sum-counter yields 0.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_mapi(
    array_range(0, 0),
    fn(@Int, @Nat -> @Int) effects(pure) {
      @Int.0 + nat_to_int(@Nat.0)
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 0

    def test_array_reverse_empty_input(self) -> None:
        """array_reverse on an empty array returns an empty array."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_reverse(array_range(0, 0));
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        # Empty result, digit-packing fold neutral == 0.
        assert _run(src) == 0

    def test_array_flatten_empty_input(self) -> None:
        """array_flatten on an empty outer array returns an empty array.

        Exercises the len==0 path for the two-pass flatten: the
        first pass (summing inner lengths) exits at idx==0, total
        stays at 0, $alloc(0) succeeds, the second pass is likewise
        empty.  No trap despite the zero-byte allocation.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = [];
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 0

    def test_array_find_returns_first_match(self) -> None:
        """array_find([1..10], > 5) → Some(6) — first match, not last."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = array_find(
    array_range(1, 10),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 5 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(src) == 6

    def test_array_find_returns_none_when_no_match(self) -> None:
        """array_find returns None sentinel when every predicate is false."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = array_find(
    array_range(1, 5),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 100 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> -42
  }
}
"""
        assert _run(src) == -42

    def test_array_find_short_circuits(self) -> None:
        """array_find short-circuit properties that are observable in pure code.

        ``array_find``'s signature requires ``effects(pure)`` on the
        predicate, so we cannot count calls from inside Vera — that
        check would require mutable state, which pure functions
        cannot reach.  What IS observable without effects:

          (a) The *first* match wins, not a later one.  A predicate
              that's true for many elements must return Some(first),
              never Some(later).  Covered by
              ``test_array_find_returns_first_match`` on [1..10].

          (b) An empty array returns None rather than trapping on
              an out-of-bounds access.  Included below.

          (c) A predicate that is expensive at later indices but
              cheap at the first match still runs cheaply overall.
              This is the architectural short-circuit; we exercise
              the compile-time structure by ensuring a match at
              index 0 of a very large array returns immediately
              (the test would time out if every element were
              actually visited).

        The WAT's inner-loop structure (``br_if $brk_find`` on
        match) is the real guarantee; these tests confirm the
        externally visible behaviour is consistent with that.
        """
        # (b) empty-array base case — None rather than a trap
        empty_src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  let @Option<Int> = array_find(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { true }
  );
  match @Option<Int>.0 {
    Some(@Int) -> 1,
    None -> 0
  }
}
"""
        assert _run(empty_src) == 0

        # (c) big-array match-at-head: if the loop didn't break
        # early, `array_range(0, 10000)` would force the runtime to
        # walk all 10,000 elements before returning.  Matching on
        # the very first element exercises the short-circuit path.
        # Returned value (0) also confirms the first match wins.
        big_src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = array_find(
    array_range(0, 10000),
    fn(@Int -> @Bool) effects(pure) { @Int.0 == 0 }
  );
  match @Option<Int>.0 {
    Some(@Int) -> @Int.0,
    None -> -1
  }
}
"""
        assert _run(big_src) == 0

    def test_array_any(self) -> None:
        """array_any: true when at least one passes; false otherwise."""
        src_true = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_any(
    array_range(-3, 3),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        src_false = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_any(
    array_range(-3, 0),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        assert _run(src_true) == 1
        assert _run(src_false) == 0

    def test_array_all(self) -> None:
        """array_all: true when every element passes; false otherwise."""
        src_true = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_all(
    array_range(1, 6),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        src_false = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if array_all(
    array_range(-3, 3),
    fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }
  ) then { 1 } else { 0 }
}
"""
        assert _run(src_true) == 1
        assert _run(src_false) == 0

    def test_array_any_short_circuits_observably(self) -> None:
        """Head-match: array_any with assert(false) on the trailing
        element confirms the predicate is *not* invoked past the
        first match.

        Input is ``[1, 99]``.  Predicate returns true for 1 and
        traps via ``assert(false)`` for any other value.  If
        array_any short-circuits on the first match (correct
        behaviour), the second element is never visited and the
        program returns 1 cleanly.  A non-short-circuiting
        implementation would invoke the predicate on 99, hit the
        assert, and trap — caught by ``_run_trap`` failing to find
        a trap.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [1, 99];
  let @Bool = array_any(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) {
      if @Int.0 == 1 then { true } else { assert(false); false }
    }
  );
  if @Bool.0 then { 1 } else { 0 }
}
"""
        assert _run(src) == 1

    def test_array_all_short_circuits_observably(self) -> None:
        """Head-fail: array_all with assert(false) on the trailing
        element confirms the predicate is *not* invoked past the
        first failure.

        Input is ``[0, 99]``.  Predicate returns false for 0 and
        traps for any other value.  If array_all short-circuits on
        the first false (correct behaviour), 0 fails and 99 is
        never visited.  A non-short-circuiting implementation
        would visit 99, hit the assert, and trap.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [0, 99];
  let @Bool = array_all(
    @Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) {
      if @Int.0 == 0 then { false } else { assert(false); true }
    }
  );
  if @Bool.0 then { 1 } else { 0 }
}
"""
        assert _run(src) == 0

    def test_array_any_all_empty(self) -> None:
        """Empty-array invariants: any → false, all → true (vacuous truth)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  let @Bool = array_any(@Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { true });
  let @Bool = array_all(@Array<Int>.0,
    fn(@Int -> @Bool) effects(pure) { false });
  if @Bool.1 then { 1 } else {
    if @Bool.0 then { 2 } else { 10 }
  }
}
"""
        # @Bool.1 (any) should be false (empty), @Bool.0 (all) should
        # be true (vacuous), so we hit the inner `if @Bool.0`'s then.
        assert _run(src) == 2

    def test_array_flatten(self) -> None:
        """Flatten [[1,2],[3,4],[5,6]] → [1,2,3,4,5,6]; pack as 123456."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Array<Int>> = array_map(
    array_range(0, 3),
    fn(@Int -> @Array<Int>) effects(pure) {
      array_range(@Int.0 * 2 + 1, @Int.0 * 2 + 3)
    }
  );
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        # Inner: (1,2), (3,4), (5,6).  Flatten → 1,2,3,4,5,6.  Pack
        # → 123456.
        assert _run(src) == 123456

    def test_array_flatten_with_empty_inners(self) -> None:
        """Flatten where some inner arrays are empty.  [[1,2], [], [3]] → [1,2,3]."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Build [[1,2], [], [3]] via mapi: idx 0 → [1,2], idx 1 → [], idx 2 → [3]
  let @Array<Array<Int>> = array_mapi(
    array_range(0, 3),
    fn(@Int, @Nat -> @Array<Int>) effects(pure) {
      if nat_to_int(@Nat.0) == 0 then {
        array_range(1, 3)
      } else {
        if nat_to_int(@Nat.0) == 1 then {
          array_range(0, 0)
        } else {
          array_range(3, 4)
        }
      }
    }
  );
  let @Array<Int> = array_flatten(@Array<Array<Int>>.0);
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        # Inner arrays: [1,2], [], [3].  Flattened: [1,2,3].  Packed: 123.
        assert _run(src) == 123

    def test_array_sort_by_ascending_ints(self) -> None:
        """Sort [3, 1, 2] ascending → [1, 2, 3]; pack → 123."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_concat(
    array_concat(array_range(3, 4), array_range(1, 2)),
    array_range(2, 3)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 123

    def test_array_sort_by_descending(self) -> None:
        """Sort [1, 3, 2] descending → [3, 2, 1]; pack → 321.

        Confirms the comparator's polarity is respected — flipping
        the < / > in the comparator inverts the sort order.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_concat(
    array_concat(array_range(1, 2), array_range(3, 4)),
    array_range(2, 3)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 > @Int.0 then { Less } else {
        if @Int.1 < @Int.0 then { Greater } else { Equal }
      }
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 321

    def test_array_sort_by_already_sorted(self) -> None:
        """Sorting an already-sorted array is a no-op."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_sort_by(
    array_range(1, 6),
    fn(@Int, @Int -> @Ordering) effects(pure) {
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 10 + @Int.0 }
  )
}
"""
        assert _run(src) == 12345

    def test_array_sort_by_empty(self) -> None:
        """Sorting an empty array returns an empty array (length 0)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [];
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) { Equal }
  );
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 0

    def test_array_sort_by_singleton(self) -> None:
        """Sorting a single-element array returns that element unchanged."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(42, 43);
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) { Equal }
  );
  array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 }
  )
}
"""
        assert _run(src) == 42

    def test_array_sort_by_strings(self) -> None:
        """sort_by on Array<String> exercises the pair-T GC rooting branch.

        ``String`` is a pair-typed element (i32 ptr + i32 len, 8 bytes),
        so the sort's ``tmp_a`` holds a heap pointer that must be
        rooted across the comparator's ``call_indirect``.  The
        comparator allocates an ``Ordering`` box per call, which can
        trigger GC; without the shadow-stack root added in round 2,
        the String pointed at by ``tmp_a`` could be collected and the
        sort would corrupt its output.

        Comparator orders by string length here (cheap and
        deterministic) rather than lexicographically — Vera does not
        yet have a built-in string ordering, and that's a separate
        ergonomic gap.  Sort the input by length, then concatenate
        the sorted result and return the byte-length of the
        concatenation as the verifiable scalar.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = ["aaa", "b", "cc"];
  let @Array<String> = array_sort_by(
    @Array<String>.0,
    fn(@String, @String -> @Ordering) effects(pure) {
      if string_length(@String.1) < string_length(@String.0) then {
        Less
      } else {
        if string_length(@String.1) > string_length(@String.0) then {
          Greater
        } else {
          Equal
        }
      }
    }
  );
  -- Fold a length-weighted fingerprint: sum of (len * 100^position).
  -- Stable ascending [b, cc, aaa] gives 1*1 + 2*100 + 3*10000 = 30201.
  -- Any other ordering produces a different fingerprint.
  let @Int = array_fold(
    @Array<String>.0, 0,
    fn(@Int, @String -> @Int) effects(pure) {
      @Int.0 * 100 + nat_to_int(string_length(@String.0))
    }
  );
  @Int.0
}
"""
        # Sorted lengths: [1, 2, 3].  Fold reads left-to-right with
        # `acc * 100 + len`:
        #   step 1: 0 * 100 + 1 = 1
        #   step 2: 1 * 100 + 2 = 102
        #   step 3: 102 * 100 + 3 = 10203
        assert _run(src) == 10203

    def test_array_sort_by_options(self) -> None:
        """sort_by on Array<Option<Int>> exercises the ADT-T GC rooting branch.

        ``Option<Int>`` is an i32 heap handle (16-byte boxed ADT,
        not a pair).  The ``tmp`` local in the sort holds this
        handle directly; without the round-2 ADT-rooting fix
        (``t_is_adt`` / ``t_needs_root``), the option box could be
        collected during the comparator's allocation, and the sort
        would dereference garbage memory.

        Sort by extracting the inner Int (with a sentinel for None)
        and comparing those.  Verify the result via match-arm fold.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Build [Some(3), Some(1), Some(2)] via array_map for an
  -- Array<Option<Int>>.  The map output element is Option<Int>,
  -- which is an i32 heap handle (the GC-managed shape we want
  -- to exercise).
  let @Array<Int> = [3, 1, 2];
  let @Array<Option<Int>> = array_map(
    @Array<Int>.0,
    fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }
  );
  let @Array<Option<Int>> = array_sort_by(
    @Array<Option<Int>>.0,
    fn(@Option<Int>, @Option<Int> -> @Ordering) effects(pure) {
      let @Int = match @Option<Int>.1 {
        Some(@Int) -> @Int.0,
        None -> 0
      };
      let @Int = match @Option<Int>.0 {
        Some(@Int) -> @Int.0,
        None -> 0
      };
      if @Int.1 < @Int.0 then { Less } else {
        if @Int.1 > @Int.0 then { Greater } else { Equal }
      }
    }
  );
  -- Fold: extract each Some payload, digit-pack.  Sorted
  -- ascending gives [Some(1), Some(2), Some(3)] → 1, 12, 123.
  array_fold(
    @Array<Option<Int>>.0, 0,
    fn(@Int, @Option<Int> -> @Int) effects(pure) {
      let @Int = match @Option<Int>.0 {
        Some(@Int) -> @Int.0,
        None -> 0
      };
      @Int.1 * 10 + @Int.0
    }
  )
}
"""
        assert _run(src) == 123

    def test_array_sort_by_stability(self) -> None:
        """Equal-keyed elements preserve their original relative order.

        Encode each element as ``key * 10 + payload`` where keys are
        duplicated (10, 10, 20, 20, 10) and payloads are the original
        indices (0, 1, 2, 3, 4).  Sort by key only — the comparator
        inspects just the key digit (x / 10).  A stable sort keeps
        equal-keyed elements in input order:

          input:     [100, 101, 202, 203, 104]  (key*10 + pos)
          sort-key:  [ 10,  10,  20,  20,  10]
          stable:    [100, 101, 104, 202, 203]  (payloads 0, 1, 4, 2, 3)
          unstable:  equal elements may shuffle (e.g. payloads 1, 0, 4)

        Digit-pack the result to nail the exact order — 100, 101,
        104 first (the 10-keyed group in original order), then 202,
        203 (the 20-keyed group in original order).
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  -- Input: [100, 101, 202, 203, 104]
  let @Array<Int> = array_concat(
    array_concat(
      array_concat(
        array_concat(array_range(100, 101), array_range(101, 102)),
        array_range(202, 203)
      ),
      array_range(203, 204)
    ),
    array_range(104, 105)
  );
  let @Array<Int> = array_sort_by(
    @Array<Int>.0,
    fn(@Int, @Int -> @Ordering) effects(pure) {
      -- Compare on key = elem / 10 only.  Payload = elem % 10 is
      -- deliberately ignored so equal-keyed elements carry no
      -- ordering signal through the comparator.
      if @Int.1 / 10 < @Int.0 / 10 then { Less } else {
        if @Int.1 / 10 > @Int.0 / 10 then { Greater } else { Equal }
      }
    }
  );
  -- Fold to a fingerprint: multiply by 1000 per step so the
  -- digits don't overlap.  Stable order [100,101,104,202,203]
  -- yields 100 then 100*1000+101=100101 then 100101*1000+104=...
  -- which gets unwieldy; use sum-of-squares instead — any
  -- transposition of adjacent equals would change at least one
  -- squared term, but sum-of-squares is order-invariant.  So
  -- use a position-weighted sum instead: fold with index.
  let @Int = array_fold(
    @Array<Int>.0, 0,
    fn(@Int, @Int -> @Int) effects(pure) { @Int.1 * 1000 + @Int.0 }
  );
  @Int.0
}
"""
        # Stable output:    [100, 101, 104, 202, 203]
        # Position-weighted: ((((0*1000+100)*1000+101)*1000+104)*1000+202)*1000+203
        #                    = (100*1e3 + 101) = 100101
        #                    * 1000 + 104       = 100101104
        #                    * 1000 + 202       = 100101104202
        #                    * 1000 + 203       = 100101104202203
        assert _run(src) == 100101104202203
