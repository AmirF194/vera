"""Regression tests for #1056 — a fn-typed slot handed to ``array_map`` /
``array_mapi`` as the closure argument.

Before #1056 the map-call emission inferred the output element type only
from an inline ``AnonFn`` literal, so a fn-typed slot reference
(``@Mapper.0`` where ``type Mapper = fn(A -> B)``) E602-dropped with
"could not infer array_map closure return type" — even though
``apply_fn`` over the identical slot resolved fine.  The fix routes the
element-type inference through the same ``_closure_arg_return_type``
resolver ``apply_fn`` uses, so a fn-typed slot's return type is recovered
from its ``FnType`` alias signature and the ``call_indirect`` is emitted
exactly as for an inline ``AnonFn``.

Each mapper adds a constant (or changes type) so the asserted value cannot
coincide with the input element or a zero/identity fallback.
"""
from __future__ import annotations

from tests.codegen_helpers import _run


class TestArrayMapSlotClosure:
    def test_array_map_letbound_fn_slot_closure(self) -> None:
        """The canonical #1056 repro: a let-bound ``Mapper`` slot handed
        to ``array_map``.  ``[1,2,3]`` mapped by ``+100`` is
        ``[101,102,103]``; element ``[1]`` is 102."""
        src = """
type Mapper = fn(Int -> Int) effects(pure);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Mapper = fn(@Int -> @Int) effects(pure) { @Int.0 + 100 };
  let @Array<Int> = array_map([1, 2, 3], @Mapper.0);
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 102

    def test_array_map_param_fn_slot_closure(self) -> None:
        """The fn-typed slot arrives as a function *parameter* (not a
        ``let``), exercising the SlotRef-to-parameter path.  Before the
        fix ``run_map``'s body dropped, so ``main``'s call resolved to a
        WAT function that was never emitted; after the fix it returns
        102."""
        src = """
type Mapper = fn(Int -> Int) effects(pure);

private fn run_map(@Mapper -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map([1, 2, 3], @Mapper.0);
  @Array<Int>.0[1]
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  run_map(fn(@Int -> @Int) effects(pure) { @Int.0 + 100 })
}
"""
        assert _run(src) == 102

    def test_array_map_type_changing_slot_closure(self) -> None:
        """A type-changing ``Int -> String`` mapper slot: the output
        element type must be resolved from the slot's ``FnType`` return
        (``String``), not the input element type (``Int``).  ``[1,20,300]``
        maps to ``["1","20","300"]``; ``string_length`` of element ``[2]``
        (``"300"``) is 3."""
        src = """
type SMapper = fn(Int -> String) effects(pure);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @SMapper = fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) };
  let @Array<String> = array_map([1, 20, 300], @SMapper.0);
  string_length(@Array<String>.0[2])
}
"""
        assert _run(src) == 3

    def test_array_mapi_fn_slot_closure(self) -> None:
        """``array_mapi`` shares the same closure-return inference, so a
        fn-typed slot works there too.  ``array_mapi([10,20,30], |x,i| x+i)``
        gives ``[10,21,32]``; element ``[2]`` is 32."""
        src = """
type IdxMapper = fn(Int, Int -> Int) effects(pure);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @IdxMapper = fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  let @Array<Int> = array_mapi([10, 20, 30], @IdxMapper.0);
  @Array<Int>.0[2]
}
"""
        assert _run(src) == 32

    def test_apply_fn_slot_closure_parity(self) -> None:
        """Parity pin: ``apply_fn`` over the identical fn-typed slot
        already resolved before #1056 (it routes through the same
        ``_closure_arg_return_type``).  Green pre- and post-fix — this
        documents the parity ``array_map`` now matches, and guards the
        shared resolver from regressing.  ``apply_fn(+100, 5)`` is 105."""
        src = """
type Mapper = fn(Int -> Int) effects(pure);

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Mapper = fn(@Int -> @Int) effects(pure) { @Int.0 + 100 };
  apply_fn(@Mapper.0, 5)
}
"""
        assert _run(src) == 105

    def test_array_map_inline_anon_fn_control(self) -> None:
        """Control: an inline ``AnonFn`` closure argument already worked
        and must keep working — the #1056 fix reroutes the ``AnonFn`` arm
        through ``_closure_arg_return_type`` (which returns the same
        declared ``return_type``), so this guards that refactor.  Green
        pre- and post-fix; element ``[1]`` of ``[101,102,103]`` is 102."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_map(
    [1, 2, 3],
    fn(@Int -> @Int) effects(pure) { @Int.0 + 100 }
  );
  @Array<Int>.0[1]
}
"""
        assert _run(src) == 102
