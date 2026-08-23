"""#1310: a qualified-only (shadowed) module generic's instantiation
discovery had no effect-operation registry at all, unlike the unshadowed
discovery walk #1207 already fixed.

``_monomorphize_shadowed_module_generics`` seeds a shadowed generic's
instances from ``ast.ModuleCall`` sites inside a module's own bodies via
``_collect_shadowed_qualified_calls`` (codegen) and the mirroring
``walk_seed`` closure (the verifier's ``_collect_shadowed_qualified_instances``,
#732).  Neither ever installed the ``handle[State<T>]`` op-result registry
``Monomorphizer._collect_calls`` merges in for the unshadowed path, so an
argument like ``get(())`` fell through to the phantom-type-variable ``Bool``
default. The WASM call-site rewrite (``CallsMixin._resolve_generic_call``),
which runs with the real handler context during actual codegen, still named
the correct clone (``mod$mlib5$idg$Int``), so discovery silently emitted a
clone nothing calls, the real one was never registered, and the caller
(``outer``, then ``main``) was dropped with E602/E620 on check-green,
verify-clean source.

Two cells:

* the issue's own repro, a private module generic instantiated from an
  effect-operation result, pinned end to end (no E602/E620, the checker's
  own clone name in the WAT, and the runtime value); and
* a nested-distinct-state variant (mirroring
  ``test_mono_effect_op_naming_1207.py``'s ``_NESTED_DISTINCT_STATE``) through
  the SAME shadowed path, so a fix that merely stops defaulting to ``Bool``
  without preserving merge-not-replace semantics for nested handlers is
  still caught: it would name the inner call from the OUTER cell and sum to
  the wrong value.
"""

from __future__ import annotations

from tests.codegen_helpers import wat_fn_names
from tests.module_fixture_helpers import build_multi_module, module_value

_MLIB5 = """\
module mlib5;

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public forall<T> fn outer(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    idg(get(()))
  }
}
"""

_MAIN5 = """\
import mlib5(outer);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer(1)
}
"""

_MLIB6 = """\
module mlib6;

private forall<T> fn idg2(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn outer2(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 2) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    nat_to_int(get(())) + handle[State<Int>](@Int = 5) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      idg2(get(()))
    }
  }
}
"""

_MAIN6 = """\
import mlib6(outer2);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer2(())
}
"""


def test_module_generic_instantiated_from_effect_op_result(tmp_path) -> None:
    """The issue's own repro: check/verify clean, ``idg$Int`` emitted, runs 42007."""
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib5.vera": _MLIB5, "main.vera": _MAIN5},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    names = wat_fn_names(result.wat)
    assert "mod$mlib5$idg$Int" in names, (
        "discovery and the call-rewrite named different clones for the "
        f"module generic; emitted: {names}"
    )
    assert "mod$mlib5$idg$Bool" not in names, (
        "the effect-op-result argument was still defaulted to the phantom "
        f"Bool type variable; emitted: {names}"
    )
    assert module_value(result) == ("ok", 42007)


def test_shadowed_generic_op_registry_merges_not_replaces(tmp_path) -> None:
    """A nested handler must still let the OUTER cell answer outside itself.

    ``idg2(get(()))`` in the INNER ``handle[State<Int>]`` body must bind
    ``@T`` from the inner cell (5), while ``get(())`` OUTSIDE it (but still
    inside the outer ``handle[State<Nat>]``) reads the outer cell (2), for
    2 + 5 = 7.  A discovery walk that REPLACED the registry instead of
    merging it over the enclosing one would still pass the first cell above
    (there is only one handler in it) but would get this one wrong: either
    a WAT type mismatch (Nat vs Int have different reprs) or a silently
    wrong sum if `_op_result_types` from the wrong handler leaked across
    the boundary the two calls actually sit in.
    """
    verify_errors, result, cg_errors = build_multi_module(
        tmp_path, {"mlib6.vera": _MLIB6, "main.vera": _MAIN6},
    )
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    names = wat_fn_names(result.wat)
    assert "mod$mlib6$idg2$Int" in names, (
        f"expected the inner cell's clone in the emitted WAT; got {names}"
    )
    assert module_value(result) == ("ok", 7)
