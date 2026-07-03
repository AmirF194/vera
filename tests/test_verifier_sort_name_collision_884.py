"""Regression: injective Z3 datatype sort names (#884).

Before #884 the verifier named Z3 datatype sorts with the old lossy sanitize
(``key.replace("<", "_").replace(">", "").replace(", ", "_")``), so two distinct
Vera types could collide on one Z3 sort name — ``Box<Int>`` and a flat ADT
literally named ``Box_Int`` both became the Z3 name ``Box_Int``.  Z3's
per-context datatype cache conflates same-named sorts (the last ``create()``
wins and earlier same-named sorts silently adopt its structure), so
``Box<Int>``'s sort acquired the flat ADT's ``MkBoxInt(Bool)`` constructor.  The
manifestation was a **false counterexample**: a trivially-true ``ensures`` was
rejected with ``@Box<Int>.0 = MkBoxInt(False)`` — the flat ADT's Bool ctor
witnessing a ``Box<Int>`` slot.

The fix routes both Z3 sort-name sites (``_get_or_create_adt_sort`` and
``_get_or_create_tuple_sort`` in ``vera/smt.py``) through the injective #775
``mangle_type_name`` mangler, so distinct type keys can never share a Z3 sort
name.  **Both sites are independently pinned** — one collision per site — so
neither ``mangle_type_name`` call can be reverted without flipping a test:

* **ADT site** (``_get_or_create_adt_sort``): the ``Box<Int>`` / flat
  ``Box_Int`` collision.  Reverting *this* site to the lossy sanitize
  re-collides the sorts and flips the three ``_COLLISION``-based tests
  (:func:`test_sort_name_collision_verifies_clean`,
  :func:`test_collision_counterexample_uses_correct_constructor`, and
  :func:`test_false_ensures_over_colliding_pair_still_disproved`) back to the
  false E500 — the false-prove probe flips too because the disproof then names
  the wrong (flat) constructor.
* **Tuple site** (``_get_or_create_tuple_sort``): the
  ``Tuple<Tuple<Int>, Int>`` / ``Tuple<Tuple<Int, Int>>`` collision.  Both keys
  lossy-sanitize to ``Tuple_Tuple_Int_Int``; the two synthesised tuple sorts
  then share one Z3 datatype, and a match arm projecting a field index the
  conflated sort does not carry raises
  ``z3.z3types.Z3Exception: Invalid accessor index`` at ``sort.accessor``
  (during ``_bind_pattern``).  Reverting *this* site to the lossy sanitize
  flips :func:`test_tuple_sort_name_collision_verifies_clean`.

The false-prove direction is probed too: a genuinely-false ``ensures`` over the
same colliding pair must still be disproved (the conflation only *freed* field
constraints, so it produced conservative false negatives — the fix must not
introduce a false PROVE either).
"""
from __future__ import annotations

from tests.verifier_helpers import _verify, _verify_ok, _verify_err


# The colliding pair: a monomorphized generic `Box<Int>` and a flat ADT whose
# name sanitizes to the same lossy Z3 name.  `bool_val` forces the flat ADT's
# sort to be constructed too, so the last-create()-wins cache conflation fires.
_COLLISION = """
public data Box<T> { MkBox(T) }
public data Box_Int { MkBoxInt(Bool) }

public fn box_val(@Box<Int> -> @Int)
  requires(true)
  ensures(match @Box<Int>.0 { MkBox(@Int) -> @Int.result == @Int.0 })
  effects(pure)
{
  match @Box<Int>.0 { MkBox(@Int) -> @Int.0 }
}

public fn bool_val(@Box_Int -> @Bool)
  requires(true)
  ensures(match @Box_Int.0 { MkBoxInt(@Bool) -> @Bool.result == @Bool.0 })
  effects(pure)
{
  match @Box_Int.0 { MkBoxInt(@Bool) -> @Bool.0 }
}

public fn identity_true(@Box<Int>, @Box_Int -> @Int)
  requires(true)
  ensures(@Int.result == box_val(@Box<Int>.0))
  effects(pure)
{
  let @Bool = bool_val(@Box_Int.0);
  box_val(@Box<Int>.0)
}
"""


# Byte-identical control with the flat ADT renamed so no lossy-name collision
# exists — this verified 6-Tier-1 clean even before the fix.  It pins that the
# fix does not regress the non-colliding case.
_CONTROL = _COLLISION.replace("Box_Int", "BoxIntFlat").replace(
    "MkBoxInt", "MkBoxIntFlat"
)


# The false-prove probe: `identity_false` returns `box_val(...)` but claims the
# result is `box_val(...) + 1`.  Genuinely false; must still be disproved (and
# for the right reason — the sorts are no longer conflated).
_FALSE = """
public data Box<T> { MkBox(T) }
public data Box_Int { MkBoxInt(Bool) }

public fn box_val(@Box<Int> -> @Int)
  requires(true)
  ensures(match @Box<Int>.0 { MkBox(@Int) -> @Int.result == @Int.0 })
  effects(pure)
{
  match @Box<Int>.0 { MkBox(@Int) -> @Int.0 }
}

public fn identity_false(@Box<Int>, @Box_Int -> @Int)
  requires(true)
  ensures(@Int.result == box_val(@Box<Int>.0) + 1)
  effects(pure)
{
  box_val(@Box<Int>.0)
}
"""


# The tuple-site collision, pinning `_get_or_create_tuple_sort` (the second
# `mangle_type_name` site).  Both `Tuple<Tuple<Int>, Int>` (outer arity 2, inner
# arity 1) and `Tuple<Tuple<Int, Int>>` (outer arity 1, inner arity 2)
# lossy-sanitize to the single Z3 name `Tuple_Tuple_Int_Int`, so under the lossy
# sanitize the two synthesised tuple sorts share one Z3 datatype.  A match arm
# projecting a field index the conflated sort does not carry raises
# `z3.z3types.Z3Exception: Invalid accessor index` at `sort.accessor` — the fix
# gives each tuple key an injective Z3 name (`Tuple_LTuple_LInt_R_CInt_R` vs
# `Tuple_LTuple_LInt_CInt_R_R`) so the sorts stay distinct and it verifies.
_TUPLE_COLLISION = """
public fn a_fst(@Tuple<Tuple<Int>, Int> -> @Int)
  requires(true)
  ensures(match @Tuple<Tuple<Int>, Int>.0 { Tuple(@Tuple<Int>, @Int) -> @Int.result == @Int.0 })
  effects(pure)
{ match @Tuple<Tuple<Int>, Int>.0 { Tuple(@Tuple<Int>, @Int) -> @Int.0 } }

public fn b_inner_sum(@Tuple<Tuple<Int, Int>> -> @Int)
  requires(true) ensures(true) effects(pure)
{ match @Tuple<Tuple<Int, Int>>.0 { Tuple(@Tuple<Int, Int>) -> match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 + @Int.1 } } }

public fn identity_true(@Tuple<Tuple<Int>, Int>, @Tuple<Tuple<Int, Int>> -> @Int)
  requires(true) ensures(@Int.result == a_fst(@Tuple<Tuple<Int>, Int>.0)) effects(pure)
{ let @Int = b_inner_sum(@Tuple<Tuple<Int, Int>>.0); a_fst(@Tuple<Tuple<Int>, Int>.0) }
"""


def test_sort_name_collision_verifies_clean() -> None:
    """The trivially-true `ensures` must verify — no false E500.

    RED on main: E500 with counterexample `@Box<Int>.0 = MkBoxInt(False)`.
    Mutation oracle: reverting a `mangle_type_name` site to the lossy sanitize
    re-collides the sorts and flips this back to the false E500.
    """
    _verify_ok(_COLLISION)


def test_rename_control_stays_clean() -> None:
    """The non-colliding rename-control keeps verifying (no regression)."""
    _verify_ok(_CONTROL)


def test_collision_counterexample_uses_correct_constructor() -> None:
    """Pin the mechanism: no `Box<Int>` slot is ever witnessed by the flat
    ADT's `MkBoxInt` constructor.

    On main the false counterexample names `@Box<Int>.0 = MkBoxInt(False)` —
    a `Box<Int>` value built from the flat ADT's Bool constructor, the direct
    fingerprint of the sort conflation.  After the fix the program verifies, so
    there is no counterexample text mentioning the cross-type constructor at
    all.
    """
    result = _verify(_COLLISION)
    text = "\n".join(d.description for d in result.diagnostics)
    assert "@Box<Int>.0 = MkBoxInt" not in text, (
        "A `Box<Int>` obligation is still being witnessed by the flat ADT's "
        f"MkBoxInt constructor — sorts remain conflated. Diagnostics:\n{text}"
    )


def test_false_ensures_over_colliding_pair_still_disproved() -> None:
    """Soundness probe: a genuinely-false `ensures` over the colliding pair is
    still rejected (the fix must not introduce a false PROVE)."""
    errors = _verify_err(_FALSE, "does not hold")
    # And for the RIGHT reason: the `@Box<Int>` slot is witnessed by its own
    # constructor `MkBox`, never the flat ADT's `MkBoxInt` (the conflation
    # fingerprint).  `@Box_Int.0 = MkBoxInt(...)` is fine — that slot really is
    # a `Box_Int`; the bug is a `Box<Int>` slot wearing the flat ctor.
    ce_text = "\n".join(e.description for e in errors)
    assert "@Box<Int>.0 = MkBoxInt" not in ce_text, (
        f"A `Box<Int>` slot is witnessed by the flat ctor MkBoxInt — sorts "
        f"remain conflated:\n{ce_text}"
    )


def test_tuple_sort_name_collision_verifies_clean() -> None:
    """The tuple-site collision must verify — pins `_get_or_create_tuple_sort`.

    `Tuple<Tuple<Int>, Int>` and `Tuple<Tuple<Int, Int>>` both lossy-sanitize
    to `Tuple_Tuple_Int_Int`; under the lossy name the two synthesised tuple
    sorts share one Z3 datatype, and a match arm projecting a field index the
    conflated sort does not carry crashes the verifier with
    `z3.z3types.Z3Exception: Invalid accessor index` at `sort.accessor`.

    Mutation oracle: reverting the `_get_or_create_tuple_sort` `mangle_type_name`
    call (vera/smt.py, the second site) to the lossy sanitize re-collides the
    two tuple sorts and flips this test — the crash surfaces instead of a clean
    verify.  This is the kill that makes the tuple mangle site load-bearing
    (reverting it with only the `Box` collision test present flipped nothing).
    """
    _verify_ok(_TUPLE_COLLISION)
