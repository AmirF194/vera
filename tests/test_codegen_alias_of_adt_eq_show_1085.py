"""Tests for #1085 / #1086 / #1087 — the alias-of-ADT / forall-Eq / bare-Future
dispatch cluster (siblings of the #1076/#1077 ground-spelling family).

Three same-family holes in the ``==`` / forall-Eq-gate / ``show`` machinery, all
reducing to "a type name reached a dispatch spelled other than as its ground
type" — but at ENTRY POINTS the #1076/#1077 pass did not touch:

**#1085 — silent wrong `==` over an alias of a WHOLE ADT.**  ``type MyBox =
Box<Int>;`` then ``@MyBox.0 == @MyBox.1``: the operand reaches the ``==``
dispatch as the bare alias name ``MyBox``, absent from ``_adt_type_names``, so
the structural path was skipped and ``==`` fell to the scalar POINTER compare —
two structurally equal, distinct-pointer values compared unequal (0) on a
check-green program.  #1076 grounded type ARGUMENTS (``Box<MyInt>``); this
grounds the whole OPERAND (``_canonical_field_type`` at the dispatch site, so
``MyBox`` → ``Box<Int>`` and ``lv_base`` → ``Box``).

**#1086 — wrong-loud E613 for a forall<T where Eq<T>> at an Eq alias.**
``same(mk(), mk())`` where the argument is ``@Box<MyInt>`` (``type MyInt =
Int;``) was rejected with E613 "Type 'MyInt' does not satisfy ability 'Eq'":
the monomorphizer's top-level constraint gate (``_check_constraints``) tested
``concrete in type_set`` (primitive) then ``_adt_satisfies_eq`` (registered ADT
layout) — an alias name is NEITHER, so the legal program was rejected.  The
gate now grounds via the shared ``_type_eq_derivable`` oracle (which the ``$eq``
generator's field resolution mirrors — the #732 differential), so an Eq alias
is accepted and a genuinely non-Eq alias (``type BadArr = Array<Int>;``) still
E613s.

**#1087 — loud show/hash miss on a bare / aliased Future value.**  ``show(@FI.0)``
(``type FI = Future<Int>;``) and ``show(@Future<Int>.0)`` loud-skipped the
enclosing function (E602): the argument's inferred type reached the top-level
show/hash dispatch as ``FI`` / ``Future<Int>``, matched no primitive / Unit /
composite arm, and abandoned the render.  #1077 covered aliased-UNIT spellings;
this is the non-Unit bare-Future sibling.  ``_translate_show`` /
``_translate_hash`` now ground the inferred type (``_canonical_field_type``
peels the transparent wrapper to its payload — ``FI`` → ``Int``), so the render
dispatches exactly as the literal payload would.
"""
from __future__ import annotations

from tests.codegen_helpers import (
    _compile,
    _run,
)


def _warnings(source: str) -> list[str]:
    """Warning codes emitted compiling *source* (severity == 'warning')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "warning"]


def _errors(source: str) -> list[str]:
    """Error codes emitted compiling *source* (severity == 'error')."""
    result = _compile(source)
    return [d.error_code for d in result.diagnostics if d.severity == "error"]


# =====================================================================
# #1085 — structural Eq over an alias of a WHOLE ADT.  Equal pairs were
# silently 0 (pointer compare); distinct pairs must STAY 0 through the
# structural path (soundness, not always-true).
# =====================================================================

def _eq_alias_adt(alias_decl: str, ty: str, pay_a: str, pay_b: str) -> str:
    """Two ``@{ty}`` slots (``ty`` an alias of a whole ADT) compared by ``==``."""
    return f"""\
data Box<T> {{ MkB(Int, T, Int) }}
{alias_decl}

private fn a(-> @{ty})
  requires(true) ensures(true) effects(pure)
{{ MkB(11, {pay_a}, 22) }}

private fn b(-> @{ty})
  requires(true) ensures(true) effects(pure)
{{ MkB(11, {pay_b}, 22) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{
  let @{ty} = a();
  let @{ty} = b();
  @{ty}.0 == @{ty}.1
}}
"""


def test_eq_alias_of_generic_adt_equal() -> None:
    """`type MyBox = Box<Int>;`: two equal `@MyBox` compare EQUAL (structural,
    not the pointer compare of two distinct allocations)."""
    assert _run(
        _eq_alias_adt("type MyBox = Box<Int>;", "MyBox", "7", "7"), fn="f",
    ) == 1


def test_eq_alias_of_generic_adt_distinct() -> None:
    assert _run(
        _eq_alias_adt("type MyBox = Box<Int>;", "MyBox", "7", "9"), fn="f",
    ) == 0


def test_eq_alias_of_generic_adt_equal_above_2_32() -> None:
    """Payloads above 2^32 compare equal — the field is compared at i64 width."""
    assert _run(
        _eq_alias_adt(
            "type MyBox = Box<Int>;", "MyBox", "4294967303", "4294967303",
        ),
        fn="f",
    ) == 1


def test_eq_alias_of_generic_adt_distinct_above_2_32_low_bits_collide() -> None:
    """4294967303 (2^32 + 7) vs 7: distinct at i64 width but identical low 32
    bits — an i32-width compare would wrongly report equal."""
    assert _run(
        _eq_alias_adt("type MyBox = Box<Int>;", "MyBox", "4294967303", "7"),
        fn="f",
    ) == 0


def test_eq_alias_of_generic_adt_string_content() -> None:
    """`type MyBoxS = Box<String>;`: the string field dispatches to the CONTENT
    comparison — two separately built equal strings compare equal."""
    assert _run(
        _eq_alias_adt(
            "type MyBoxS = Box<String>;", "MyBoxS",
            'string_concat("he", "llo")', 'string_concat("hel", "lo")',
        ),
        fn="f",
    ) == 1


def test_eq_alias_of_generic_adt_string_distinct() -> None:
    assert _run(
        _eq_alias_adt(
            "type MyBoxS = Box<String>;", "MyBoxS",
            'string_concat("he", "llo")', 'string_concat("wor", "ld")',
        ),
        fn="f",
    ) == 0


def test_eq_alias_chain_of_generic_adt_equal() -> None:
    """`type MyBox = Box<Int>; type MyBox2 = MyBox;`: an alias CHAIN to a whole
    ADT grounds hop by hop and compares structurally."""
    assert _run(
        _eq_alias_adt(
            "type MyBox = Box<Int>;\ntype MyBox2 = MyBox;",
            "MyBox2", "7", "7",
        ),
        fn="f",
    ) == 1


def test_eq_alias_chain_of_generic_adt_distinct() -> None:
    assert _run(
        _eq_alias_adt(
            "type MyBox = Box<Int>;\ntype MyBox2 = MyBox;",
            "MyBox2", "7", "9",
        ),
        fn="f",
    ) == 0


_EQ_ALIAS_NON_GENERIC = """\
data P { MkP(Int, Int) }
type PA = P;

private fn a(-> @PA)
  requires(true) ensures(true) effects(pure)
{ MkP(11, 22) }

private fn b(-> @PA)
  requires(true) ensures(true) effects(pure)
{ MkP(11, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @PA = a();
  let @PA = b();
  @PA.0 == @PA.1
}
"""


def test_eq_alias_of_non_generic_adt_equal() -> None:
    """`type PA = P;` (alias of a NON-generic ADT): still routes structurally."""
    assert _run(_EQ_ALIAS_NON_GENERIC, fn="f") == 1


_EQ_ALIAS_NON_GENERIC_DISTINCT = """\
data P { MkP(Int, Int) }
type PA = P;

private fn mk(@Int -> @PA)
  requires(true) ensures(true) effects(pure)
{ MkP(@Int.0, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @PA = mk(11);
  let @PA = mk(99);
  @PA.0 == @PA.1
}
"""


def test_eq_alias_of_non_generic_adt_distinct() -> None:
    assert _run(_EQ_ALIAS_NON_GENERIC_DISTINCT, fn="f") == 0


# -- #1085 controls: the direct (un-aliased) spelling was already structural.

_EQ_DIRECT_CONTROL = """\
data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

private fn b(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 7, 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = a();
  let @Box<Int> = b();
  @Box<Int>.0 == @Box<Int>.1
}
"""


def test_control_eq_direct_box_int() -> None:
    """The un-aliased `@Box<Int>` compare was already structural (pins that the
    alias path now agrees with the direct path)."""
    assert _run(_EQ_DIRECT_CONTROL, fn="f") == 1


# =====================================================================
# #1086 — forall<T where Eq<T>> instantiated at an Eq alias.  The
# top-level constraint gate rejected a legal program with E613.
# =====================================================================

def _forall_eq_alias(alias_decl: str, arg: str, pay_a: str, pay_b: str) -> str:
    """`same(a(), b())` with `same : forall<T where Eq<T>>`, T inferred to the
    alias `arg` from a `@Box<arg>` argument."""
    return f"""\
data Box<T> {{ MkB(T) }}
{alias_decl}

forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{{ @Box<T>.1 == @Box<T>.0 }}

private fn a(-> @Box<{arg}>)
  requires(true) ensures(true) effects(pure)
{{ MkB({pay_a}) }}

private fn b(-> @Box<{arg}>)
  requires(true) ensures(true) effects(pure)
{{ MkB({pay_b}) }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{ same(a(), b()) }}
"""


def test_forall_eq_alias_int_equal() -> None:
    """T := MyInt (`type MyInt = Int;`): the gate accepts and the equal values
    compare EQUAL (was a wrong-loud E613)."""
    src = _forall_eq_alias("type MyInt = Int;", "MyInt", "7", "7")
    assert "E613" not in _errors(src)
    assert _run(src, fn="f") == 1


def test_forall_eq_alias_int_distinct() -> None:
    """Distinct payloads compare UNEQUAL through the structural path (the fix
    must not make the compare always-true)."""
    assert _run(
        _forall_eq_alias("type MyInt = Int;", "MyInt", "7", "9"), fn="f",
    ) == 0


def test_forall_eq_alias_int_equal_above_2_32() -> None:
    assert _run(
        _forall_eq_alias(
            "type MyInt = Int;", "MyInt", "4294967303", "4294967303",
        ),
        fn="f",
    ) == 1


def test_forall_eq_alias_int_distinct_above_2_32_low_bits_collide() -> None:
    assert _run(
        _forall_eq_alias("type MyInt = Int;", "MyInt", "4294967303", "7"),
        fn="f",
    ) == 0


def test_forall_eq_alias_future_int_equal() -> None:
    """T := FI (`type FI = Future<Int>;`): a transparent-Future alias is Eq
    (grounds to Int); equal payloads compare equal."""
    src = _forall_eq_alias("type FI = Future<Int>;", "FI", "async(5)", "async(5)")
    assert "E613" not in _errors(src)
    assert _run(src, fn="f") == 1


def test_forall_eq_alias_future_int_distinct() -> None:
    assert _run(
        _forall_eq_alias(
            "type FI = Future<Int>;", "FI", "async(5)", "async(9)",
        ),
        fn="f",
    ) == 0


def test_forall_eq_alias_of_whole_adt_equal() -> None:
    """T := MyPair (`type MyPair = Pair;`, a whole-ADT alias): the gate grounds
    it to the registered ADT and derives Eq structurally."""
    src = """\
data Pair { MkPair(Int, Int) }
data Box<T> { MkB(T) }
type MyPair = Pair;

forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Box<T>.1 == @Box<T>.0 }

private fn a(-> @Box<MyPair>)
  requires(true) ensures(true) effects(pure)
{ MkB(MkPair(1, 2)) }

private fn b(-> @Box<MyPair>)
  requires(true) ensures(true) effects(pure)
{ MkB(MkPair(1, 2)) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ same(a(), b()) }
"""
    assert "E613" not in _errors(src)
    assert _run(src, fn="f") == 1


# -- #1086 differential lockstep: the gate must ACCEPT an Eq alias (compiles
# -- cleanly) and REJECT a genuinely non-Eq alias (E613, and never the codegen
# -- E699 invariant — the two sides agree).  Keeps `_type_eq_derivable` in
# -- lockstep with the `$eq` generator (the #732 invariant) at THIS entry point.

_FORALL_EQ_NON_EQ_ALIAS = """\
data Box<T> { MkB(T) }
type BadArr = Array<Int>;

forall<T where Eq<T>>
fn same(@Box<T>, @Box<T> -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Box<T>.1 == @Box<T>.0 }

private fn a(-> @Box<BadArr>)
  requires(true) ensures(true) effects(pure)
{ MkB([1]) }

private fn b(-> @Box<BadArr>)
  requires(true) ensures(true) effects(pure)
{ MkB([1]) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ same(a(), b()) }
"""


def test_forall_eq_non_eq_alias_still_rejected() -> None:
    """`type BadArr = Array<Int>;` grounds to a non-Eq type — the gate still
    raises E613 (never weakened) and codegen never hits its E699 invariant
    (the gate rejects first; the two sides stay in lockstep)."""
    codes = _errors(_FORALL_EQ_NON_EQ_ALIAS)
    assert "E613" in codes
    assert "E699" not in codes


# =====================================================================
# #1087 — show / hash of a bare or aliased Future value.  All loud-skipped
# (E602), never a wrong value.
# =====================================================================

def _show_future(alias_decl: str, ty: str, pay: str, expected: str) -> str:
    return f"""\
{alias_decl}
private fn mkf(-> @{ty})
  requires(true) ensures(true) effects(pure)
{{ {pay} }}

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{{
  let @{ty} = mkf();
  eq(show(@{ty}.0), "{expected}")
}}
"""


def test_show_aliased_future_int() -> None:
    """show(@FI.0) (`type FI = Future<Int>;`) renders the payload "5" — the
    alias grounds and the transparent wrapper peels to Int."""
    src = _show_future("type FI = Future<Int>;", "FI", "async(5)", "5")
    assert _run(src, fn="f") == 1
    assert "E602" not in _warnings(src)


def test_show_bare_future_int() -> None:
    """show(@Future<Int>.0) renders "5" — the transparent wrapper peels to its
    payload at the top-level show dispatch."""
    src = _show_future("", "Future<Int>", "async(5)", "5")
    assert _run(src, fn="f") == 1
    assert "E602" not in _warnings(src)


def test_show_aliased_future_bool() -> None:
    """show(@FB.0) (`type FB = Future<Bool>;`) renders the Bool payload."""
    src = _show_future("type FB = Future<Bool>;", "FB", "async(true)", "true")
    assert _run(src, fn="f") == 1
    assert "E602" not in _warnings(src)


_HASH_FUTURE_EQUAL = """\
type FI = Future<Int>;

private fn mkf(@Int -> @FI)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf(5);
  let @FI = mkf(5);
  hash(@FI.0) == hash(@FI.1)
}
"""


def test_hash_aliased_future_equal_payload() -> None:
    """hash(@FI.0) folds the peeled payload — equal payloads hash equal."""
    assert _run(_HASH_FUTURE_EQUAL, fn="f") == 1
    assert "E602" not in _warnings(_HASH_FUTURE_EQUAL)


_HASH_FUTURE_DISTINCT = """\
type FI = Future<Int>;

private fn mkf(@Int -> @FI)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @FI = mkf(4294967303);
  let @FI = mkf(7);
  hash(@FI.0) == hash(@FI.1)
}
"""


def test_hash_aliased_future_distinct_payload_i64() -> None:
    """Distinct payloads (2^32+7 vs 7, colliding low 32 bits) hash distinctly —
    the payload is folded at i64 width, not truncated to the pointer word."""
    assert _run(_HASH_FUTURE_DISTINCT, fn="f") == 0


_HASH_BARE_FUTURE = """\
private fn mkf(@Int -> @Future<Int>)
  requires(true) ensures(true) effects(pure)
{ async(@Int.0) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Future<Int> = mkf(5);
  let @Future<Int> = mkf(5);
  hash(@Future<Int>.0) == hash(@Future<Int>.1)
}
"""


def test_hash_bare_future_equal_payload() -> None:
    assert _run(_HASH_BARE_FUTURE, fn="f") == 1
    assert "E602" not in _warnings(_HASH_BARE_FUTURE)


# -- #1087 control: show of a plain Int (the ground payload) already worked.

_SHOW_INT_CONTROL = """\
private fn mki(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(show(mki()), "5") }
"""


def test_control_show_plain_int() -> None:
    assert _run(_SHOW_INT_CONTROL, fn="f") == 1
