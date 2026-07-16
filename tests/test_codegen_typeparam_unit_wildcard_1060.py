"""Tests for #1060 — wildcard over a type-parameter field instantiated to Unit.

A generic constructor's type-parameter field (``Box<T>`` field ``T``) registers
in the layout as the generic 4-byte i32 placeholder.  Construction, however,
lays each instantiation out concretely: ``Box<Unit>`` *erases* the field to zero
bytes, ``Box<String>`` widens it to an i32_pair, ``Box<Int>`` to an i64.  A
WILDCARD sub-pattern over such a field used to advance the offset walk by the
generic i32 width regardless — so on a ``Box<Unit>`` every field *after* the
erased one was read four bytes too high, silently, on a check-green program with
no diagnostics:

* ``match b { MkB(@Int, _, @Int) -> @Int.0 }`` on ``Box<Unit>`` returned 0, not
  the real trailing Int;
* ``N(_, @String)`` on ``Named<Unit>`` read the String header at the wrong
  offset (garbage);
* ``En(_, MkBox(@Int))`` on ``Entry<Unit>`` read the nested constructor tag at a
  shifted address and matched the wrong arm.

Only the WILDCARD walks were wrong — ``@Unit`` bindings, let-destructures, and
structural ``Eq`` / ``show`` / ``hash`` already recompute each field from the
concrete instantiation and were correct *for the literal ``Unit`` spelling*
(pinned below as regression controls).  A NON-literal erases-to-Unit type
argument (``Box<U>`` with ``type U = Unit;``, ``Box<Future<Unit>>``, chains)
hit the same class of hole in the width recomputation AND in ``Eq``'s dispatch
— that is #1070, pinned in ``test_codegen_erased_alias_typeargs_1070.py``.

The fix makes the two wildcard walks (``_extract_constructor_fields`` and
``_sub_pattern_wasm_type``) instantiation-aware: a bare type-parameter field's
width is recomputed from the scrutinee's concrete type args, mirroring the
eq/show recomputation.  A concrete field keeps its (#1043-erasure-aware)
registered width.  When the instantiation is unrecoverable (a direct-call
scrutinee whose inferred type dropped its args) AND a later field is read, the
function LOUD-skips (E602) rather than reading a wrong offset; a trailing
unrecoverable wildcard stays compilable (its unknown width is never consumed).
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
# The core silent-wrong shapes: a WILDCARD over a type-parameter field
# instantiated to Unit, followed by a field that IS read.  Each returns the
# real value only when the erased field advances the offset by 0 bytes.
# The scrutinee is a slot (`@Box<Unit>.0`) whose type args are recoverable.
# =====================================================================

_BOX_UNIT = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = mk();
  match @Box<Unit>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_box_unit_wildcard_reads_trailing_int() -> None:
    """MkB(@Int, _, @Int) on Box<Unit>: @Int.0 is the real trailing 22, not 0."""
    assert _run(_BOX_UNIT, fn="f") == 22


_BOX_UNIT_FIRST = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = mk();
  match @Box<Unit>.0 {
    MkB(@Int, _, @Int) -> @Int.1
  }
}
"""


def test_box_unit_field_before_erased_is_unaffected() -> None:
    """@Int.1 (field 0, BEFORE the erased field) was always correct — 11."""
    assert _run(_BOX_UNIT_FIRST, fn="f") == 11


_NAMED_UNIT = """\
data Named<T> { N(T, String) }

private fn mk(-> @Named<Unit>)
  requires(true) ensures(true) effects(pure)
{ N((), "payload") }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Named<Unit> = mk();
  match @Named<Unit>.0 {
    N(_, @String) -> eq(@String.0, "payload")
  }
}
"""


def test_named_unit_wildcard_reads_string_at_right_offset() -> None:
    """N(_, @String) on Named<Unit>: the String header is read @4, not @8."""
    assert _run(_NAMED_UNIT, fn="f") == 1


_ENTRY_UNIT = """\
data BB { MkBox(Int), MkNot(Int) }
data Entry<T> { En(T, BB) }

private fn mk(-> @Entry<Unit>)
  requires(true) ensures(true) effects(pure)
{ En((), MkBox(314)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Entry<Unit> = mk();
  match @Entry<Unit>.0 {
    En(_, MkBox(@Int)) -> @Int.0,
    En(_, MkNot(@Int)) -> 0 - @Int.0
  }
}
"""


def test_entry_unit_wildcard_before_nested_ctor() -> None:
    """En(_, MkBox(@Int)) on Entry<Unit>: the nested tag is read @4, hits the
    MkBox arm, and extracts the real 314 (both the condition tag-walk and the
    field-extraction walk must give the erased field zero width)."""
    assert _run(_ENTRY_UNIT, fn="f") == 314


_BOOL_FOLLOWING = """\
data Bx<T> { MkBx(T, Bool) }

private fn mk(-> @Bx<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkBx((), true) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Bx<Unit> = mk();
  match @Bx<Unit>.0 {
    MkBx(_, @Bool) -> @Bool.0
  }
}
"""


def test_bool_following_erased_typeparam() -> None:
    """A Bool (align 4) after the erased field is a RED shape — the spurious +4
    is not masked by re-alignment.  MkBx(_, @Bool) reads the real true."""
    assert _run(_BOOL_FOLLOWING, fn="f") == 1


_SECOND_TYPEPARAM = """\
data P2<A, B> { MkP2(Int, B, Int) }

private fn mk(-> @P2<Int, Unit>)
  requires(true) ensures(true) effects(pure)
{ MkP2(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @P2<Int, Unit> = mk();
  match @P2<Int, Unit>.0 {
    MkP2(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_second_type_parameter_instantiated_to_unit() -> None:
    """The erased field is the SECOND type parameter (P2<Int, Unit> field B):
    the positional tp-index lookup must resolve B, not A."""
    assert _run(_SECOND_TYPEPARAM, fn="f") == 22


_NESTED_GENERIC = """\
data Inner<T> { MkI(Int, T, Int) }
data Outer<T> { MkO(Inner<T>) }

private fn mk(-> @Outer<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkO(MkI(11, (), 22)) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Outer<Unit> = mk();
  match @Outer<Unit>.0 {
    MkO(MkI(@Int, _, @Int)) -> @Int.0
  }
}
"""


def test_nested_generic_wildcard_resolves_inner_instantiation() -> None:
    """A wildcard over Inner's type parameter one level DOWN: recursing into
    MkO's Inner<T> field must substitute the outer <Unit> so Inner<Unit>'s
    erased field advances by 0 bytes and the trailing Int is read as 22."""
    assert _run(_NESTED_GENERIC, fn="f") == 22


# =====================================================================
# Builtin Option / Result — a wildcard over the payload type parameter
# instantiated to Unit.  The payload is the last field, so nothing is read
# after it (harmless), but the arm must still match and return correctly.
# =====================================================================

_OPTION_UNIT = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Unit> = Some(());
  match @Option<Unit>.0 {
    Some(_) -> 5,
    None -> 9
  }
}
"""


def test_option_unit_some_wildcard() -> None:
    assert _run(_OPTION_UNIT, fn="f") == 5


_RESULT_UNIT = """\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<Unit, Int> = Ok(());
  match @Result<Unit, Int>.0 {
    Ok(_) -> 5,
    Err(@Int) -> @Int.0
  }
}
"""


def test_result_unit_ok_wildcard() -> None:
    assert _run(_RESULT_UNIT, fn="f") == 5


# =====================================================================
# Controls — a type-parameter wildcard whose instantiation is NOT Unit.  The
# fix must recompute these widths correctly too (String → i32_pair, Int → i64).
# Box<Int> / Box<Bool> were green even before the fix (alignment coincidence);
# they pin that the recomputation keeps them green.
# =====================================================================

_BOX_STRING = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<String>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, "x", 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<String> = mk();
  match @Box<String>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_box_string_wildcard_recomputes_i32_pair_width() -> None:
    """Box<String>: the erased-field slot is an i32_pair (8 bytes); the trailing
    Int is still read correctly."""
    assert _run(_BOX_STRING, fn="f") == 22


_BOX_INT = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, 55, 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = mk();
  match @Box<Int>.0 {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_box_int_wildcard_control() -> None:
    """Box<Int>: i64 payload; green before and after (alignment coincidence)."""
    assert _run(_BOX_INT, fn="f") == 22


_TAGGED_UNIT = """\
data Tagged<T> { Tag(T, Int) }

private fn mk(-> @Tagged<Unit>)
  requires(true) ensures(true) effects(pure)
{ Tag((), 99) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Tagged<Unit> = mk();
  match @Tagged<Unit>.0 {
    Tag(_, @Int) -> @Int.0
  }
}
"""


def test_tagged_unit_alignment_masked_control() -> None:
    """Tag(T, Int) as Tagged<Unit>: the spurious +4 is re-aligned away by the
    following i64, so this shape was CORRECT even before the fix.  Pin it green
    so the fix does not perturb the alignment-masked case."""
    assert _run(_TAGGED_UNIT, fn="f") == 99


# =====================================================================
# Trailing type-parameter wildcard — the erased field is LAST, so its width is
# never consumed.  Green whether or not the instantiation is recoverable.
# =====================================================================

_TRAILING_SLOT = """\
data W<T> { MkW(Int, T) }

private fn mk(-> @W<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkW(5, ()) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @W<Unit> = mk();
  match @W<Unit>.0 {
    MkW(@Int, _) -> @Int.0
  }
}
"""


def test_trailing_typeparam_wildcard_slot() -> None:
    assert _run(_TRAILING_SLOT, fn="f") == 5


# =====================================================================
# Recoverability boundary — a DIRECT-CALL scrutinee's inferred Vera type drops
# its type args, so a type-parameter wildcard's concrete width is unrecoverable.
# * followed by a read  → LOUD skip (E602), never a wrong read;
# * trailing (nothing read after) → still compiles (width never consumed).
# =====================================================================

_DIRECT_CALL_HARMFUL = """\
data Box<T> { MkB(Int, T, Int) }

private fn mk(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkB(@Int, _, @Int) -> @Int.0
  }
}
"""


def test_direct_call_unrecoverable_read_after_loud_skips() -> None:
    """`match mk() { MkB(@Int, _, @Int) }` — mk's return type inference drops the
    `<Unit>` arg, so the erased field's width is unknown AND a later Int is read.
    LOUD-skip (E602), never a silent wrong read."""
    assert "E602" in _warnings(_DIRECT_CALL_HARMFUL)
    assert _errors(_DIRECT_CALL_HARMFUL) == []


_DIRECT_CALL_TRAILING = """\
data W<T> { MkW(Int, T) }

private fn mk(-> @W<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkW(5, ()) }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match mk() {
    MkW(@Int, _) -> @Int.0
  }
}
"""


def test_direct_call_unrecoverable_trailing_wildcard_compiles() -> None:
    """Same unrecoverable direct-call scrutinee, but the type-parameter wildcard
    is TRAILING — its unknown width is never consumed, so the function still
    compiles and reads field 0 (5)."""
    assert "E602" not in _warnings(_DIRECT_CALL_TRAILING)
    assert _run(_DIRECT_CALL_TRAILING, fn="f") == 5


# =====================================================================
# Regression controls — structural Eq / show over a type-parameter-Unit
# instantiation were ALREADY correct (they recompute from the concrete type).
# Pin them so the wildcard fix does not perturb the recomputation path.
# =====================================================================

_EQ_EQUAL = """\
data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = a();
  let @Box<Unit> = a();
  @Box<Unit>.0 == @Box<Unit>.1
}
"""


def test_eq_box_unit_equal_control() -> None:
    assert _run(_EQ_EQUAL, fn="f") == 1


_EQ_DISTINCT = """\
data Box<T> { MkB(Int, T, Int) }

private fn a(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 22) }

private fn b(-> @Box<Unit>)
  requires(true) ensures(true) effects(pure)
{ MkB(11, (), 99) }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Unit> = a();
  let @Box<Unit> = b();
  @Box<Unit>.1 == @Box<Unit>.0
}
"""


def test_eq_box_unit_distinct_trailing_int_control() -> None:
    """Distinct trailing Int → unequal: Eq reads the real field, not garbage."""
    assert _run(_EQ_DISTINCT, fn="f") == 0


_SHOW_NAMED = """\
data Named<T> { N(T, String) }

private fn a(-> @Named<Unit>)
  requires(true) ensures(true) effects(pure)
{ N((), "hi") }

public fn f(-> @Bool)
  requires(true) ensures(true) effects(pure)
{
  let @Named<Unit> = a();
  eq(show(@Named<Unit>.0), "N(unit, hi)")
}
"""


def test_show_named_unit_control() -> None:
    assert _run(_SHOW_NAMED, fn="f") == 1
