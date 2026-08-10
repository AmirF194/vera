"""``throw``'s payload is obligated like every other narrowing site (#1268).

Every position a value narrows into a typed slot carries a proof obligation —
``let``, call argument, constructor field, effect-operation argument, handler
state init — and ``throw(v)`` narrows ``v`` into the ``Exn<E>`` payload exactly
as ``Log.emit(v)`` narrows into a declared op's formal.  It carried none.
``throw(0 - 5)`` under ``effects(<Exn<Nat>>)`` verified at 4/4 Tier 1 and
``vera run`` returned **-5** through the ``@Nat`` slot: no obligation, no
diagnostic, no guard.

The cause is not ``throw``'s ``Never`` return.  ``throw`` is a bare
:class:`~vera.ast.FnCall` with no entry in the function registry, so
``param_types`` is None and the formal loop that obligates a call's arguments
never runs.  #1203 met the same hole at the State ``put`` and added a
table-driven fallback for it — keyed on ``expr.name == "put"``, so ``throw``,
the only other bare built-in op taking an argument, stayed outside it.

Codegen emits no guard on the payload — ``throw`` lowers straight to a WASM
``throw $exn_<family>`` with the argument on the stack — so the obligation is
unguarded (``guarded=False``) at all three arms, and its Tier-3 leg discloses
rather than claiming a runtime check it never gets.  That claim is checked
against codegen here rather than asserted: the disclosure's own status is
pinned, and a run confirms the value really does pass through unchecked.
"""
from __future__ import annotations

import pytest

from tests.codegen_helpers import _run
from tests.verifier_helpers import _verify, _verify_err


_POS = "type Pos = { @Int | @Int.0 > 0 };\n"
_SMALL = "type Small = { @Byte | @Byte.0 < 10 };\n"


def _thrower(payload: str, value: str, *, prelude: str = "",
             params: str = "@Unit", handler_body: str = "0") -> str:
    """A function that throws *value* into an ``Exn<payload>``, and a handler.

    The handler is what makes the program whole; the obligation under test is
    at the ``throw``, in ``boom``.
    """
    return f"""
{prelude}
private fn boom({params} -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<{payload}>>)
{{
  throw({value})
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{payload}>] {{
    throw(@{payload}) -> {{ {handler_body} }}
  }} in {{
    boom({'(())' if params == '@Unit' else '(0 - 5)'})
  }}
}}
"""


class TestTheThrowPayloadIsObligated:
    """The obligation exists at all, in each of the three arms."""

    def test_a_negative_literal_into_a_nat_payload_is_refuted(self) -> None:
        """The `@Nat` arm: `throw(0 - 5)` into `Exn<Nat>` is an E503.

        This is the shape that ran to completion returning -5.
        """
        src = _thrower("Nat", "0 - 5", handler_body="nat_to_int(@Nat.0)")
        errs = _verify_err(src, "may be negative")
        assert any(e.error_code == "E503" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        binds = [o for o in _verify(src).obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["violated"], binds

    def test_a_violating_literal_into_a_refined_payload_is_refuted(
        self,
    ) -> None:
        """The refinement arm, over a base the verifier models: the solver
        refutes `0 - 5 > 0` and the site reports E505."""
        src = _thrower("Pos", "0 - 5", prelude=_POS)
        errs = _verify_err(src, "refinement predicate")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        binds = [o for o in _verify(src).obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["violated"], binds

    def test_a_nat_payload_widening_into_an_int_slot_is_obligated(
        self,
    ) -> None:
        """The widening arm: a bare `@Nat` thrown into an `Exn<Int>` payload
        reinterprets above i64.MAX, so the site records a
        `nat_to_int_coerce` obligation where it recorded nothing."""
        src = _thrower("Int", "@Nat.0", params="@Nat",
                       handler_body="@Int.0")
        # `boom(0 - 5)` is not a @Nat argument, so drive the call directly.
        src = src.replace("boom((0 - 5))", "boom(5)")
        coerce = [o for o in _verify(src).obligations
                  if o.kind == "nat_to_int_coerce"]
        assert coerce, [o.kind for o in _verify(src).obligations]


class TestTheConcreteGateReachesTheThrowPayload:
    """#1251(b)'s literal gate applies here for free, being the same helper."""

    def test_a_literal_over_an_unmodelled_base_is_decided(self) -> None:
        """`throw(200)` into `Exn<{ @Byte | @Byte.0 < 10 }>`.

        `Byte` is not a base the verifier models, so before #1251(b) this
        would have been the honest-but-silent Tier-3; routing `throw` into the
        shared helper means the concrete gate decides it, naming the value.
        """
        src = _thrower("Small", "200", prelude=_SMALL,
                       handler_body="byte_to_int(@Small.0)")
        errs = _verify_err(src, "violates the refinement")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]
        assert any("200" in e.description for e in errs), [
            e.description[:120] for e in errs
        ]

    def test_a_satisfying_literal_over_an_unmodelled_base_proves(self) -> None:
        """The passing twin, so the gate is not "reject every thrown literal"."""
        src = _thrower("Small", "5", prelude=_SMALL,
                       handler_body="byte_to_int(@Small.0)")
        result = _verify(src)
        binds = [o for o in result.obligations if o.kind == "refine_bind"]
        assert [o.status for o in binds] == ["verified"], binds
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]


class TestTheThrowPayloadObligationMatchesEveryOtherSite:
    """Contrast and spelling: the same value, reached three other ways."""

    _USER_EFFECT = """
type Pos = { @Int | @Int.0 > 0 };

effect Log {
  op emit(Pos -> Unit);
}

private fn boom(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<Log>)
{
  Log.emit(0 - 5)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Log] {
    emit(@Pos) -> { resume(()) }
  } in {
    boom(());
    0
  }
}
"""

    def test_the_user_effect_op_and_throw_agree(self) -> None:
        """A declared op's argument was loud while `throw`'s was silent, for
        the same value against the same refinement — the asymmetry that made
        this a bug rather than a documented limitation.  Both are loud now,
        at the same site name, so a reader cannot learn one rule from a user
        effect and have it fail to hold for `Exn`."""
        user = _verify_err(self._USER_EFFECT, "refinement predicate")
        thrown = _verify_err(
            _thrower("Pos", "0 - 5", prelude=_POS), "refinement predicate")
        assert {e.error_code for e in user} == {"E505"}, user
        assert {e.error_code for e in thrown} == {"E505"}, thrown
        assert all("effect-operation argument" in e.description
                   for e in user + thrown), [
            e.description[:90] for e in user + thrown
        ]

    def test_the_refined_alias_spelling_is_obligated_too(self) -> None:
        """`Exn<Payload>` where `type Payload = Pos` resolves through the
        alias chain to the same refinement, so it obligates identically — a
        gate keyed on the syntactic spelling would let it through."""
        src = _thrower("Payload", "0 - 5",
                       prelude=_POS + "\ntype Payload = Pos;\n")
        errs = _verify_err(src, "refinement predicate")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]


class TestTheThrowPayloadDisclosureIsHonestAboutTheGuard:
    """The verifier's `guarded=False` is checked against what codegen emits.

    A unit assertion that the status is `tier3_unguarded` says what the
    verifier believes; it cannot say whether the belief is true.  The pair
    here does: the status pins the flag, and the run pins codegen's side of
    it.  Were codegen to gain a payload guard, the run would trap and this
    class would go red rather than leaving the verifier quietly pessimistic;
    were the flag flipped without that codegen work, the status assertion
    would go red rather than leaving a claimed runtime check that is not
    emitted.
    """

    _UNTRANSLATABLE = """
private fn boom(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(array_length(string_lines("a\\nb")))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    boom(())
  }
}
"""

    _SYMBOLIC = """
private fn boom(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(@Int.0)
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    boom(@Int.0)
  }
}
"""

    def test_an_undischargeable_payload_discloses_unguarded(self) -> None:
        """`array_length` over a non-literal is deliberately untranslatable
        (#802), so the obligation reaches Tier 3 — and must land on the
        UNGUARDED leg (E504, excluded from the totals), not the
        runtime-guarded one."""
        result = _verify(self._UNTRANSLATABLE)
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["tier3_unguarded"], binds
        assert [o.error_code for o in binds] == ["E504"], binds
        assert result.summary.tier3_runtime == 0, result.summary

    def test_the_payload_really_is_unchecked_at_run_time(self) -> None:
        """...because codegen emits no guard: -5 comes back out of the `@Nat`
        payload.  This is the measurement the `guarded=False` above rests on,
        and the reason the refutation in the first class has to be an ERROR
        rather than a deferral to a runtime check."""
        assert _run(self._SYMBOLIC, "main", [-5]) == -5

    def test_a_symbolic_payload_the_contract_bounds_proves(self) -> None:
        """The obligation is dischargeable, not merely loud: a `requires`
        implying the payload's type proves it at Tier 1.  Without this the
        suite above is satisfied by a site that always fails."""
        result = _verify("""
private fn boom(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(<Exn<Nat>>)
{
  throw(@Int.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Nat>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    boom(7)
  }
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["verified"], binds
        assert not [
            d for d in result.diagnostics if d.severity == "error"
        ], [d.description[:90] for d in result.diagnostics]


class TestABareOpArgumentIsObligatedByStructureNotByName:
    """The fallback is keyed on "this resolves to an effect operation".

    Its first version listed the two built-in op NAMES that take a value, and
    a name list is a claim about every other name.  A user effect's op called
    bare is the same narrowing at the same site, and it was obligated iff it
    happened to be spelled `put` — `emit` was silent for the identical value
    against the identical refinement.  That falsifies the two places the rule
    is written down: spec §2.6.4 lists effect-operation arguments among the
    sites every narrowing is obligated at, and KNOWN_ISSUES.md's #754 row
    says every narrowing binding site is statically obligated.

    Resolving the operation is the structural question, and the code already
    resolved it one line below the gate to compute guardedness.
    """

    _USER_OP = """
type Pos = { @Int | @Int.0 > 0 };

effect Log {
  op %(name)s(Pos -> Unit);
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Log] {
    %(name)s(@Pos) -> { resume(()) }
  } in {
    %(name)s(0 - 5);
    0
  }
}
"""

    @pytest.mark.parametrize("name", ["emit", "put"])
    def test_a_bare_user_op_argument_is_obligated_whatever_its_name(
        self, name: str,
    ) -> None:
        """Both spellings are loud.  `put` was already, by coincidence."""
        errs = _verify_err(self._USER_OP % {"name": name},
                           "refinement predicate")
        assert any(e.error_code == "E505" for e in errs), [
            (e.error_code, e.description[:80]) for e in errs
        ]

    def test_a_user_op_is_not_claimed_runtime_guarded(self) -> None:
        """Guardedness stays keyed on the PARENT EFFECT, so a user effect's
        op — of either name — is the unguarded class and discloses E504
        rather than claiming the built-in `State` store's runtime guard.

        Named `put` deliberately: the coincidence that made the old gate look
        right is the same coincidence that would make a name-keyed
        guardedness computation look right.
        """
        result = _verify("""
effect Log {
  op put(Nat -> Unit);
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Log] {
    put(@Nat) -> { resume(()) }
  } in {
    put(array_length(string_lines("a\\nb")));
    0
  }
}
""")
        binds = [o for o in result.obligations if o.kind == "nat_bind"]
        assert [o.status for o in binds] == ["tier3_unguarded"], binds
        assert [o.error_code for o in binds] == ["E504"], binds
        assert result.summary.tier3_runtime == 0, result.summary

    def test_a_resume_value_is_obligated_exactly_once(self) -> None:
        """A `State` get clause's tail `resume(v)` is obligated from the
        HandleExpr arm, where the clause's effect identity is known.  Widening
        the bare-call gate must not let the walk obligate it a SECOND time
        from the call site — one violation, one diagnostic.
        """
        result = _verify("""
type Pos = { @Int | @Int.0 > 0 };

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(0 - 5) },
    put(@Pos) -> { resume(()) }
  } in {
    get(())
  }
}
""")
        binds = [o for o in result.obligations
                 if o.kind == "refine_bind" and o.status == "violated"]
        assert len(binds) == 1, binds
        assert len([d for d in result.diagnostics
                    if d.error_code == "E505"]) == 1, [
            d.description[:80] for d in result.diagnostics
        ]


@pytest.mark.parametrize("program", [
    "ch07_exn_handler.vera",
    "ch07_exn_string.vera",
    "ch07_exn_composite.vera",
    "ch07_exn_scalar_alias.vera",
    "ch07_exn_string_alias.vera",
    "ch07_exn_param_alias.vera",
])
def test_the_exn_conformance_programs_stay_clean(program: str) -> None:
    """The canaries: obligating a position that had none must not turn a
    correct `throw` into a rejection.  Every conformance program that throws
    is verified whole here, so a regression names itself instead of arriving
    as one line of a corpus sweep."""
    import pathlib

    path = pathlib.Path(__file__).parent / "conformance" / program
    result = _verify(path.read_text(encoding="utf-8"))
    assert not [
        d for d in result.diagnostics if d.severity == "error"
    ], [d.description[:90] for d in result.diagnostics]
