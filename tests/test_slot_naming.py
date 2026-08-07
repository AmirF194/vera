"""Rule table for :mod:`vera.naming` — the ONE slot/family naming renderer.

Each test pins one clause of THE RULE (see the module docstring of
``vera/naming.py``) to an EXACT rendered string.  The companion
``test_slot_naming_differential.py`` proves the module agrees with the
checker across the whole corpus; this file states what that agreed-upon
rendering *is*, so a future change to either side has to argue with a
written-down expectation rather than silently re-baseline.
"""

from __future__ import annotations

import pytest

from vera import ast
from vera.checker.core import TypeChecker
from vera.naming import (
    EMPTY_ALIAS_ENV,
    AliasEnv,
    AliasResolutionDepthError,
    alias_env_from_declarations,
    alias_env_from_environment,
    family_name,
    is_ref_spellable,
    refinement_binder_parts,
    resolve_alias_type_expr,
    slot_name,
    slot_ref_key,
    type_arg_name,
    with_type_params,
)
from vera.parser import parse_to_ast

# =====================================================================
# Helpers
# =====================================================================

ALIASES = """\
type MyAlias = Int;
type A2 = MyAlias;
type Box<T> = Option<T>;
type PosT<T> = { @T | @T.0 > 0 };
type Pos = { @Int | @Int.0 > 0 };
type Count = Nat;
type Composite = Option<Int>;
type BoxedComposite = Box<MyAlias>;
type Txt = String;
type Sized = { @Array<Txt> | array_length(@Array<Txt>.0) > 0 };
type Cyc1 = Cyc2;
type Cyc2 = Cyc1;
type Fwd = Later;
type Later = Int;
"""

_FN = """\
public {forall}fn probe({shape} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}
"""


def _parse(shape: str, prelude: str = ALIASES, forall: str = "") -> ast.Program:
    return parse_to_ast(prelude + _FN.format(shape=shape, forall=forall))


def _probe(
    shape: str, prelude: str = ALIASES, forall: str = "",
) -> tuple[ast.TypeExpr, AliasEnv]:
    """The first parameter's TypeExpr plus the module-scoped naming env."""
    prog = _parse(shape, prelude, forall)
    fn = next(d.decl for d in prog.declarations
              if isinstance(d.decl, ast.FnDecl))
    env = alias_env_from_declarations(prog.declarations)
    if fn.forall_vars:
        env = with_type_params(env, fn.forall_vars)
    return fn.params[0], env


def _name(shape: str, prelude: str = ALIASES, forall: str = "") -> str:
    te, env = _probe(shape, prelude, forall)
    return slot_name(te, env)


def _env(prelude: str = ALIASES) -> AliasEnv:
    return alias_env_from_declarations(parse_to_ast(prelude).declarations)


# =====================================================================
# Clause: the head is SYNTACTIC (alias-opaque)
# =====================================================================

def test_bare_head_renders_as_itself() -> None:
    assert _name("@Int") == "Int"


def test_alias_head_stays_opaque() -> None:
    """`@MyAlias` counts MyAlias bindings, not Int bindings."""
    assert _name("@MyAlias") == "MyAlias"
    assert _name("@A2") == "A2"


def test_parameterised_alias_head_stays_opaque() -> None:
    assert _name("@Box<Int>") == "Box<Int>"


# =====================================================================
# Clause: type ARGUMENTS are fully resolved
# =====================================================================

def test_alias_argument_resolves() -> None:
    assert _name("@Option<MyAlias>") == "Option<Int>"


def test_nested_alias_argument_resolves_through_the_chain() -> None:
    assert _name("@Option<A2>") == "Option<Int>"


def test_parameterised_alias_argument_substitutes_then_resolves() -> None:
    assert _name("@Option<Box<MyAlias>>") == "Option<Option<Int>>"


def test_multi_argument_join_matches_the_checkers() -> None:
    assert _name("@Map<MyAlias, Box<A2>>") == "Map<Int, Option<Int>>"


def test_argument_arity_mismatch_renders_unknown() -> None:
    """A partially-applied alias is E133 at check and `?` here."""
    assert _name("@Option<Box>") == "Option<?>"
    assert _name("@Option<Box<Int, Int>>") == "Option<?>"


def test_head_arity_mismatch_still_renders_the_head_syntactically() -> None:
    assert _name("@Box") == "Box"


# =====================================================================
# Clause: refinements
# =====================================================================

def test_refinement_at_top_level_renders_its_base() -> None:
    assert _name("@{ @Int | @Int.0 > 0 }") == "Int"
    # The base is a head, so ITS arguments resolve: `Array<String>`, not the
    # source-spelled `Array<Txt>` codegen's refinement binder produces (see
    # `test_refinement_binder_names_parameterised_bases_syntactically`) —
    # the exact split #1208 records.
    assert _name("@{ @Array<Txt> | array_length(@Array<Txt>.0) > 0 }") \
        == "Array<String>"


def test_refinement_alias_at_top_level_stays_opaque() -> None:
    assert _name("@Pos") == "Pos"


def test_refinement_in_argument_position_renders_the_elided_form() -> None:
    assert _name("@Option<Pos>") == "Option<{@Int | ...}>"


def test_parameterised_refinement_alias_substitutes_before_refining() -> None:
    """Ordering: substitute the alias parameters, THEN take the refinement
    branch — otherwise the binder renders as the un-substituted `{@T | ...}`
    and never matches the instantiated key."""
    assert _name("@Option<PosT<Int>>") == "Option<{@Int | ...}>"
    assert _name("@Option<PosT<MyAlias>>") == "Option<{@Int | ...}>"


# =====================================================================
# Clause: function types
# =====================================================================

def test_function_type_at_top_level_renders_fn() -> None:
    assert _name("@fn(Int -> Int) effects(pure)") == "Fn"


def test_function_type_in_argument_position_renders_in_full() -> None:
    assert _name("@Option<fn(MyAlias -> Int) effects(pure)>") \
        == "Option<fn(Int -> Int) effects(pure)>"


def test_function_type_argument_sorts_its_effect_row() -> None:
    """Written unsorted; rendered sorted, so the name is stable across
    hash seeds (the row is a frozenset)."""
    assert _name("@Option<fn(Int -> Int) effects(<State<Int>, IO>)>") \
        == "Option<fn(Int -> Int) effects(<IO, State<Int>>)>"


# =====================================================================
# Clause: total — the `?` paths
# =====================================================================

def test_decimal_with_arguments_drops_them() -> None:
    """`Decimal` is opaque and non-parameterised (E134 at check); the
    arguments do not reach the name."""
    assert _name("@Option<Decimal<Int>>") == "Option<Decimal>"


def test_removed_alias_renders_unknown_in_argument_position() -> None:
    assert _name("@Option<Float>") == "Option<?>"


def test_removed_alias_head_stays_syntactic() -> None:
    assert _name("@Float") == "Float"


# =====================================================================
# Clause: a DECLARED ADT outranks the special-cased names
# =====================================================================

_ADT_SHADOWS = ALIASES + """\
private data Float { MkFl(Int) }
private data Decimal { MkDec(Int) }
"""


def test_declared_adt_outranks_the_removed_alias_branch() -> None:
    """`private data Float { ... }` checks clean (`Float` is not a primitive,
    only a REMOVED alias), and the checker reaches its data-type branch
    BEFORE its removed-alias branch — so the argument renders `Float`, not
    the `?` the removed-alias branch would give."""
    assert _name("@Option<Float>", prelude=_ADT_SHADOWS) == "Option<Float>"
    assert _name("@Float", prelude=_ADT_SHADOWS) == "Float"


def test_declared_adt_outranks_the_builtin_decimal_branch() -> None:
    """The built-in `Decimal` branch is opaque and DROPS type arguments; a
    user-declared `data Decimal` keeps them, because the data-type branch is
    reached first."""
    assert _name("@Option<Decimal<Int>>", prelude=_ADT_SHADOWS) \
        == "Option<Decimal<Int>>"
    assert _name("@Decimal<Float>", prelude=_ADT_SHADOWS) == "Decimal<Float>"


def test_an_alias_still_outranks_a_same_named_adt() -> None:
    """Alias before data type, as in the checker: both may be declared under
    one name, and an argument resolves to the alias body."""
    prelude = ALIASES + "private data MyAlias { MkMy(Int) }\n"
    assert _name("@Option<MyAlias>", prelude=prelude) == "Option<Int>"


def test_adt_visibility_is_bounded_by_declaration_index() -> None:
    """ADT visibility is bounded by declaration index, exactly as alias
    visibility is — the two registries share ONE index space (#1208).

    An alias body naming a special-cased ADT declared BELOW it resolves
    against the table as it stood when `_register_alias` ran, which did not
    yet hold the ADT: the built-in `Decimal` branch, arguments dropped.  The
    ADT is only reachable from an alias declared AFTER it.  Both directions
    are asserted, because a bound applied in the wrong direction would agree
    with the checker on one ordering and not the other."""
    forward = "type M = Decimal<Int>;\nprivate data Decimal { MkDec(Int) }\n"
    assert _name("@Option<M>", prelude=forward) == "Option<Decimal>"
    backward = "private data Decimal { MkDec(Int) }\ntype M = Decimal<Int>;\n"
    assert _name("@Option<M>", prelude=backward) == "Option<Decimal<Int>>"


def test_removed_alias_adt_visibility_is_bounded_the_same_way() -> None:
    """The mirror spelling of the corner: a `data Float` declared below the
    alias leaves the removed-alias branch reachable (`?`); declared above it,
    the ADT branch wins."""
    forward = "type F = Float;\nprivate data Float { MkFl(Int) }\n"
    assert _name("@Option<F>", prelude=forward) == "Option<?>"
    backward = "private data Float { MkFl(Int) }\ntype F = Float;\n"
    assert _name("@Option<F>", prelude=backward) == "Option<Float>"


def test_adt_visibility_bound_does_not_reach_the_top_level() -> None:
    """The bound applies INSIDE an alias body only.  A slot named directly
    for the ADT renders against the whole table, whatever the declaration
    order — the checker resolves those after registration has finished."""
    forward = "type M = Decimal<Int>;\nprivate data Decimal { MkDec(Int) }\n"
    assert _name("@Option<Decimal<Int>>", prelude=forward) \
        == "Option<Decimal<Int>>"
    assert _name("@Decimal<Int>", prelude=forward) == "Decimal<Int>"


def test_unresolvable_type_expression_renders_question_mark() -> None:
    class _Alien(ast.TypeExpr):
        pass

    assert slot_name(_Alien(), EMPTY_ALIAS_ENV) == "?"
    assert type_arg_name(_Alien(), EMPTY_ALIAS_ENV) == "?"


# =====================================================================
# Clause: type parameters SHADOW aliases
# =====================================================================

def test_type_parameter_shadows_a_same_named_alias() -> None:
    """`type MyAlias = Int` is in scope, but a `forall<MyAlias>` parameter
    of the same name wins — the shadowing test comes first."""
    env = _env()
    te = ast.NamedType(
        name="Option",
        type_args=(ast.NamedType(name="MyAlias", type_args=None),),
    )
    assert slot_name(te, env) == "Option<Int>"
    assert slot_name(te, with_type_params(env, ["MyAlias"])) \
        == "Option<MyAlias>"


def test_type_parameter_argument_renders_as_the_variable() -> None:
    assert _name("@Option<T>", forall="forall<T> ") == "Option<T>"
    assert _name("@T", forall="forall<T> ") == "T"


# =====================================================================
# Clause: alias visibility follows declaration order
# =====================================================================

def test_alias_cycle_terminates_on_the_opaque_placeholder() -> None:
    """`type Cyc1 = Cyc2; type Cyc2 = Cyc1;` — E132 at check.  The renderer
    neither hangs nor raises: an alias body sees only the aliases declared
    before it, so the cycle bottoms out exactly where the checker's
    registration-order resolution bottoms out."""
    assert _name("@Option<Cyc1>") == "Option<Cyc2>"
    assert _name("@Option<Cyc2>") == "Option<Cyc2>"


def test_forward_reference_stays_opaque() -> None:
    """`type Fwd = Later;` is declared before `Later`, so its body resolved
    against a table that did not yet contain `Later`."""
    assert _name("@Option<Fwd>") == "Option<Later>"
    assert _name("@Option<Later>") == "Option<Int>"


def test_deep_alias_chain_resolves_without_a_depth_bound() -> None:
    """The naming walk is bounded by declaration order, not by a depth
    limit, so a 40-deep chain resolves rather than degrading."""
    depth = 40
    chain = f"type L{depth} = Int;\n" + "".join(
        f"type L{i} = L{i + 1};\n" for i in reversed(range(depth))
    )
    assert _name("@Option<L0>", prelude=chain) == "Option<Int>"
    # Declared the other way round, every link is a forward reference and
    # each one stays opaque — the registration-order rule, not a bound.
    forward = "".join(
        f"type F{i} = F{i + 1};\n" for i in range(depth)
    ) + f"type F{depth} = Int;\n"
    assert _name("@Option<F0>", prelude=forward) == "Option<F1>"


def test_alias_walk_depth_bound_still_raises_for_its_own_callers() -> None:
    """The moved-but-unchanged :func:`resolve_alias_type_expr` keeps its
    loud overflow (the family-collapse callers must not degrade to an
    opaque fallback, which would split the State/Exn family)."""
    depth = 40
    aliases: dict[str, ast.TypeExpr] = {
        f"L{i}": ast.NamedType(name=f"L{i + 1}", type_args=None)
        for i in range(depth)
    }
    aliases[f"L{depth}"] = ast.NamedType(name="Int", type_args=None)
    with pytest.raises(AliasResolutionDepthError):
        resolve_alias_type_expr(
            ast.NamedType(name="L0", type_args=None), aliases, {})


# =====================================================================
# Slot-reference keys
# =====================================================================

def test_slot_ref_key_matches_the_binding_side() -> None:
    env = _env()
    ref = ast.SlotRef(
        type_name="Option",
        type_args=(ast.NamedType(name="MyAlias", type_args=None),),
        index=0,
    )
    te, _ = _probe("@Option<MyAlias>")
    assert slot_ref_key(ref, env) == slot_name(te, env) == "Option<Int>"


def test_bare_slot_ref_key_is_the_type_name() -> None:
    ref = ast.SlotRef(type_name="MyAlias", type_args=None, index=2)
    assert slot_ref_key(ref, _env()) == "MyAlias"


def test_slot_ref_key_resolves_nested_alias_arguments() -> None:
    ref = ast.SlotRef(
        type_name="Array",
        type_args=(ast.NamedType(
            name="Option",
            type_args=(ast.NamedType(name="A2", type_args=None),)),),
        index=0,
    )
    assert slot_ref_key(ref, _env()) == "Array<Option<Int>>"


# =====================================================================
# Family names (#1209) — cell identity, not source spelling
# =====================================================================

def _fam(name: str, fallback: str = "FALLBACK") -> str:
    return family_name(
        ast.NamedType(name=name, type_args=None), _env(), fallback)


def test_family_name_collapses_a_scalar_alias() -> None:
    assert _fam("Count") == "Nat"


def test_family_name_collapses_a_composite_alias() -> None:
    """#1209: `State<Composite>` is the same cell as `State<Option<Int>>`."""
    assert _fam("Composite") == "Option<Int>"


def test_family_name_collapses_a_parameterised_composite_alias() -> None:
    assert _fam("BoxedComposite") == "Option<Int>"
    assert family_name(
        ast.NamedType(
            name="Box",
            type_args=(ast.NamedType(name="A2", type_args=None),)),
        _env(), "FALLBACK") == "Option<Int>"


def test_family_name_collapses_a_refinement_to_its_base() -> None:
    assert _fam("Pos") == "Int"


def test_family_name_falls_back_when_there_is_no_nameable_family() -> None:
    assert family_name(None, _env(), "FALLBACK") == "FALLBACK"
    assert _fam("Float") == "FALLBACK"  # removed alias -> unresolvable
    fn_te, env = _probe("@fn(Int -> Int) effects(pure)")
    assert family_name(fn_te, env, "FALLBACK") == "FALLBACK"


# =====================================================================
# Spellability
# =====================================================================

@pytest.mark.parametrize("name", [
    "Int", "MyAlias", "Fn", "Option<Int>", "Map<Int, Option<Int>>",
    "Array<Option<Tuple<Int, Bool>>>", "Vera_Thing2",
])
def test_spellable_names(name: str) -> None:
    assert is_ref_spellable(name)


@pytest.mark.parametrize("name", [
    "?", "", "Option<?>", "{@Int | ...}", "Option<{@Int | ...}>",
    "fn(Int -> Int) effects(pure)", "Option<fn(Int -> Int) effects(pure)>",
    "lower", "Option<Int", "Option<Int>>", "Option<Int,Bool>",
])
def test_unspellable_names(name: str) -> None:
    assert not is_ref_spellable(name)


# =====================================================================
# Refinement binders (codegen's guard derivation, as a pure function)
# =====================================================================

def test_refinement_binder_names_the_base_slot() -> None:
    binder = refinement_binder_parts(
        ast.NamedType(name="Pos", type_args=None), _env())
    assert binder is not None
    assert binder.binder_name == "Int"
    assert not binder.base_is_refinement


def test_refinement_binder_names_parameterised_bases_through_slot_name() -> None:
    """The binder is `slot_name`'s answer (#1208), so it agrees with what a
    predicate's `@Array<Txt>.0` resolves to through `slot_ref_key` and with
    what the checker bound the predicate's binder under.  The pre-
    consolidation derivation named the arguments by SOURCE spelling
    (`Array<Txt>`) and met a reference side that was syntactic too; with both
    resolved they meet here."""
    binder = refinement_binder_parts(
        ast.NamedType(name="Sized", type_args=None), _env())
    assert binder is not None
    assert binder.binder_name == "Array<String>"
    assert binder.binder_name == slot_ref_key(
        ast.SlotRef(
            type_name="Array",
            type_args=(ast.NamedType(name="Txt", type_args=None),),
            index=0,
        ),
        _env(),
    )


def test_refinement_binder_conjoins_the_nat_range() -> None:
    prelude = ALIASES + "type PosCount = { @Count | @Count.0 < 10 };\n"
    binder = refinement_binder_parts(
        ast.NamedType(name="PosCount", type_args=None), _env(prelude))
    assert binder is not None
    assert binder.binder_name == "Count"
    assert isinstance(binder.predicate, ast.BinaryExpr)
    assert binder.predicate.op is ast.BinOp.AND
    lower = binder.predicate.left
    assert isinstance(lower, ast.BinaryExpr) and lower.op is ast.BinOp.GE
    assert lower.left == ast.SlotRef(
        type_name="Count", type_args=None, index=0)


def test_refinement_binder_flags_a_refinement_over_a_refinement() -> None:
    prelude = ALIASES + "type Tiny = { @Pos | @Pos.0 < 10 };\n"
    binder = refinement_binder_parts(
        ast.NamedType(name="Tiny", type_args=None), _env(prelude))
    assert binder is not None
    assert binder.base_is_refinement


def test_refinement_binder_returns_none_for_a_non_refinement() -> None:
    assert refinement_binder_parts(
        ast.NamedType(name="Count", type_args=None), _env()) is None


# =====================================================================
# Environment construction
# =====================================================================

def test_alias_env_from_environment_reads_the_registered_bodies() -> None:
    """The C0 `TypeAliasInfo.body` wiring: a live checker environment
    yields the same naming env the declarations do."""
    src = ALIASES + _FN.format(shape="@Option<MyAlias>", forall="")
    prog = parse_to_ast(src)
    checker = TypeChecker(source=src)
    checker.check_program(prog)
    env = alias_env_from_environment(checker.env)
    assert "MyAlias" in env.aliases
    assert env.alias_params["Box"] == ("T",)
    te = next(d.decl for d in prog.declarations
              if isinstance(d.decl, ast.FnDecl)).params[0]
    assert slot_name(te, env) == "Option<Int>"


def test_alias_env_from_declarations_layers_a_base_underneath() -> None:
    base = _env("type MyAlias = Int;\n")
    layered = alias_env_from_declarations(
        parse_to_ast("type Wrap = Option<MyAlias>;\n").declarations, base)
    assert set(layered.aliases) == {"MyAlias", "Wrap"}
    assert family_name(
        ast.NamedType(name="Wrap", type_args=None), layered, "FB") \
        == "Option<Int>"


def test_empty_alias_env_resolves_nothing() -> None:
    te = ast.NamedType(
        name="Option",
        type_args=(ast.NamedType(name="MyAlias", type_args=None),),
    )
    assert slot_name(te, EMPTY_ALIAS_ENV) == "Option<MyAlias>"


def test_with_type_params_does_not_mutate_its_input() -> None:
    env = _env()
    extended = with_type_params(env, ["MyAlias"])
    assert env.type_params == frozenset()
    assert extended.type_params == frozenset({"MyAlias"})
