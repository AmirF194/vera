"""Tests for vera.prelude — standard prelude injection."""

from __future__ import annotations

import re

from vera import ast
from vera.parser import parse
from vera.transform import transform
from vera.prelude import inject_prelude


def _make_program(src: str) -> ast.Program:
    tree = parse(src)
    return transform(tree)


def _fn_names(prog: ast.Program) -> set[str]:
    return {
        tld.decl.name
        for tld in prog.declarations
        if isinstance(tld.decl, ast.FnDecl)
    }


def _data_names(prog: ast.Program) -> set[str]:
    return {
        tld.decl.name
        for tld in prog.declarations
        if isinstance(tld.decl, ast.DataDecl)
    }


def _alias_names(prog: ast.Program) -> set[str]:
    return {
        tld.decl.name
        for tld in prog.declarations
        if isinstance(tld.decl, ast.TypeAliasDecl)
    }


# Prelude ADT names injected by default
_PRELUDE_DATA_NAMES = {"Option", "Result", "Ordering", "UrlParts"}

# Prelude combinator function names
_OPTION_FN_NAMES = {"option_unwrap_or", "option_map", "option_and_then"}
_RESULT_FN_NAMES = {"result_unwrap_or", "result_map"}
# ``array_map``, ``array_filter``, and ``array_fold`` are all
# emitted as iterative WASM by codegen (#480); none of them have
# prelude-injected recursive implementations.  The set is empty but
# kept around so adding a future array helper that DOES need prelude
# injection is a one-line change.
_ARRAY_FN_NAMES: set[str] = set()


class TestPreludeADTs:
    """Tests for unconditional ADT injection."""

    def test_prelude_injects_all_adts(self) -> None:
        """Option, Result, Ordering, UrlParts injected without user defs."""
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _data_names(prog)
        assert _PRELUDE_DATA_NAMES.issubset(names)

    def test_user_data_shadows_prelude(self) -> None:
        """User-defined Option replaces the prelude's Option."""
        prog = _make_program(
            "public data Option<T> { None, Some(T) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        # Count Option definitions — should be exactly 1 (user's)
        option_count = sum(
            1 for tld in prog.declarations
            if isinstance(tld.decl, ast.DataDecl) and tld.decl.name == "Option"
        )
        assert option_count == 1
        # Other prelude ADTs still injected
        names = _data_names(prog)
        assert {"Result", "Ordering", "UrlParts"}.issubset(names)


class TestPreludeCombinators:
    """Tests for combinator injection."""

    def test_option_combinators_injected(self) -> None:
        """Option combinators injected without user Option definition."""
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert _OPTION_FN_NAMES.issubset(names)

    def test_result_combinators_injected(self) -> None:
        """Result combinators injected without user Result definition."""
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert _RESULT_FN_NAMES.issubset(names)

    def test_array_operations_not_injected(self) -> None:
        """No array combinators injected as prelude functions.

        All three combinators (``array_map``, ``array_filter``,
        ``array_fold``) are emitted as iterative WASM by codegen
        (#480).  The explicit absence assertions guard against
        accidental re-injection — especially ``*_go`` helpers that
        used to be paired with each recursive implementation.
        """
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        for forbidden in (
            "array_map", "array_map_go",
            "array_filter", "array_filter_go",
            "array_fold", "array_fold_go",
        ):
            assert forbidden not in names, (
                f"{forbidden} should not be prelude-injected — it's "
                f"emitted as iterative WASM by codegen (#480)."
            )

    def test_combinators_with_user_option(self) -> None:
        """Option combinators still injected when user defines standard Option."""
        prog = _make_program(
            "public data Option<T> { None, Some(T) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert _OPTION_FN_NAMES.issubset(names)

    def test_non_standard_option_skips_combinators(self) -> None:
        """Non-standard Option (Just instead of Some) skips combinators.

        The user's data type shadows the prelude's Option, but since
        the constructors don't match, Option combinators are not injected.
        Other prelude declarations (Result, Ordering, array ops) still are.
        """
        prog = _make_program(
            "public data Option<T> { None, Just(T) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        # Option combinators NOT injected
        assert not _OPTION_FN_NAMES.intersection(names)
        # Result combinators and array ops still injected
        assert _RESULT_FN_NAMES.issubset(names)
        assert _ARRAY_FN_NAMES.issubset(names)


    def test_non_standard_result_skips_combinators(self) -> None:
        """Non-standard Result (Fail instead of Err) skips combinators."""
        prog = _make_program(
            "public data Result<T, E> { Ok(T), Fail(E) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert not _RESULT_FN_NAMES.intersection(names)
        # Option combinators and array ops still injected
        assert _OPTION_FN_NAMES.issubset(names)
        assert _ARRAY_FN_NAMES.issubset(names)

    def test_extra_constructor_option_skips_combinators(self) -> None:
        """Option with extra constructor skips combinators."""
        prog = _make_program(
            "public data Option<T> { None, Some(T), Unknown }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert not _OPTION_FN_NAMES.intersection(names)

    def test_extra_constructor_result_skips_combinators(self) -> None:
        """Result with extra constructor skips combinators."""
        prog = _make_program(
            "public data Result<T, E> { Ok(T), Err(E), Retry }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert not _RESULT_FN_NAMES.intersection(names)

    def test_concrete_option_skips_combinators(self) -> None:
        """Option with concrete field type (Some(Int)) skips combinators."""
        prog = _make_program(
            "public data Option<T> { None, Some(Int) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert not _OPTION_FN_NAMES.intersection(names)

    def test_concrete_result_skips_combinators(self) -> None:
        """Result with concrete field types (Ok(Int), Err(String)) skips."""
        prog = _make_program(
            "public data Result<T, E> { Ok(Int), Err(String) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _fn_names(prog)
        assert not _RESULT_FN_NAMES.intersection(names)


class TestPreludeShadowing:
    """Tests for user-defined function shadowing."""

    def test_user_fn_shadows_combinator(self) -> None:
        """User-defined option_map is not overwritten."""
        prog = _make_program(
            "public data Option<T> { None, Some(T) }\n"
            "public fn option_map(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        user_fns = [
            tld.decl
            for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
            and tld.decl.name == "option_map"
        ]
        assert len(user_fns) >= 1
        # Exactly one user-defined (no forall_vars), rest are prelude
        assert sum(1 for fn in user_fns if fn.forall_vars is None) == 1
        for fn in user_fns:
            if fn.forall_vars is not None:
                assert fn.forall_vars  # prelude version has forall_vars


class TestPreludeTypeAliases:
    """Tests for type alias injection."""

    def test_option_aliases_injected(self) -> None:
        """OptionMapFn and OptionBindFn injected with Option combinators."""
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _alias_names(prog)
        assert "OptionMapFn" in names
        assert "OptionBindFn" in names

    def test_result_alias_injected(self) -> None:
        """ResultMapFn injected with Result combinators."""
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _alias_names(prog)
        assert "ResultMapFn" in names

    def test_array_aliases_injected(self) -> None:
        """Array type aliases always injected."""
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        names = _alias_names(prog)
        assert "ArrayMapFn" in names
        assert "ArrayFilterFn" in names
        assert "ArrayFoldFn" in names


class TestPreludeInternalAliases:
    """#1184: the combinators resolve through reserved-name twins."""

    def test_no_combinator_spells_a_user_facing_alias(self) -> None:
        """The structural statement of the #1184 fix, as a drift guard.

        A prelude combinator that reaches for a user-facing alias name
        is re-typable by any user or module declaration of that name —
        silently, and differently in the main-file and module
        namespaces.  Every prelude body must spell its closure
        parameters with the reserved ``Vera``-prefixed twin instead, so
        adding a combinator that reaches for the public name fails
        here rather than in someone's program.
        """
        from vera import prelude

        public_names = {
            name
            for block in (
                prelude._OPTION_TYPE_ALIASES,
                prelude._RESULT_TYPE_ALIASES,
                prelude._ARRAY_TYPE_ALIASES,
            )
            for name in re.findall(
                r"^type\s+([A-Za-z_][A-Za-z0-9_]*)", block, re.MULTILINE,
            )
        }
        assert public_names, "no prelude alias blocks found — guard is inert"
        for block_name in (
            "_OPTION_COMBINATORS", "_RESULT_COMBINATORS",
            "_ARRAY_COMBINATORS", "_JSON_COMBINATORS", "_HTML_COMBINATORS",
        ):
            block = getattr(prelude, block_name)
            for name in public_names:
                assert not re.search(rf"\b{name}\b", block), (
                    f"{block_name} resolves through the user-facing alias "
                    f"{name!r}; use the reserved "
                    f"{prelude._INTERNAL_ALIAS_PREFIX}{name} twin (#1184)"
                )

    def test_internal_twin_is_derived_from_the_public_declaration(
        self,
    ) -> None:
        """The twin restates the public alias's body under a new name.

        Only the declared name is rewritten — a body mentioning
        ``Option`` or a ``Vera*`` type parameter must survive verbatim,
        or the twin would alias a different type from the name the user
        can still spell.
        """
        from vera.prelude import _internal_alias_decls

        assert _internal_alias_decls(
            "type OptionBindFn<VeraA, VeraB> = fn(VeraA -> Option<VeraB>)"
            " effects(pure);\n"
        ) == (
            "type VeraOptionBindFn<VeraA, VeraB> = fn(VeraA -> Option<VeraB>)"
            " effects(pure);\n"
        )

    def test_internal_twins_injected_even_when_user_shadows_the_alias(
        self,
    ) -> None:
        """A user alias may take the public name; it must not take the twin.

        This is the injection-side half of the fix: the user's
        ``OptionMapFn`` shadows the public declaration (its right), and
        ``option_map`` keeps a resolvable parameter type regardless.
        """
        prog = _make_program(
            "type OptionMapFn = Int;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        aliases = {
            tld.decl.name: tld.decl
            for tld in prog.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }
        assert "VeraOptionMapFn" in aliases
        assert "VeraOptionBindFn" in aliases
        assert "VeraResultMapFn" in aliases
        # The combinators spell the twins at arity 2, so the parsed
        # declarations must carry the derived parameter list (PR #1191
        # review): a twin arriving with type_params None would break
        # resolution while presence checks stay green.
        assert aliases["VeraOptionMapFn"].type_params == ("VeraA", "VeraB")
        assert aliases["VeraOptionBindFn"].type_params == ("VeraA", "VeraB")
        assert aliases["VeraResultMapFn"].type_params == ("VeraA", "VeraB")
        # The user's own declaration is the only OptionMapFn left.
        user_decls = [
            tld.decl
            for tld in prog.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
            and tld.decl.name == "OptionMapFn"
        ]
        assert len(user_decls) == 1
        assert user_decls[0].type_params is None


class TestPreludeEndToEnd:
    """End-to-end tests verifying combinators compile and run."""

    def test_option_unwrap_or_some(self) -> None:
        """option_unwrap_or(Some(42), 0) returns 42."""
        from tests.test_codegen_closures import _run
        src = """\
public data Option<T> { None, Some(T) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(Some(42), 0)
}
"""
        assert _run(src, "test") == 42

    def test_option_map_some(self) -> None:
        """option_map(Some(10), +1) returns Some(11)."""
        from tests.test_codegen_closures import _run
        src = """\
public data Option<T> { None, Some(T) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(
    option_map(Some(10), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }),
    0
  )
}
"""
        assert _run(src, "test") == 11

    def test_option_and_then_some(self) -> None:
        """option_and_then(Some(5), *2) returns Some(10)."""
        from tests.test_codegen_closures import _run
        src = """\
public data Option<T> { None, Some(T) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(
    option_and_then(Some(5), fn(@Int -> @Option<Int>) effects(pure) {
      Some(@Int.0 * 2)
    }),
    0
  )
}
"""
        assert _run(src, "test") == 10

    def test_result_unwrap_or_ok(self) -> None:
        """result_unwrap_or(Ok(77), 0) returns 77."""
        from tests.test_codegen_closures import _run
        src = """\
public data Result<T, E> { Ok(T), Err(E) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  result_unwrap_or(Ok(77), 0)
}
"""
        assert _run(src, "test") == 77

    def test_result_map_ok(self) -> None:
        """result_map(Ok(100), -1) returns Ok(99)."""
        from tests.test_codegen_closures import _run
        src = """\
public data Result<T, E> { Ok(T), Err(E) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  result_unwrap_or(
    result_map(Ok(100), fn(@Int -> @Int) effects(pure) { @Int.0 - 1 }),
    0
  )
}
"""
        assert _run(src, "test") == 99

    def test_no_boilerplate_option(self) -> None:
        """Option pattern matching works without local data definition."""
        from tests.test_codegen_closures import _run
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match Some(42) {
    Some(@Int) -> @Int.0,
    None -> 0
  }
}
"""
        assert _run(src, "test") == 42

    def test_no_boilerplate_result(self) -> None:
        """Result pattern matching works without local data definition."""
        from tests.test_codegen_closures import _run
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match Ok(99) {
    Ok(@Int) -> @Int.0,
    Err(@String) -> 0
  }
}
"""
        assert _run(src, "test") == 99

    def test_no_boilerplate_combinators(self) -> None:
        """Combinators work without local data definitions."""
        from tests.test_codegen_closures import _run
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(Some(7), 0) + result_unwrap_or(Ok(3), 0)
}
"""
        assert _run(src, "test") == 10
