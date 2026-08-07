"""Every consumer renders against the env the CHECKER rendered under (#1208).

The naming consolidation gave the whole toolchain one renderer; these tests pin
the other half of the contract — the ENVIRONMENT it is handed.  A renderer fed a
neighbouring module's namespace, or a module env where the checker had a
``forall`` variable in scope, produces names nobody looks up, and the miss is
silent: an obligation attaches to the wrong parameter, or vanishes.

Four provenance failures, each with the adversarial probe that exhibited it:

* the verifier + SMT layer rendered an IMPORTED callee's contract slots with the
  IMPORTER's alias env (``reviewA2`` p10 / p11 / p8q);
* the verifier monomorphized an IMPORTED generic under the importer's env while
  codegen used the defining module's, so the two proved and emitted DIFFERENT
  bodies (``reviewA2`` p3 + ``pin_clone.py``);
* the monomorphizer's De Bruijn recount, the verifier's parameter declaration
  and codegen's template emission all rendered a generic's signature WITHOUT its
  ``forall`` variables, so a same-named module alias resolved through where the
  checker had a type variable (``reviewA1`` m01 / m03 / v01);
* the tester handed ``SmtContext`` the un-narrowed env while keying its own slot
  names in the narrowed one (``reviewA1`` finding 4).
"""
from __future__ import annotations

import os
import tempfile
from pathlib import Path

from vera import ast
from vera.checker import typecheck
from vera.codegen import compile, execute
from vera.monomorphize import Monomorphizer
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.transform import transform
from vera.verifier import ContractVerifier, VerifyResult, verify

from tests.codegen_helpers import _compile_ok, _run


# =====================================================================
# Helpers
# =====================================================================

def _resolved(path: tuple[str, ...], source: str) -> ResolvedModule:
    """A ``ResolvedModule`` from source text, via a real temp file.

    ``delete=False`` + explicit unlink is the Windows-safe pattern (an open
    ``NamedTemporaryFile`` cannot be reopened there).
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        return ResolvedModule(
            path=path, file_path=Path(fp),
            program=transform(parse_file(fp)), source=source,
        )
    finally:
        os.unlink(fp)


def _verify_mod(source: str, modules: list[ResolvedModule]) -> VerifyResult:
    """Type-check and verify *source* against *modules*, asserting check-clean.

    Check-clean is the premise of every provenance test here: a fixture that
    fails to type-check would pass an ``errors == []`` assertion trivially.
    """
    prog = parse_to_ast(source)
    diags = typecheck(prog, source, resolved_modules=modules)
    check_errors = [d for d in diags if d.severity == "error"]
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verify(prog, source, resolved_modules=modules)


def _codes(result: VerifyResult) -> set[str]:
    return {d.error_code for d in result.diagnostics if d.severity == "error"}


def _compile_mod(source: str, modules: list[ResolvedModule]) -> object:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        return compile(
            transform(parse_file(fp)), source=source, file=fp,
            resolved_modules=modules,
        )
    finally:
        os.unlink(fp)


def _slot_refs(node: object) -> list[str]:
    """Every ``@Type<args>.n`` in *node*, in walk order, as source spellings."""
    out: list[str] = []

    def walk(v: object) -> None:
        if isinstance(v, ast.SlotRef):
            args = (
                "<" + ", ".join(
                    getattr(a, "name", "?") for a in v.type_args
                ) + ">" if v.type_args else ""
            )
            out.append(f"@{v.type_name}{args}.{v.index}")
            return
        if isinstance(v, ast.Node):
            for fld in v.__dataclass_fields__:
                if fld != "span":
                    walk(getattr(v, fld))
            return
        if isinstance(v, (tuple, list)):
            for item in v:
                walk(item)

    walk(node)
    return out


# =====================================================================
# Finding 1a — an imported callee's contract renders in ITS module
# =====================================================================

# `Cnt` names DIFFERENT bodies in the library and in the importer, so a
# contract rendered in the wrong namespace lands on the wrong parameter.
_CONFLICT_LIB = """\
module clib;

type Cnt = Nat;

public fn need3(@Option<Int>, @Option<Cnt> -> @Int)
  requires(@Option<Int>.0 == Some(3))
  ensures(true)
  effects(pure)
{
  0
}
"""


class TestImportedCalleeContractEnv:
    """The call obligation is rendered in the CALLEE's namespace (#1208).

    Rendered in the importer's, ``@Option<Int>`` and ``@Option<Cnt>`` either
    merge into one stack (the precondition attaches to the wrong argument, and
    the obligation VANISHES) or split one the callee merged (a spurious E501).
    Reviewer probes ``reviewA2/p10*`` (the vanish) and ``reviewA2/p11*`` (the
    spurious error).
    """

    def test_violated_precondition_still_reported_bare_import(self) -> None:
        """probe p10: the E501 must not vanish because the importer renames.

        The library's ``@Option<Cnt>`` is ``Option<Nat>``, so its
        ``@Option<Int>.0`` is parameter 1 and the call passes ``Some(9)`` —
        a violation.  Under the importer's ``type Cnt = Int`` both parameters
        render ``Option<Int>``, ``@Option<Int>.0`` resolves to parameter 2
        (``Some(3)``), and the precondition proves: a false Tier-1.
        """
        result = _verify_mod("""\
import clib(need3);

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need3(Some(9), Some(3))
}
""", [_resolved(("clib",), _CONFLICT_LIB)])
        assert "E501" in _codes(result), (
            "the callee's precondition obligation was lost to the importer's "
            f"alias namespace; got {_codes(result)}"
        )

    def test_violated_precondition_still_reported_qualified_call(self) -> None:
        """probe p8q: a ``mod::fn`` call takes the same registry, same fix."""
        result = _verify_mod("""\
import clib;

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  clib::need3(Some(9), Some(3))
}
""", [_resolved(("clib",), _CONFLICT_LIB)])
        assert "E501" in _codes(result), (
            f"qualified call lost its precondition obligation: {_codes(result)}"
        )

    def test_satisfied_precondition_is_not_spuriously_reported(self) -> None:
        """probe p11: the mirror — a CORRECT program must stay clean.

        Same shape, but the argument the callee's contract names IS the one it
        constrains.  Under the importer's env the reference resolved onto the
        other parameter and the call E501'd for no reason.
        """
        result = _verify_mod("""\
import clib(pick);

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Some(7), Some(3))
}
""", [_resolved(("clib",), """\
module clib;

type Cnt = Nat;

public fn pick(@Option<Int>, @Option<Cnt> -> @Int)
  requires(@Option<Int>.0 == Some(7))
  ensures(true)
  effects(pure)
{
  0
}
""")])
        assert not _codes(result), (
            f"correct cross-module call spuriously rejected: {_codes(result)}"
        )

    def test_control_no_alias_conflict_still_reports(self) -> None:
        """Control: with no same-named alias the two envs agree, and always did.

        Present so a fix that merely disabled the cross-module obligation would
        fail here rather than pass the two probes above by omission.
        """
        result = _verify_mod("""\
import dlib(need3);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need3(Some(9), Some(3))
}
""", [_resolved(("dlib",), """\
module dlib;

public fn need3(@Option<Int>, @Option<Nat> -> @Int)
  requires(@Option<Int>.0 == Some(3))
  ensures(true)
  effects(pure)
{
  0
}
""")])
        assert "E501" in _codes(result)


# =====================================================================
# Finding 1b — an imported generic clones in ITS module's namespace
# =====================================================================

_GENERIC_LIB = """\
module blib;

type Cnt = Int;

public forall<T> fn twolen(@Array<Cnt>, @Array<T> -> @Nat)
  requires(array_length(@Array<T>.0) == 2)
  ensures(@Nat.result == 2)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
"""

_GENERIC_MAIN = """\
import blib(twolen);

type Cnt = Nat;

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  twolen(array_range(0, 5), array_range(0, 2))
}
"""


class TestImportedGenericCloneEnv:
    """The verifier clones an imported generic in the DEFINING module's env.

    Codegen already does (``_clone_alias_env``, #1208).  While the verifier did
    not, the two sides monomorphized the same template into different functions
    — the De Bruijn recount permutes the parameters — so the verifier proved a
    body codegen never emitted.  Reviewer probes ``reviewA2/p3*`` (verify green,
    trap at run) and ``reviewA2/pin_clone.py`` (the recount itself).
    """

    def test_lying_imported_generic_contract_is_an_honest_e500(self) -> None:
        """The false Tier-1 this gap produced, in its smallest form.

        In ``blib``'s namespace ``@Array<Cnt>`` is ``Array<Int>`` and
        ``@Array<T>`` is not, so ``requires`` constrains parameter 2 while the
        body reads parameter 1 — the ``ensures`` is FALSE.  In the importer's
        (``type Cnt = Nat``) the recount merges both references onto one slot,
        the contract looks self-consistent, and it verifies clean while the
        emitted clone violates its postcondition at run time.
        """
        result = _verify_mod(_GENERIC_MAIN, [_resolved(("blib",), _GENERIC_LIB)])
        assert "E500" in _codes(result), (
            "an imported generic's lying postcondition proved clean — the "
            f"clone was verified in the importer's namespace; got {_codes(result)}"
        )

    def test_verifier_clone_matches_codegen_clone(self) -> None:
        """The direct recount differential (``pin_clone.py``, in-tree).

        Compares the slot references the VERIFIER's monomorphization produces
        for an imported generic against the ones CODEGEN produces for the same
        template at the same instantiation.  A unit test on either side alone
        cannot see the desync — that is the whole point of a differential.
        """
        module = _resolved(("blib",), _GENERIC_LIB)
        prog = parse_to_ast(_GENERIC_MAIN)
        typecheck(prog, _GENERIC_MAIN, resolved_modules=[module])

        clones: dict[str, list[str]] = {}
        original = Monomorphizer.monomorphize_fn

        def record(side: str):
            def patched(self, decl, concrete_types, alias_env=None):
                out = original(self, decl, concrete_types, alias_env)
                if decl.name == "twolen":
                    clones.setdefault(side, _slot_refs(out))
                return out
            return patched

        try:
            Monomorphizer.monomorphize_fn = record("verifier")  # type: ignore[method-assign]
            verify(prog, _GENERIC_MAIN, resolved_modules=[module])
            Monomorphizer.monomorphize_fn = record("codegen")  # type: ignore[method-assign]
            _compile_mod(_GENERIC_MAIN, [module])
        finally:
            Monomorphizer.monomorphize_fn = original  # type: ignore[method-assign]

        assert "verifier" in clones and "codegen" in clones, (
            f"both sides must clone the imported generic; saw {sorted(clones)}"
        )
        assert clones["verifier"] == clones["codegen"], (
            "the verifier and codegen monomorphize the imported generic into "
            f"DIFFERENT bodies: {clones['verifier']} vs {clones['codegen']}"
        )

    def test_imported_generic_run_agrees_with_verify(self) -> None:
        """The runtime oracle for the same clone.

        The emitted clone's own postcondition guard fails, which is what the
        E500 above now predicts — verify and run agree on the same body.

        A CONTROL, not a proving test: codegen always named this clone in the
        defining module's env, so the trap is green before and after.  Its job
        is to show the E500 is HONEST — that the verifier now agrees with the
        emitted code rather than merely reporting more.
        """
        module = _resolved(("blib",), _GENERIC_LIB)
        result = _compile_mod(_GENERIC_MAIN, [module])
        errors = [
            d for d in result.diagnostics  # type: ignore[attr-defined]
            if d.severity == "error"
        ]
        assert not errors, f"unexpected codegen errors: {errors}"
        try:
            execute(result, fn_name="main")  # type: ignore[arg-type]
        except RuntimeError as exc:
            assert "ensures" in str(exc) or "ostcondition" in str(exc), (
                f"expected the clone's postcondition guard to fail: {exc}"
            )
        else:  # pragma: no cover — a pass here would contradict the E500
            raise AssertionError(
                "the emitted clone satisfied a postcondition the verifier "
                "reports as violated: verify and run disagree"
            )


# =====================================================================
# Finding 1c — a `forall` variable shadows a same-named module alias
# =====================================================================

class TestForallShadowNarrowing:
    """``forall<T>`` shadows ``type T = …`` everywhere the signature renders.

    The checker binds the type parameter first (``_check_fn`` step 1), so
    ``forall<T> fn f(@Option<T>, @Option<Int>)`` binds TWO stacks for it.  Every
    consumer that rendered the same signature against the bare module env saw
    ONE, and silently resolved references onto the wrong parameter.  Reviewer
    probes ``reviewA1/m01``, ``m03`` and ``v01``.
    """

    _M01 = """\
type T = Int;

public forall<T> fn pick(@Option<T>, @Option<Int> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<T>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(pick(Some(11), Some(22)), 0)
}
"""

    def test_mono_clone_reads_the_parameter_the_checker_bound(self) -> None:
        """probe m01: ``@Option<T>.0`` is parameter 1 — the run must give 11.

        Without the narrowing the recount saw one ``Option<Int>`` stack, kept
        the index, and the clone read parameter 2: 22.
        """
        assert _run(self._M01) == 11

    def test_mono_clone_control_without_shadowing(self) -> None:
        """probe m01_control: the same program with the alias renamed.

        Green before and after — it is here so the assertion above is known to
        be about the SHADOWING and not about De Bruijn resolution generally.
        """
        assert _run(self._M01.replace("type T = Int;", "type TT = Int;")) == 11

    def test_let_binder_inside_a_generic_body(self) -> None:
        """probe m03: the same collapse reached through a body ``let``.

        The ``let @Option<Int>`` interposes a binding that only counts for the
        reference when the two stacks are (wrongly) one.
        """
        assert _run("""\
type T = Int;

public forall<T> fn pick(@Option<T> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = Some(99);
  @Option<T>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(pick(Some(11)), 0)
}
""") == 11

    _V01 = """\
type T = Int;

public forall<T> fn f(@Array<T>, @Array<Int> -> @Nat)
  requires(array_length(@Array<T>.0) == 3 && array_length(@Array<Int>.0) == 7)
  ensures(@Nat.result == 999)
  effects(pure)
{
  array_length(@Array<T>.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([1, 2, 3], [1, 2, 3, 4, 5, 6, 7])
}
"""

    def test_verifier_does_not_prove_from_collapsed_premises(self) -> None:
        """probe v01: a FALSE Tier-1, because the premises became unsatisfiable.

        The two ``requires`` conjuncts constrain different parameters.  Collapse
        them onto one slot and it must have length 3 AND 7 — from which anything
        follows, including the false ``ensures(@Nat.result == 999)``.
        """
        prog = parse_to_ast(self._V01)
        assert not [
            d for d in typecheck(prog, self._V01) if d.severity == "error"
        ]
        result = verify(prog, self._V01)
        codes = {d.error_code for d in result.diagnostics if d.severity == "error"}
        assert "E500" in codes, (
            "a postcondition that is false for every input proved at Tier 1: "
            f"the premises collapsed onto one slot; got {codes}"
        )

    def test_verifier_control_without_shadowing(self) -> None:
        """probe v01_control: the same program, alias renamed — E500 both ways."""
        src = self._V01.replace("type T = Int;", "type TT = Int;")
        prog = parse_to_ast(src)
        result = verify(prog, src)
        assert "E500" in {
            d.error_code for d in result.diagnostics if d.severity == "error"
        }

    def test_uninstantiated_generic_template_reads_parameter_one(self) -> None:
        """Codegen emits (and EXPORTS) the template, so it must name it right.

        A never-instantiated generic still reaches ``_compile_fn``; under the
        bare module env its two ``Option`` parameters merged and the exported
        body returned the second one.
        """
        wat = _compile_ok("""\
type T = Int;

public forall<T> fn pick(@Option<T>, @Option<Int> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<T>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
""").wat
        body = wat.split("(func $pick")[1].split("(func ")[0]
        assert "local.get 0" in body and "local.get 1" not in body, (
            "the exported template returns the wrong parameter:\n" + body
        )


# =====================================================================
# Finding 1d — the tester's SmtContext gets the NARROWED scope
# =====================================================================

class TestTesterSmtScope:
    """``_generate_inputs`` keys its slot names in the function's own scope, so
    the ``SmtContext`` that RESOLVES those names must hold the same scope.

    Handed the un-narrowed module env, ``_translate_slot_ref`` looks a
    ``requires`` clause's ``@T.n`` up under a key the bind side never pushed —
    latent until a ``forall`` variable shadows a same-named module alias.
    """

    def test_smt_context_holds_the_narrowed_scope(self) -> None:
        from vera import naming
        from vera.smt import SmtContext
        from vera.tester import _generate_inputs
        from vera.types import INT

        src = """\
type T = Int;

public forall<T> fn f(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
        prog = parse_to_ast(src)
        decl = next(
            tld.decl for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
        )
        env = naming.alias_env_from_declarations(prog.declarations)
        seen: list[object] = []
        original = SmtContext.__init__

        def patched(self, *args, **kwargs):
            original(self, *args, **kwargs)
            seen.append(self._alias_env)

        try:
            SmtContext.__init__ = patched  # type: ignore[method-assign]
            _generate_inputs(decl, [INT], 1, env)
        finally:
            SmtContext.__init__ = original  # type: ignore[method-assign]

        assert seen, "the generator must build an SmtContext"
        assert "T" in seen[0].type_params, (  # type: ignore[attr-defined]
            "the tester handed SmtContext the un-narrowed module env, so a "
            "reference under a shadowed alias resolves against a scope the "
            "bind side never used"
        )


# =====================================================================
# The verifier's per-module registries
# =====================================================================

class TestVerifierModuleAliasEnvs:
    """``ContractVerifier`` builds its OWN per-module naming envs (#1208).

    ``CheckArtifacts`` carries none: ``vera verify`` runs with module-artifact
    collection off, so an artifact-sourced table would have been empty exactly
    where the cross-module obligations need it.  This pins that the verifier's
    own registration supplies them.
    """

    def test_module_env_is_the_modules_own_namespace(self) -> None:
        module = _resolved(("clib",), _CONFLICT_LIB)
        prog = parse_to_ast("""\
import clib(need3);

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need3(Some(9), Some(3))
}
""")
        v = ContractVerifier(resolved_modules=[module])
        v.register_program(prog)
        assert ("clib",) in v._module_alias_envs
        mod_env = v._module_alias_envs[("clib",)]
        assert mod_env.aliases["Cnt"].name == "Nat"  # type: ignore[union-attr]
        assert v._alias_env.aliases["Cnt"].name == "Int"  # type: ignore[union-attr]

    def test_check_artifacts_carry_no_per_module_env(self) -> None:
        """The dead artifact field is gone, not merely unread (#1208).

        Two consumers need a per-module env and each builds its own from a
        namespace it already holds — codegen from its flat alias maps, the
        verifier from its own registration.  A third, unread copy on
        ``CheckArtifacts`` was one more table to drift.
        """
        from vera.checker.core import CheckArtifacts

        assert "module_alias_envs" not in CheckArtifacts.__dataclass_fields__

    def test_generic_origin_records_the_defining_module(self) -> None:
        module = _resolved(("blib",), _GENERIC_LIB)
        prog = parse_to_ast(_GENERIC_MAIN)
        v = ContractVerifier(resolved_modules=[module])
        v.register_program(prog)
        assert v._generic_origins.get("twolen") == ("blib",)
        assert v._alias_env_for_generic("twolen") is v._module_alias_envs[("blib",)]
        # A main-file generic has no origin and keeps this program's env.
        assert v._alias_env_for_generic("no_such_generic") is v._alias_env
