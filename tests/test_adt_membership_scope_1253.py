"""#1253: codegen's ADT membership is the module's, not the whole program's.

Codegen's `_adt_layouts` is one map across every absorbed namespace, and
the naming environment's `data_types` set was derived from all of it.  So
inside `_module_alias_scope(blib)` a sibling module's ADTs were still
members of `blib`'s namespace — while the checker registers each module in
isolation and never sees them.  The two sides then disagree about what a
NAME MEANS, which is the #1213 disease as a membership question:

    blib:  fn bcount(@Array<Float>, @Array<Int> -> @Int)
    checker slot table:  ['Array<?>', 'Array<Int>']
    codegen slot table:  ['Array<Float>', 'Array<Int>']

with `Float` an ADT `alib` declares and `blib` never imports.  Membership
now derives from the owning namespace plus that module's OWN imports —
the same own-imports discipline #1225 established on the verifier side —
and honours the checker's public-only view of an import, so a private
sibling ADT is as opaque to codegen as it is to the checker.

The proving check is a DIFFERENTIAL over the two slot tables, not an
assertion on either: both sides agreeing on the WRONG name would satisfy
a one-sided check, so each case also pins the value the checker derives.
The positive control — an ADT the module does import — is green before
and after, which is what stops the scoping from being a blanket erasure
of cross-module ADTs rather than the visibility rule it implements.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from vera import ast, naming
from vera.checker.core import TypeChecker
from vera.codegen.core import CodeGenerator
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.transform import transform

# `Float` is not a Vera primitive (the primitive is `Float64`), so an
# unregistered `Float` renders `?` — which is exactly what makes this pair
# distinguishing: the checker's answer for a name it does not know differs
# visibly from codegen's answer for a name it wrongly knows.
_ALIB_PUBLIC = """
public data Float {
  MkFloat(Int)
}

public fn atag(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""

_ALIB_PRIVATE = _ALIB_PUBLIC.replace("public data Float", "private data Float")

_BLIB_UNIMPORTED = """
public fn bcount(@Array<Float>, @Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
"""

_BLIB_IMPORTED = """
import alib(Float);

public fn bcount(@Array<Float>, @Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
"""

_MAIN = """
import alib(atag);
import blib(bcount);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  atag(())
}
"""


def _params(program: ast.Program, name: str) -> tuple[ast.TypeExpr, ...]:
    for tld in program.declarations:
        if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == name:
            return tld.decl.params
    raise AssertionError(f"no function {name!r} in module")


def _slot_tables(
    tmp_path: Path, files: dict[str, str], module: str, fn: str,
) -> tuple[list[str], list[str]]:
    """(checker's slot names for *fn*, codegen's) inside *module*'s namespace."""
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    mods = ModuleResolver(tmp_path).resolve_imports(program, main_path)
    mod = next(m for m in mods if m.path == (module,))
    params = _params(mod.program, fn)

    # The checker's view: the module checked as ITSELF, with its own
    # imports — the same construction `ModulesMixin._check_module_bodies`
    # uses (#1244), so this reads the environment the checker really binds
    # that module's declarations in rather than a rebuild of it.
    host = TypeChecker(resolved_modules=mods)
    scoped = TypeChecker(
        source=mod.source, file=str(mod.file_path),
        resolved_modules=host._modules_visible_to(mod),
    )
    scoped.check_program(mod.program)
    checker = [
        naming.slot_name(p, naming.alias_env_from_environment(scoped.env))
        for p in params
    ]

    # Codegen's view: the flat generator, inside the module's alias scope —
    # the scope every one of that module's bodies compiles under.
    gen = CodeGenerator(
        source=main_path.read_text(encoding="utf-8"), file=str(main_path),
    )
    gen._resolved_modules = mods
    gen._register_modules(program)
    gen._register_all(program)
    with gen._module_alias_scope((module,)):
        codegen = [naming.slot_name(p, gen._alias_env) for p in params]
    return checker, codegen


@pytest.mark.parametrize(
    ("alib", "blib", "expected"),
    [
        # The reported shape: a PUBLIC sibling ADT that `blib` never imported.
        pytest.param(
            _ALIB_PUBLIC, _BLIB_UNIMPORTED, ["Array<?>", "Array<Int>"],
            id="unimported_public_sibling",
        ),
        # The visibility dimension appended to the issue: a PRIVATE sibling
        # ADT is not importable at all, so it can never be a member anywhere
        # but its own module.
        pytest.param(
            _ALIB_PRIVATE, _BLIB_UNIMPORTED, ["Array<?>", "Array<Int>"],
            id="private_sibling",
        ),
        # The positive control — `blib` imports the ADT, so both sides see
        # it.  Green before the fix as well as after: it is what separates
        # "membership is scoped" from "cross-module ADTs are erased".
        pytest.param(
            _ALIB_PUBLIC, _BLIB_IMPORTED, ["Array<Float>", "Array<Int>"],
            id="imported_control",
        ),
    ],
)
def test_module_slot_tables_agree(
    tmp_path: Path, alib: str, blib: str, expected: list[str],
) -> None:
    """Checker and codegen render one module's signature the same way."""
    checker, codegen = _slot_tables(
        tmp_path,
        {"alib.vera": alib, "blib.vera": blib, "main.vera": _MAIN},
        "blib", "bcount",
    )
    assert checker == expected, "the checker's own answer moved"
    assert codegen == checker, (
        f"checker {checker} vs codegen {codegen}: the two sides disagree "
        f"about what the name MEANS in this module"
    )


def test_main_file_still_sees_its_own_imports(tmp_path: Path) -> None:
    """The importer's own namespace is unchanged by the scoping.

    `main` imports `Float` by name, so it is a member there — the check
    that the new membership rule reads the ENTRY program's imports too,
    rather than emptying every namespace but the modules'.
    """
    files = {
        "alib.vera": _ALIB_PUBLIC,
        "blib.vera": _BLIB_UNIMPORTED,
        "main.vera": """
import alib(atag, Float);
import blib(bcount);

public fn takes(@Array<Float> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Float>.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  atag(())
}
""",
    }
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    main_path = tmp_path / "main.vera"
    program = transform(parse_file(str(main_path)))
    mods = ModuleResolver(tmp_path).resolve_imports(program, main_path)
    gen = CodeGenerator(
        source=main_path.read_text(encoding="utf-8"), file=str(main_path),
    )
    gen._resolved_modules = mods
    gen._register_modules(program)
    gen._register_all(program)
    names = [naming.slot_name(p, gen._alias_env)
             for p in _params(program, "takes")]
    assert names == ["Array<Float>"], names
