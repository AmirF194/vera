"""Shared builders for multi-module test fixtures (#1228).

Six test files carried independent copies of the same two patterns for
turning a source string into a :class:`~vera.resolver.ResolvedModule`.
They are two patterns, not one, and what separates them is PARSE
PROVENANCE — not whether a file survives the call, because neither
leaves one:

``resolved_module`` — writes the source to a real temporary file, parses
THAT (:func:`~vera.parser.parse_file`), and deletes the file before
returning.  The module carries real-file provenance: its program came
through the on-disk parse path, and ``file_path`` is a well-formed
absolute path of the shape the pipeline sees in production.

``fake_resolved_module`` — parses the source in memory
(:func:`~vera.parser.parse_to_ast`) and labels the module
``/fake/<path>.vera``.  Cheaper, and correct wherever the parse path
does not matter; the label is conspicuously synthetic, so a path that
turns up in a failure message is recognisable as a fixture's rather than
a real module's.

**Neither builder leaves a file on disk, and neither ``file_path`` can
be opened after the call returns.**  That is safe because nothing
downstream re-reads it: ``compile()`` and the checker work off the
parsed program and the in-memory ``source`` string and keep the path
only as a diagnostic label (PR #664 review — the one ``read_text`` under
``vera/codegen/`` is the ``IO.read_file`` HOST binding, which reads
whatever path the compiled program asks for at run time, not the
module's).  A test that needs a module file to EXIST while it runs must
therefore write one itself; these builders will not provide it.
:func:`test_neither_builder_leaves_a_file_behind` pins the contract.

Both are Windows-portable, per the rules in TESTING.md's "Test Fixture
Conventions": ``delete=False`` plus a manual unlink (Windows cannot
reopen a held ``NamedTemporaryFile``), explicit ``encoding="utf-8"``,
and — for callers embedding a fixture path into Vera source —
POSIX-form paths via ``Path.as_posix()``.

One of the consolidated copies did not unlink at all, and leaked one
temp file per fixture it built.
"""
from __future__ import annotations

import tempfile
from pathlib import Path

from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.transform import transform


def resolved_module(path: tuple[str, ...], source: str) -> ResolvedModule:
    """A ``ResolvedModule`` parsed from a real (temporary) file.

    The file exists for the parse and is deleted before this returns, so
    ``file_path`` names a path that is no longer there.  What the module
    keeps is the PROVENANCE — a program that came through the on-disk
    parse path, under a realistic absolute path — which is all any
    consumer needs, since none of them reopens it (see the module
    docstring).
    """
    # Creation, then ONE cleanup site covering every path.  Two rules
    # meet here and the obvious arrangement satisfies only one of them:
    # the file must be removed even if the WRITE fails (`delete=False`
    # means it outlives the context manager), and on Windows it cannot
    # be removed while the handle is open at all — an unlink in an
    # `except` inside the `with` is WinError 32 there, which is
    # TESTING.md's first fixture rule (PR #1282 review, and its own CI).
    # So the name is captured and the `try` entered before anything that
    # can fail, the `with` closes the handle on its way out however it
    # leaves, and the `finally` unlinks after it — never during.
    tmp = tempfile.NamedTemporaryFile(  # noqa: SIM115 — closed by the `with`
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    )
    fp = tmp.name
    try:
        with tmp as f:
            f.write(source)
            f.flush()
        return ResolvedModule(
            path=path,
            file_path=Path(fp),
            program=transform(parse_file(fp)),
            source=source,
        )
    finally:
        Path(fp).unlink(missing_ok=True)


def fake_resolved_module(
    path: tuple[str, ...], source: str,
) -> ResolvedModule:
    """A ``ResolvedModule`` parsed in memory, labelled with a fake path.

    For tests where the parse path does not matter.  The label is
    ``/fake/<dotted/path>.vera`` — conspicuously synthetic, so a path
    appearing in a failure message is recognisable as a fixture's.  Like
    :func:`resolved_module` it leaves nothing on disk; the difference
    between them is where the program was parsed from, not whether the
    file survives.
    """
    return ResolvedModule(
        path=path,
        file_path=Path(f"/fake/{'/'.join(path)}.vera"),
        program=parse_to_ast(source),
        source=source,
    )
