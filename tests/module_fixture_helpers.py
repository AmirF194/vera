"""Shared builders for multi-module test fixtures (#1228).

Six test files carried independent copies of the same two patterns for
turning a source string into a :class:`~vera.resolver.ResolvedModule`.
They are two patterns, not one, and which is correct depends on whether
the code under test reads the module's ``file_path``:

``resolved_module`` — writes the source to a real temporary file and
parses THAT, so ``file_path`` names a file the pipeline can open.
Required by anything that reports a location in the module, re-reads it,
or keys on a real path.

``fake_resolved_module`` — parses the source in memory and labels it
``/fake/<path>.vera``.  Cheaper, and correct wherever the file is never
opened; the fake path is deliberately non-existent so a consumer that
DOES open it fails loudly instead of reading something plausible.

Both are Windows-portable, per the three rules in TESTING.md's "Test
Fixture Conventions": ``delete=False`` plus a manual unlink (Windows
cannot reopen a held ``NamedTemporaryFile``), explicit
``encoding="utf-8"``, and — for callers embedding a fixture path into
Vera source — POSIX-form paths via ``Path.as_posix()``.

The temp file is unlinked as soon as parsing is done: the resulting
``ResolvedModule`` carries the parsed program and the source string, and
the compiler works off those rather than re-reading the path (PR #664
review).  One of the consolidated copies did not unlink, and leaked one
temp file per fixture it built.
"""
from __future__ import annotations

import os
import tempfile
from pathlib import Path

from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.transform import transform


def resolved_module(path: tuple[str, ...], source: str) -> ResolvedModule:
    """A ``ResolvedModule`` parsed from a real (temporary) file.

    The file exists only for the duration of the parse; ``file_path``
    keeps naming it afterwards, which is what the location-reporting
    paths need it for.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        return ResolvedModule(
            path=path,
            file_path=Path(fp),
            program=transform(parse_file(fp)),
            source=source,
        )
    finally:
        os.unlink(fp)


def fake_resolved_module(
    path: tuple[str, ...], source: str,
) -> ResolvedModule:
    """A ``ResolvedModule`` parsed in memory, labelled with a fake path.

    For tests where nothing opens the module's file.  The path is
    ``/fake/<dotted/path>.vera`` — a location that does not exist, so a
    consumer that unexpectedly opens it raises rather than succeeding
    against some other file.
    """
    return ResolvedModule(
        path=path,
        file_path=Path(f"/fake/{'/'.join(path)}.vera"),
        program=parse_to_ast(source),
        source=source,
    )
