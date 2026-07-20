"""Shared lexical scanning for Vera source text.

The single comment scanner that both the parser's pre-lex pass and the
formatter's comment extraction are derived from.

Vera's block comments **nest** (spec 1.3): a ``{-`` inside a block
comment opens a nested comment that must be closed by its own ``-}``.
A regular expression cannot express balanced delimiters at all, so
nesting is resolved here, once, by counting depth.

#1112 arose precisely because two scanners disagreed: the formatter
counted depth correctly (and ``tests/test_formatter.py`` asserted it),
while the grammar's ``%ignore /\\{-[\\s\\S]*?-\\}/`` closed at the
*first* ``-}``.  The same text was therefore a single nested comment to
``vera fmt`` and a syntax error to ``vera check``.  Deriving every
consumer from one scan makes that drift impossible by construction.

This module deliberately imports nothing from ``vera.parser`` or
``vera.formatter`` — the formatter already imports the parser, so a
shared helper has to sit below both.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = ["CommentSpan", "scan_comments", "blank_block_comments"]


@dataclass(frozen=True)
class CommentSpan:
    """A comment's extent in the source text.

    ``start``/``end`` are character offsets (``end`` exclusive), so a
    consumer can slice or blank the exact region without rescanning.
    ``terminated`` is False for a block comment whose nesting never
    returns to depth zero, or an annotation comment with no ``*/`` —
    both run to end of input.
    """

    kind: str          # "line" | "block" | "annotation"
    start: int
    end: int
    terminated: bool


def scan_comments(source: str) -> list[CommentSpan]:
    """Every comment span in ``source``, in source order.

    String literals are skipped (with backslash escapes honoured) so a
    ``{-`` or ``--`` inside a string is not mistaken for a comment
    opener.  Because the scan is strictly left-to-right, a delimiter
    inside an earlier comment is likewise consumed by that comment
    rather than opening a new one.
    """
    spans: list[CommentSpan] = []
    src = source
    n = len(src)
    pos = 0

    while pos < n:
        # Line comment — runs to end of line.
        if src[pos:pos + 2] == "--":
            end = src.find("\n", pos)
            if end == -1:
                end = n
            spans.append(CommentSpan("line", pos, end, True))
            pos = end
            continue

        # Block comment — nestable, so count depth rather than
        # scanning for the first closer.
        if src[pos:pos + 2] == "{-":
            depth = 1
            j = pos + 2
            while j < n and depth > 0:
                if src[j:j + 2] == "{-":
                    depth += 1
                    j += 2
                elif src[j:j + 2] == "-}":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            spans.append(CommentSpan("block", pos, j, depth == 0))
            pos = j
            continue

        # Annotation comment — does not nest (spec 1.3).
        if src[pos:pos + 2] == "/*":
            close = src.find("*/", pos + 2)
            terminated = close != -1
            end = n if close == -1 else close + 2
            spans.append(CommentSpan("annotation", pos, end, terminated))
            pos = end
            continue

        # String literal — skip so delimiters inside it never match.
        if src[pos] == '"':
            j = pos + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            pos = j + 1
            continue

        pos += 1

    return spans


def blank_block_comments(source: str) -> tuple[str, int | None]:
    """``source`` with block comments replaced by spaces.

    Every non-newline character of a block comment becomes a space and
    newlines are kept, so the result is **byte-for-byte the same length
    and line structure** as the input.  That is load-bearing: the
    grammar is parsed with ``propagate_positions=True``, every
    diagnostic quotes a line and column, and the formatter attaches
    comments by source span — all of which would shift if comments were
    deleted rather than blanked.

    Returns ``(blanked_source, unterminated_line)`` where
    ``unterminated_line`` is the 1-based line of the first block comment
    that never closes, or ``None`` when every block comment is balanced.
    The caller reports that as a diagnostic; leaving it to the grammar
    would surface as a confusing "unexpected end of input" far from the
    offending ``{-``.
    """
    spans = scan_comments(source)
    chars = list(source)
    unterminated: int | None = None

    for span in spans:
        if span.kind != "block":
            continue
        if not span.terminated and unterminated is None:
            unterminated = source.count("\n", 0, span.start) + 1
        for i in range(span.start, span.end):
            if chars[i] != "\n":
                chars[i] = " "

    return "".join(chars), unterminated
