"""Unit tests for the Python Markdown parser and renderer (§9.7.3).

Tests the pure-Python reference implementation used by the host-imported
md_parse, md_render, md_has_heading, md_has_code_block, and
md_extract_code_blocks built-in functions.
"""

import pytest

from vera.markdown import (
    MdBlockQuote,
    MdCode,
    MdCodeBlock,
    MdEmph,
    MdHeading,
    MdImage,
    MdLink,
    MdList,
    MdParagraph,
    MdStrong,
    MdTable,
    MdText,
    MdThematicBreak,
    extract_code_blocks,
    has_code_block,
    has_heading,
    parse_markdown,
    render_markdown,
)


# =====================================================================
# Parsing tests
# =====================================================================


class TestParseHeadings:
    """ATX heading parsing."""

    def test_h1(self) -> None:
        doc = parse_markdown("# Hello")
        assert len(doc.children) == 1
        h = doc.children[0]
        assert isinstance(h, MdHeading)
        assert h.level == 1
        assert h.children == (MdText("Hello"),)

    def test_h2_through_h6(self) -> None:
        for level in range(2, 7):
            doc = parse_markdown("#" * level + " Heading")
            h = doc.children[0]
            assert isinstance(h, MdHeading)
            assert h.level == level

    def test_heading_with_closing_hashes(self) -> None:
        doc = parse_markdown("## Title ##")
        h = doc.children[0]
        assert isinstance(h, MdHeading)
        assert h.level == 2
        assert h.children == (MdText("Title"),)


class TestParseCodeBlocks:
    """Fenced code block parsing."""

    def test_backtick_fence(self) -> None:
        doc = parse_markdown("```python\nprint(42)\n```")
        assert len(doc.children) == 1
        cb = doc.children[0]
        assert isinstance(cb, MdCodeBlock)
        assert cb.language == "python"
        assert cb.code == "print(42)"

    def test_tilde_fence(self) -> None:
        doc = parse_markdown("~~~\ncode\n~~~")
        cb = doc.children[0]
        assert isinstance(cb, MdCodeBlock)
        assert cb.language == ""
        assert cb.code == "code"

    def test_multiline_code(self) -> None:
        doc = parse_markdown("```\nline1\nline2\nline3\n```")
        cb = doc.children[0]
        assert isinstance(cb, MdCodeBlock)
        assert cb.code == "line1\nline2\nline3"

    def test_code_block_no_language(self) -> None:
        doc = parse_markdown("```\nstuff\n```")
        cb = doc.children[0]
        assert isinstance(cb, MdCodeBlock)
        assert cb.language == ""


class TestParseParagraphs:
    """Paragraph parsing."""

    def test_single_paragraph(self) -> None:
        doc = parse_markdown("Hello world")
        assert len(doc.children) == 1
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        assert p.children == (MdText("Hello world"),)

    def test_multiline_paragraph(self) -> None:
        doc = parse_markdown("line one\nline two")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        assert p.children == (MdText("line one line two"),)

    def test_paragraphs_separated_by_blank(self) -> None:
        doc = parse_markdown("para one\n\npara two")
        assert len(doc.children) == 2
        assert isinstance(doc.children[0], MdParagraph)
        assert isinstance(doc.children[1], MdParagraph)


class TestParseLists:
    """List parsing."""

    def test_unordered_list(self) -> None:
        doc = parse_markdown("- item 1\n- item 2\n- item 3")
        assert len(doc.children) == 1
        lst = doc.children[0]
        assert isinstance(lst, MdList)
        assert not lst.ordered
        assert len(lst.items) == 3

    def test_ordered_list(self) -> None:
        doc = parse_markdown("1. first\n2. second")
        lst = doc.children[0]
        assert isinstance(lst, MdList)
        assert lst.ordered
        assert len(lst.items) == 2

    def test_unordered_star(self) -> None:
        doc = parse_markdown("* alpha\n* beta")
        lst = doc.children[0]
        assert isinstance(lst, MdList)
        assert not lst.ordered

    def test_ordered_paren(self) -> None:
        doc = parse_markdown("1) first\n2) second")
        lst = doc.children[0]
        assert isinstance(lst, MdList)
        assert lst.ordered


class TestParseBlockQuotes:
    """Block quote parsing."""

    def test_simple_quote(self) -> None:
        doc = parse_markdown("> quoted text")
        bq = doc.children[0]
        assert isinstance(bq, MdBlockQuote)
        assert len(bq.children) == 1
        assert isinstance(bq.children[0], MdParagraph)

    def test_multiline_quote(self) -> None:
        doc = parse_markdown("> line one\n> line two")
        bq = doc.children[0]
        assert isinstance(bq, MdBlockQuote)


class TestParseTables:
    """GFM table parsing."""

    def test_simple_table(self) -> None:
        doc = parse_markdown("| A | B |\n| --- | --- |\n| 1 | 2 |")
        tbl = doc.children[0]
        assert isinstance(tbl, MdTable)
        assert len(tbl.rows) == 2  # header + 1 data row

    def test_table_multiple_rows(self) -> None:
        md = "| X | Y |\n| --- | --- |\n| a | b |\n| c | d |"
        doc = parse_markdown(md)
        tbl = doc.children[0]
        assert isinstance(tbl, MdTable)
        assert len(tbl.rows) == 3  # header + 2 data rows


class TestParseThematicBreak:
    """Thematic break / horizontal rule."""

    def test_dashes(self) -> None:
        doc = parse_markdown("---")
        assert isinstance(doc.children[0], MdThematicBreak)

    def test_asterisks(self) -> None:
        doc = parse_markdown("***")
        assert isinstance(doc.children[0], MdThematicBreak)

    def test_underscores(self) -> None:
        doc = parse_markdown("___")
        assert isinstance(doc.children[0], MdThematicBreak)


class TestParseInlines:
    """Inline element parsing."""

    def test_emphasis(self) -> None:
        doc = parse_markdown("*italic*")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        assert p.children == (MdEmph((MdText("italic"),)),)

    def test_strong(self) -> None:
        doc = parse_markdown("**bold**")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        assert p.children == (MdStrong((MdText("bold"),)),)

    def test_inline_code(self) -> None:
        doc = parse_markdown("`code`")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        assert p.children == (MdCode("code"),)

    def test_link(self) -> None:
        doc = parse_markdown("[text](url)")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        link = p.children[0]
        assert isinstance(link, MdLink)
        assert link.children == (MdText("text"),)
        assert link.url == "url"

    def test_image(self) -> None:
        doc = parse_markdown("![alt](src)")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        img = p.children[0]
        assert isinstance(img, MdImage)
        assert img.alt == "alt"
        assert img.src == "src"

    def test_mixed_inlines(self) -> None:
        doc = parse_markdown("hello *world* `code`")
        p = doc.children[0]
        assert isinstance(p, MdParagraph)
        assert len(p.children) == 4  # text, emph, text, code


class TestParseMixed:
    """Mixed document parsing."""

    def test_heading_and_paragraph(self) -> None:
        doc = parse_markdown("# Title\n\nSome text.")
        assert len(doc.children) == 2
        assert isinstance(doc.children[0], MdHeading)
        assert isinstance(doc.children[1], MdParagraph)

    def test_empty_document(self) -> None:
        doc = parse_markdown("")
        assert doc.children == ()

    def test_whitespace_only(self) -> None:
        doc = parse_markdown("   \n  \n  ")
        assert doc.children == ()


# =====================================================================
# Rendering tests
# =====================================================================


class TestRender:
    """Canonical Markdown rendering."""

    def test_heading(self) -> None:
        block = MdHeading(2, (MdText("Title"),))
        assert render_markdown(block) == "## Title"

    def test_paragraph(self) -> None:
        block = MdParagraph((MdText("Hello"),))
        assert render_markdown(block) == "Hello"

    def test_code_block(self) -> None:
        block = MdCodeBlock("python", "print(42)")
        assert render_markdown(block) == "```python\nprint(42)\n```"

    def test_thematic_break(self) -> None:
        assert render_markdown(MdThematicBreak()) == "---"

    def test_emphasis(self) -> None:
        block = MdParagraph((MdEmph((MdText("italic"),)),))
        assert render_markdown(block) == "*italic*"

    def test_strong(self) -> None:
        block = MdParagraph((MdStrong((MdText("bold"),)),))
        assert render_markdown(block) == "**bold**"

    def test_link(self) -> None:
        block = MdParagraph(
            (MdLink((MdText("click"),), "https://example.com"),),
        )
        assert render_markdown(block) == "[click](https://example.com)"

    def test_image(self) -> None:
        block = MdParagraph((MdImage("alt", "img.png"),))
        assert render_markdown(block) == "![alt](img.png)"


class TestRoundTrip:
    """Parse → render → parse round-trip property."""

    @pytest.mark.parametrize("markdown", [
        "# Hello",
        "Some text here.",
        "```python\nprint(42)\n```",
        "---",
        "- item 1\n- item 2",
        "1. first\n2. second",
        "> quoted",
        "| A | B |\n| --- | --- |\n| 1 | 2 |",
        # Multi-child containers.  Every entry above is single-line or
        # fence-only, so none of them can see a container that drops the
        # separator between its children — which the blockquote arm did
        # until v0.1.12 (#1294 review), turning two quoted paragraphs
        # into one.
        "> a\n>\n> b",
        "> a\n>\n> - b\n> - c",
        "> # H\n>\n> para\n>\n> ```py\n> x = 1\n> ```",
    ])
    def test_round_trip(self, markdown: str) -> None:
        doc = parse_markdown(markdown)
        rendered = render_markdown(doc)
        doc2 = parse_markdown(rendered)
        assert doc == doc2

    @pytest.mark.parametrize("markdown", [
        "> a\n>\n> b",
        "> a\n>\n> - b\n> - c",
        "> # H\n>\n> para\n>\n> ```py\n> x = 1\n> ```",
        "- item 1\n- item 2",
        "> quoted",
        # An empty quote is a block like any other: it has to survive
        # its own render, or a `>` in a document disappears on the
        # round trip and takes the document's block spacing with it.
        ">",
        "---\n>",
        "> a\n\n>\n\n> b",
    ])
    def test_render_is_a_fixed_point(self, markdown: str) -> None:
        """Rendering the render changes nothing.

        The ADT equality above is the property spec §9.7.3 states; this
        is the weaker string form the cross-host battery in
        ``tests/test_browser.py`` can observe.  Both are asserted here
        so a future divergence between them is visible: a renderer that
        satisfies the string form while losing structure would pass one
        and fail the other.
        """
        once = render_markdown(parse_markdown(markdown))
        twice = render_markdown(parse_markdown(once))
        assert twice == once

    @pytest.mark.parametrize(("code", "rendered"), [
        ("code", "`code`"),
        ("a`b", "``a`b``"),
        ("a``b", "```a``b```"),
        ("`x", "`` `x ``"),
        ("x`", "`` x` ``"),
        (" ", "` `"),
    ])
    def test_code_span_fence_round_trips(
        self, code: str, rendered: str,
    ) -> None:
        """A code span is fenced with one more backtick than its longest
        internal run, padded only when it starts or ends with one.

        The old rule was "two backticks and padding spaces if the
        content holds any backtick", which is right for one backtick and
        wrong for two: ``MdCode("a``b")`` rendered ``` `` a``b `` ```,
        whose closing run is the one *inside* the content, so it read
        back as a different document.

        The round trip is asserted with the span preceded by text.  A
        three-backtick fence at the *start of a line* is a block fence
        to the block parser, which is a separate collision — pinned on
        its own below rather than folded in here, so this case tests the
        inline rule and nothing else.
        """
        doc = MdParagraph((MdCode(code),))
        assert render_markdown(doc) == rendered

        embedded = MdParagraph((MdText("x "), MdCode(code)))
        line = render_markdown(embedded)
        assert line == "x " + rendered
        assert parse_markdown(line).children[0] == embedded

    def test_code_span_needing_a_triple_fence_collides_at_line_start(
        self,
    ) -> None:
        """A span whose content holds ``` `` ``` needs a three-backtick
        fence, and at the start of a line that IS a block fence.

        Measured, not assumed: the block parser matches
        ``^(`{3,}|~{3,})`` before any inline parsing happens, so the
        paragraph is read as an empty fenced code block whose language
        tag is the rest of the line.  There is no escape syntax in the
        §9.7.3 subset to write it another way, so the shape is simply
        not representable at line start — the same on both runtimes,
        since neither has anything to disagree about.  Pinned so the
        limitation is visible rather than inferred from a gap.
        """
        doc = MdParagraph((MdCode("a``b"),))
        line = render_markdown(doc)
        assert line == "```a``b```"
        assert parse_markdown(line).children[0] == MdCodeBlock("a``b```", "")

    def test_blockquote_children_are_separated(self) -> None:
        """A blockquote separates its children with a bare ``>``.

        Directly pinned, not inferred from the round trip, because the
        round trip is satisfiable in two ways and only one is right: a
        renderer could also "preserve structure" by merging the two
        paragraphs at parse time.  The bytes say which happened.
        """
        doc = MdBlockQuote((
            MdParagraph((MdText("first"),)),
            MdParagraph((MdText("second"),)),
        ))
        assert render_markdown(doc) == "> first\n>\n> second"


# =====================================================================
# Query function tests
# =====================================================================


class TestHasHeading:
    """has_heading query function."""

    def test_has_h1(self) -> None:
        doc = parse_markdown("# Title\n\nText")
        assert has_heading(doc, 1)

    def test_no_h2(self) -> None:
        doc = parse_markdown("# Title\n\nText")
        assert not has_heading(doc, 2)

    def test_nested_in_blockquote(self) -> None:
        doc = parse_markdown("> ## Quoted heading")
        assert has_heading(doc, 2)

    def test_empty_document(self) -> None:
        doc = parse_markdown("")
        assert not has_heading(doc, 1)


class TestHasCodeBlock:
    """has_code_block query function."""

    def test_has_python(self) -> None:
        doc = parse_markdown("```python\ncode\n```")
        assert has_code_block(doc, "python")

    def test_no_rust(self) -> None:
        doc = parse_markdown("```python\ncode\n```")
        assert not has_code_block(doc, "rust")

    def test_no_language(self) -> None:
        doc = parse_markdown("```\ncode\n```")
        assert has_code_block(doc, "")

    def test_empty_document(self) -> None:
        doc = parse_markdown("")
        assert not has_code_block(doc, "python")


class TestExtractCodeBlocks:
    """extract_code_blocks query function."""

    def test_single_block(self) -> None:
        doc = parse_markdown("```python\nprint(1)\n```")
        assert extract_code_blocks(doc, "python") == ["print(1)"]

    def test_multiple_blocks(self) -> None:
        md = "```python\nprint(1)\n```\n\n```python\nprint(2)\n```"
        doc = parse_markdown(md)
        result = extract_code_blocks(doc, "python")
        assert result == ["print(1)", "print(2)"]

    def test_filter_by_language(self) -> None:
        md = "```python\npy\n```\n\n```rust\nrs\n```"
        doc = parse_markdown(md)
        assert extract_code_blocks(doc, "python") == ["py"]
        assert extract_code_blocks(doc, "rust") == ["rs"]

    def test_no_matches(self) -> None:
        doc = parse_markdown("```python\ncode\n```")
        assert extract_code_blocks(doc, "java") == []

    def test_empty_document(self) -> None:
        doc = parse_markdown("")
        assert extract_code_blocks(doc, "python") == []
