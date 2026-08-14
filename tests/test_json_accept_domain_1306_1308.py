"""``json_parse``'s accept domain (#1306, #1308).

Vera defines its own domain for ``json_parse`` rather than inheriting
whichever one the host parser happens to implement:

    ``json_parse`` accepts exactly RFC 8259-valid text that decodes to
    finite numbers and strings of Unicode scalar values; everything
    else is a handled ``Err``, identically on both hosts, at the parse.

Two texts sit outside that domain and used to be admitted by accident on
the reference host, each by a different mechanism:

* **#1306** — a non-finite number, by either of two routes.  The
  JavaScript constants ``NaN`` / ``Infinity`` / ``-Infinity`` are
  admitted by Python's default ``parse_constant`` and refused by
  ``JSON.parse``, so the reference host accepted the text and the
  refusal landed at ``json_stringify`` instead — a *different call* on
  each host.  A syntactically valid number that OVERFLOWS (``1e999``) is
  accepted by both parsers, so that route diverged from the stated
  domain on both hosts at once, which is the harder failure to notice:
  nothing disagreed.

* **#1308** — a lone-surrogate escape (``\\ud800`` with no paired low
  surrogate).  The text is grammatically valid RFC 8259, but its decoded
  value is not a Unicode scalar sequence and so has no UTF-8 encoding.
  The reference host used to die with a raw ``UnicodeEncodeError`` from
  ``_alloc_string``; the browser's ``TextEncoder`` silently substituted
  U+FFFD.

Both refusals now happen at the parse, with one sentence per refusal
shared verbatim between ``vera/runtime/json.py`` and
``vera/browser/runtime.mjs``.  The cross-host half of this battery lives
in ``tests/test_browser.py``
(``TestBrowserJsonAcceptDomainParity1306_1308``); this file pins the
reference host and the shared sentences themselves.
"""

from __future__ import annotations

import sys

import pytest

from tests.codegen_helpers import _run_io
from tests.json_domain_helpers import (
    ERR_PREFIX,
    INT_ROUNDS_TO_INFINITY,
    MAX_FINITE_AS_INT,
    accept_domain_src,
    err,
    ok,
)
from vera.wasm.json_serde import (
    lone_surrogate_message,
    non_finite_number_message,
    non_finite_parse_message,
    first_domain_violation,
)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _parse_probe(raw_json: str) -> str:
    """Run ``json_parse(raw_json)`` on the REFERENCE host and report the arm.

    The program, the escaping and the output protocol all come from
    ``tests/json_domain_helpers``, so this battery and the cross-host one
    in ``tests/test_browser.py`` cannot drift into sending ``json_parse``
    different bytes while claiming to cover the same case.
    """
    return _run_io(accept_domain_src(raw_json))


# The four probe inputs from #1306's table, plus the two-constant case
# that pins WHICH constant names the refusal.
_NON_FINITE_CASES = [
    ("bare_nan", "NaN", "NaN"),
    ("bare_infinity", "Infinity", "Infinity"),
    ("bare_negative_infinity", "-Infinity", "-Infinity"),
    # ``json.loads`` admits the constants inside containers too, so the
    # refusal has to reach there and not just the top-level value.
    ("nan_in_array", "[NaN]", "NaN"),
    ("infinity_in_object", '{"a":Infinity}', "Infinity"),
    ("negative_infinity_in_object", '{"a":-Infinity}', "-Infinity"),
    # First in document order names the refusal — the order
    # ``parse_constant`` is called in, and the order the browser's
    # twin scan finds them in.
    ("first_of_two_wins", "[NaN,Infinity]", "NaN"),
]

# Positions × escape casings for #1308.  The check has to cover keys as
# well as values, at any nesting depth, and must not care how the user
# spelled the hex digits.
_LONE_SURROGATE_CASES = [
    ("value_lower", '{"k":"a\\ud800b"}', 0xD800),
    ("value_upper", '{"k":"a\\uD800b"}', 0xD800),
    ("value_low_surrogate", '{"k":"a\\udc00b"}', 0xDC00),
    ("value_low_surrogate_upper", '{"k":"a\\uDC00b"}', 0xDC00),
    ("key", '{"a\\ud800b":1}', 0xD800),
    ("key_upper", '{"a\\uD800b":1}', 0xD800),
    ("array_element", '["a\\ud800b"]', 0xD800),
    ("nested_object", '{"o":{"k":"a\\ud800b"}}', 0xD800),
    ("nested_array_in_object", '{"o":[1,"a\\ud800b"]}', 0xD800),
    ("top_level_string", '"a\\ud800b"', 0xD800),
    # High surrogate followed by something that is NOT a low surrogate:
    # the pair-aware scan must not treat the next unit as a partner.
    ("high_then_ascii_escape", '{"k":"\\ud800\\u0041"}', 0xD800),
    # High surrogate followed by another high surrogate.
    ("high_then_high", '{"k":"\\ud800\\ud800"}', 0xD800),
    # Low surrogate FIRST, then a well-formed pair — the leading unit is
    # lone even though a valid pair follows it.
    ("low_then_valid_pair", '{"k":"\\udc00\\ud83d\\ude00"}', 0xDC00),
]

# Controls: paired surrogates encode real astral characters and MUST
# still parse.  This is the boundary the #1308 check must not overshoot.
_PAIRED_SURROGATE_CASES = [
    ("paired_value", '{"k":"a\\ud83d\\ude00b"}', '{"k":"a\U0001F600b"}'),
    ("paired_value_upper", '{"k":"a\\uD83D\\uDE00b"}', '{"k":"a\U0001F600b"}'),
    ("paired_key", '{"a\\ud83d\\ude00b":1}', '{"a\U0001F600b":1}'),
    ("paired_array_element", '["\\ud83d\\ude00"]', '["\U0001F600"]'),
    # Two pairs back to back: the scan must consume each pair whole and
    # not read the low of the first beside the high of the second.
    ("two_pairs", '["\\ud83d\\ude00\\ud83d\\ude80"]', '["\U0001F600\U0001F680"]'),
    # A pair at the very end of the string — the "is there a next unit?"
    # bound is where an off-by-one turns a valid pair into a lone high.
    ("pair_at_end", '{"k":"ab\\ud83d\\ude00"}', '{"k":"ab\U0001F600"}'),
    # The literal (non-escaped) astral character, for good measure.
    ("literal_astral", '{"k":"\U0001F600"}', '{"k":"\U0001F600"}'),
]

# Controls: valid documents whose behaviour must be untouched by either
# refusal.  ``"NaN"`` as a *string value* is ordinary JSON.
_VALID_CASES = [
    ("null", "null", "null"),
    ("number", "1.5", "1.5"),
    ("negative_number", "-1.5", "-1.5"),
    ("nan_as_string_value", '{"k":"NaN"}', '{"k":"NaN"}'),
    ("infinity_as_string_value", '{"k":"Infinity"}', '{"k":"Infinity"}'),
    ("nan_as_key", '{"NaN":1}', '{"NaN":1}'),
    ("object_and_array", '{"a":1,"b":[true,null]}', '{"a":1,"b":[true,null]}'),
    ("escaped_backslash_u", '{"k":"\\\\ud800"}', '{"k":"\\\\ud800"}'),
]


# ---------------------------------------------------------------------------
# #1306 — the JavaScript non-finite constants
# ---------------------------------------------------------------------------


class TestNonFiniteParseRefusal1306:
    """``NaN`` / ``Infinity`` / ``-Infinity`` are refused at the parse.

    Before the fix the reference host parsed all of these into a
    ``JNumber`` and the program only failed later, at ``json_stringify``
    — and then as a raw Python traceback (#1302), not an ``Err``.  The
    browser refused at the parse all along, so the two hosts disagreed
    about *which call* rejects a non-finite value.
    """

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "name"),
        _NON_FINITE_CASES,
        ids=[c[0] for c in _NON_FINITE_CASES],
    )
    def test_refused_with_the_shared_sentence(
        self, case_id: str, raw_json: str, name: str,
    ) -> None:
        assert _parse_probe(raw_json) == err(non_finite_parse_message(name))

    def test_message_names_the_constant_and_the_remedy(self) -> None:
        """Guards the guard: the sentence has to carry both halves.

        A message that named the constant but not what to do about it
        would satisfy an equality assertion against itself while telling
        the user nothing — the assertions above compare the production
        sentence with itself, so the *content* needs its own check.
        """
        msg = non_finite_parse_message("NaN")
        assert "NaN" in msg
        assert "RFC 8259" in msg
        assert "json_parse:" in msg
        # The remedy half, per the diagnostic house style.
        assert "quote" in msg or "null" in msg

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _VALID_CASES,
        ids=[c[0] for c in _VALID_CASES],
    )
    def test_valid_documents_are_unaffected(
        self, case_id: str, raw_json: str, expected: str,
    ) -> None:
        assert _parse_probe(raw_json) == ok(expected)

    def test_malformed_text_keeps_the_host_parser_message(self) -> None:
        """The refinement must not swallow ordinary syntax errors.

        Only the non-finite constants get the shared sentence; text that
        is malformed for any other reason still reports whatever the
        host parser said, which is the pre-existing (and deliberately
        host-native) behaviour for syntax errors.
        """
        out = _parse_probe("{not json")
        assert out.startswith(ERR_PREFIX)
        assert non_finite_parse_message("NaN") not in out
        assert "json_parse:" not in out

    @pytest.mark.parametrize(
        ("case_id", "raw_json"),
        [
            # Python's scanner calls ``parse_constant`` the moment it
            # sees the token, so a hook that RAISED would report the
            # non-finite sentence for this — while the browser, which
            # decides by substituting and re-parsing, reported a syntax
            # error.  The recording hook asks the browser's question.
            ("constant_prefix", "[Infinity_x]"),
            ("nan_prefix", "[NaNx]"),
            # A constant in a key position: neither parser gets far
            # enough to consider it a value.
            ("constant_as_bare_key", "{Infinity:1}"),
            # A sign the constant cannot take.  RFC 8259 gives `-` to
            # numbers, and neither host's parser reads `-NaN` as
            # anything at all; a scan matching the token wherever it
            # appeared would find `NaN` at offset 1 and claim the
            # domain had refused it.
            ("signed_nan", "-NaN"),
            ("signed_nan_in_array", "[-NaN]"),
            # The mirror-image sign error, which no token begins with.
            ("plus_infinity", "+Infinity"),
            # Case matters: the constants are spelled exactly one way.
            ("lowercase_infinity", "infinity"),
            ("lowercase_nan", "nan"),
            ("constant_suffix", "-Infinityx"),
        ],
        ids=["constant_prefix", "nan_prefix", "constant_as_bare_key",
             "signed_nan", "signed_nan_in_array", "plus_infinity",
             "lowercase_infinity", "lowercase_nan", "constant_suffix"],
    )
    def test_a_constant_lookalike_is_not_reported_as_non_finite(
        self, case_id: str, raw_json: str,
    ) -> None:
        """The shared sentence is for text whose ONLY defect is a constant.

        Text that is malformed for an additional reason keeps the host
        parser's own syntax message — the long-standing convention for
        syntax errors, and the only rule both hosts can implement
        identically.
        """
        out = _parse_probe(raw_json)
        assert out.startswith(ERR_PREFIX)
        assert "json_parse:" not in out

    def test_a_non_finite_constant_outranks_a_lone_surrogate(self) -> None:
        """Precedence between the two refusals, pinned.

        ``json.loads`` reaches the end of the text before the
        surrogate scan runs at all, so the constant is recorded and
        wins.  The browser arrives at the same answer by a different
        route (``JSON.parse`` rejects the text outright, so its
        surrogate scan never runs either) — see the parity twin in
        ``tests/test_browser.py``.
        """
        assert _parse_probe('["\\ud800",NaN]') == err(
            non_finite_parse_message("NaN"),
        )


# A syntactically valid number whose magnitude overflows Float64.  RFC
# 8259 §6 sets no range limit but explicitly permits an implementation to
# set one, so this is the second entry route to a non-finite JNumber and
# the domain has to close it or the "no entry route" claim is false.
_OVERFLOW_CASES = [
    ("bare", "1e999", "Infinity"),
    ("bare_negative", "-1e999", "-Infinity"),
    ("in_array", "[1e999]", "Infinity"),
    ("in_object", '{"a":1e309}', "Infinity"),
    ("capital_exponent", "1E999", "Infinity"),
    ("doubly_nested", "[[1e999]]", "Infinity"),
    ("negative_in_object", '{"a":-1e999}', "-Infinity"),
]

# Finite boundary controls the overflow refusal must not reach.  The
# underflow case is the one that needs a decision rather than a check:
# 1e-999 decodes to 0.0, which is finite and therefore in the domain.
_FINITE_BOUNDARY_CASES = [
    ("max_float", "1e308", "1e+308"),
    ("negative_max_float", "-1e308", "-1e+308"),
    ("largest_representable", "1.7976931348623157e308", "1.7976931348623157e+308"),
    ("underflow_to_zero", "1e-999", "0"),
    ("negative_underflow_to_zero", "-1e-999", "0"),
    ("underflow_in_array", "[1e-999]", "[0]"),
]


class TestNonFiniteNumberOverflowRefusal1306:
    """A number that overflows to an infinity is refused at the parse.

    The constant refusal alone left the domain open: ``1e999`` is
    grammatically valid RFC 8259 that both host parsers accept, decoding
    to an infinite ``JNumber`` that then died at ``json_stringify`` —
    the very route #1306 claims to have closed, reached by a different
    syntax.  RFC 8259 §6 sets no limit on a number's range but says in
    so many words that an implementation may set one; §9.7.1 sets Vera's
    at the finite ``Float64`` values, which is also exactly what
    ``json_stringify`` can write back.

    Underflow is not the same question and is not refused: ``1e-999``
    decodes to ``0``, which is finite and in the domain.
    """

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "name"),
        _OVERFLOW_CASES,
        ids=[c[0] for c in _OVERFLOW_CASES],
    )
    def test_overflow_is_refused_with_the_shared_sentence(
        self, case_id: str, raw_json: str, name: str,
    ) -> None:
        assert _parse_probe(raw_json) == err(non_finite_number_message(name))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _FINITE_BOUNDARY_CASES,
        ids=[c[0] for c in _FINITE_BOUNDARY_CASES],
    )
    def test_finite_numbers_at_the_boundary_still_parse(
        self, case_id: str, raw_json: str, expected: str,
    ) -> None:
        """The controls that make the refusal a boundary and not a wall.

        ``1.7976931348623157e308`` is the largest finite double: a
        refusal keyed on "large" rather than on "not finite" would take
        it, and take every legitimate scientific document with it.
        """
        assert _parse_probe(raw_json) == ok(expected)

    def test_underflow_decodes_to_zero_rather_than_being_refused(
        self,
    ) -> None:
        """The decision, stated as a test as well as in the spec.

        ``1e-999`` is as unrepresentable as ``1e999`` in the sense that
        the value the text names is not the value you get — but what you
        get is ``0``, a finite number the format and the language both
        carry, so the domain admits it.  Pinned explicitly because
        "symmetry with overflow" is the plausible wrong answer.
        """
        assert _parse_probe("1e-999") == ok("0")
        assert _parse_probe("[1e-999,1e999]") == err(
            non_finite_number_message("Infinity"),
        )

    def test_a_constant_outranks_an_overflow(self) -> None:
        """Both hosts reach the constant sentence, by different routes.

        The reference host records the constant during the parse and
        checks it before walking the decoded tree; the browser never
        parses the text at all.  Pinned in both orders so the answer
        cannot depend on which appears first.
        """
        expected = err(non_finite_parse_message("NaN"))
        assert _parse_probe("[NaN,1e999]") == expected
        assert _parse_probe("[1e999,NaN]") == expected

    def test_document_order_decides_between_the_two_walk_refusals(
        self,
    ) -> None:
        """Overflow and lone surrogate are found by ONE walk.

        Both are properties of the decoded value rather than of the
        text, so both are found by the same document-order traversal and
        whichever comes first names the refusal — a rule that needs no
        precedence table and that the two hosts cannot implement
        differently.
        """
        assert _parse_probe('["a\\ud800b",1e999]') == err(
            lone_surrogate_message(0xD800),
        )
        assert _parse_probe('[1e999,"a\\ud800b"]') == err(
            non_finite_number_message("Infinity"),
        )


# The integer arm of the overflow route.  ``json.loads`` yields a Python
# ``int`` — not a float — for a digit string with no fraction and no
# exponent, so ``1`` followed by 309 zeros never reaches a float range
# check at all.  It reaches ``write_json``'s ``float(value)`` instead,
# where the conversion raises.  JS has no such split: ``JSON.parse``
# produces a double either way, so the browser was right about these all
# along and only the reference host had a hole.
#
# The boundary is the double rounding boundary, not ``sys.float_info.max``.
# An integer strictly between the largest finite double and the midpoint
# to 2**1024 rounds DOWN to that double and is perfectly representable —
# ``int(sys.float_info.max) + 1`` is such an integer, and both hosts
# accept it.  A comparison against ``int(sys.float_info.max)`` would
# refuse it on the reference host alone, trading this divergence for its
# mirror image.

_INT_OVERFLOW_CASES = [
    ("digits_309", "1" + "0" * 309, "Infinity"),
    ("digits_310", "1" + "0" * 310, "Infinity"),
    # 400 digits: far past anything a float conversion could survive, so
    # a comparison implemented AS a float conversion raises here instead
    # of refusing.  The assertion is on the Err, never on an exception.
    ("digits_400", "1" + "0" * 400, "Infinity"),
    ("negative_309", "-1" + "0" * 309, "-Infinity"),
    ("in_array", "[1" + "0" * 309 + "]", "Infinity"),
    ("in_object", '{"a":1' + "0" * 309 + "}", "Infinity"),
    ("nested", "[[1" + "0" * 309 + "]]", "Infinity"),
    ("exact_rounding_boundary", str(INT_ROUNDS_TO_INFINITY), "Infinity"),
    ("negative_exact_boundary", "-" + str(INT_ROUNDS_TO_INFINITY),
     "-Infinity"),
]

_INT_ACCEPTED_CASES = [
    ("digits_308", "1" + "0" * 308, "1e+308"),
    ("negative_digits_308", "-1" + "0" * 308, "-1e+308"),
    ("boundary_minus_one", str(INT_ROUNDS_TO_INFINITY - 1),
     "1.7976931348623157e+308"),
    ("max_finite_as_int", str(MAX_FINITE_AS_INT),
     "1.7976931348623157e+308"),
    # The control that separates the rounding boundary from
    # ``sys.float_info.max``: this integer is LARGER than the largest
    # finite double and still rounds to it.
    ("max_finite_as_int_plus_one", str(MAX_FINITE_AS_INT + 1),
     "1.7976931348623157e+308"),
    ("ordinary_integer", "42", "42"),
    ("negative_ordinary_integer", "-42", "-42"),
]


class TestIntegerOverflowRefusal1306:
    """An integer literal too large for a double is refused at the parse.

    The float arm of the walk cannot see these.  ``json.loads`` returns
    an ``int`` for a digit string with no fraction and no exponent, and
    a Python ``int`` is never infinite however many digits it has — the
    reasoning that made a float-only range check look complete.  What it
    missed is that the value still has to BECOME a double at the WASM
    boundary: ``write_json`` calls ``float(value)``, which raises
    ``OverflowError`` for a magnitude past the rounding boundary.  So a
    text the browser refused with the shared sentence killed the
    reference host with a CPython message instead — an `Err`-at-parse
    MUST and a same-message-on-every-runtime MUST, both broken by one
    shape.

    The comparison is integer arithmetic against an exact integer bound.
    Implementing it as ``float(value)`` would be the very overflow it is
    meant to detect.
    """

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "name"),
        _INT_OVERFLOW_CASES,
        ids=[c[0] for c in _INT_OVERFLOW_CASES],
    )
    def test_integer_overflow_is_refused_with_the_shared_sentence(
        self, case_id: str, raw_json: str, name: str,
    ) -> None:
        assert _parse_probe(raw_json) == err(non_finite_number_message(name))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _INT_ACCEPTED_CASES,
        ids=[c[0] for c in _INT_ACCEPTED_CASES],
    )
    def test_integers_that_round_into_range_still_parse(
        self, case_id: str, raw_json: str, expected: str,
    ) -> None:
        assert _parse_probe(raw_json) == ok(expected)

    def test_the_bound_is_the_rounding_boundary_not_the_largest_double(
        self,
    ) -> None:
        """The two candidate bounds differ, and only one matches the browser.

        Everything in ``[int(sys.float_info.max), boundary)`` rounds down
        to the largest finite double and is accepted by ``JSON.parse``.
        A reference-host check against ``sys.float_info.max`` would
        refuse that band and diverge again — the same defect with its
        sign flipped, and invisible to a battery whose only large case
        is a round number of zeros.
        """
        assert MAX_FINITE_AS_INT < INT_ROUNDS_TO_INFINITY
        assert first_domain_violation(MAX_FINITE_AS_INT) is None
        assert first_domain_violation(MAX_FINITE_AS_INT + 1) is None
        assert first_domain_violation(INT_ROUNDS_TO_INFINITY - 1) is None
        assert first_domain_violation(INT_ROUNDS_TO_INFINITY) == (
            non_finite_number_message("Infinity")
        )
        assert first_domain_violation(-INT_ROUNDS_TO_INFINITY) == (
            non_finite_number_message("-Infinity")
        )

    def test_the_bound_agrees_with_python_s_own_float_conversion(
        self,
    ) -> None:
        """A differential, because the bound is a hand-derived constant.

        ``2**1024 - 2**970`` is the midpoint between the largest finite
        double and ``2**1024``, and ties-to-even sends it upward — but
        that is a derivation, and a derivation is what a test is for.
        The oracle is ``float()`` itself: below the bound it succeeds,
        at and above it raises.
        """
        assert float(INT_ROUNDS_TO_INFINITY - 1) == sys.float_info.max
        with pytest.raises(OverflowError):
            float(INT_ROUNDS_TO_INFINITY)

    def test_a_huge_integer_is_refused_rather_than_raising(self) -> None:
        """The 400-digit case, stated as its own property.

        A range check written as a float conversion does not merely give
        the wrong answer here — it raises, which a parametrized equality
        assertion would report as an error rather than as the divergence
        it is.  Asserting the ``Err`` value directly says what must
        happen.
        """
        assert _parse_probe("1" + "0" * 400) == err(
            non_finite_number_message("Infinity"),
        )

    def test_a_bool_is_still_not_a_number(self) -> None:
        """``bool`` subclasses ``int``; the int arm must not claim it."""
        assert first_domain_violation(True) is None
        assert first_domain_violation([True, False]) is None
        assert _parse_probe("[true,false]") == ok("[true,false]")


# ---------------------------------------------------------------------------
# #1308 — lone-surrogate escapes
# ---------------------------------------------------------------------------


class TestLoneSurrogateParseRefusal1308:
    """A lone-surrogate escape is refused at the parse, keys included.

    RFC 8259 permits the *text*; Unicode does not permit the *value*.
    A lone surrogate is not a scalar value and has no UTF-8 encoding, so
    it cannot cross the WASM boundary into a Vera string at all — which
    is why the pre-fix reference host died inside ``_alloc_string``
    rather than returning anything.
    """

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "code_point"),
        _LONE_SURROGATE_CASES,
        ids=[c[0] for c in _LONE_SURROGATE_CASES],
    )
    def test_refused_with_the_shared_sentence(
        self, case_id: str, raw_json: str, code_point: int,
    ) -> None:
        assert _parse_probe(raw_json) == err(lone_surrogate_message(code_point))

    @pytest.mark.parametrize(
        ("case_id", "raw_json", "expected"),
        _PAIRED_SURROGATE_CASES,
        ids=[c[0] for c in _PAIRED_SURROGATE_CASES],
    )
    def test_paired_surrogates_still_parse(
        self, case_id: str, raw_json: str, expected: str,
    ) -> None:
        """The boundary the refusal must not overshoot.

        ``\\ud83d\\ude00`` is the ordinary way to write U+1F600 in JSON.
        A check that refused any code unit in the surrogate range would
        break every astral character in every document — so these run
        beside the refusals rather than in a separate file.
        """
        assert _parse_probe(raw_json) == ok(expected)

    def test_message_names_the_code_point_and_the_remedy(self) -> None:
        """Guards the guard — same reasoning as the #1306 twin."""
        msg = lone_surrogate_message(0xD800)
        assert "\\uD800" in msg
        assert "surrogate" in msg
        assert "json_parse:" in msg
        assert "pair" in msg

    def test_message_normalises_the_hex_casing(self) -> None:
        """One sentence per code point, whatever the input looked like.

        The escape can be written ``\\ud800`` or ``\\uD800``; the
        refusal names the code point, so both spellings produce the same
        message and the parity battery can compare across hosts without
        a casing rule.
        """
        assert lone_surrogate_message(0xD800) == lone_surrogate_message(0xD800)
        assert "\\uD800" in lone_surrogate_message(0xD800)
        assert "\\uDFFF" in lone_surrogate_message(0xDFFF)


class TestFirstDomainViolationScan:
    """Unit tests for the one tree walk behind both value-level refusals.

    The end-to-end tests above can only observe the first refusal; these
    pin the traversal directly, including the cases where "which one is
    first" is the whole question.  The walk returns the ``Err`` sentence
    itself rather than a code point or a float, so a caller cannot pair
    a found violation with the wrong message, and the browser's twin
    returns the same kind of thing.
    """

    def test_returns_none_for_clean_trees(self) -> None:
        assert first_domain_violation(None) is None
        assert first_domain_violation(True) is None
        assert first_domain_violation(1.5) is None
        assert first_domain_violation(0.0) is None
        assert first_domain_violation(1) is None
        assert first_domain_violation("plain") is None
        assert first_domain_violation("\U0001F600") is None
        assert first_domain_violation([1.0, "a", {"b": "c"}]) is None
        assert first_domain_violation({"k": ["nested", {"deep": "ok"}]}) is None

    def test_finds_a_lone_surrogate_in_a_value(self) -> None:
        assert first_domain_violation({"k": "a\ud800b"}) == (
            lone_surrogate_message(0xD800)
        )

    def test_finds_a_lone_surrogate_in_a_key(self) -> None:
        """Keys are strings too, and cross the same boundary.

        A walk that only visited values would leave the key route open —
        and the key route is what #1308's own reproduction used.
        """
        assert first_domain_violation({"a\ud800b": 1.0}) == (
            lone_surrogate_message(0xD800)
        )

    def test_finds_a_non_finite_number(self) -> None:
        assert first_domain_violation(float("inf")) == (
            non_finite_number_message("Infinity")
        )
        assert first_domain_violation(float("-inf")) == (
            non_finite_number_message("-Infinity")
        )
        assert first_domain_violation({"a": [1.0, float("inf")]}) == (
            non_finite_number_message("Infinity")
        )

    def test_nan_is_covered_though_no_json_text_decodes_to_one(self) -> None:
        """The third non-finite float, for completeness of the helper.

        No RFC 8259 number literal decodes to NaN and the bare constant
        is refused at the parse gate, so this arm is unreachable through
        ``json_parse`` — which is exactly why it needs a direct test:
        an unreachable branch is where a wrong answer survives.
        """
        assert first_domain_violation(float("nan")) == (
            non_finite_number_message("NaN")
        )

    def test_an_integer_in_range_is_not_a_violation(self) -> None:
        """An in-range ``int`` passes; an out-of-range one does not.

        This test asserted ``first_domain_violation(10**400) is None``
        until the integer arm landed.  It read "a Python ``int`` cannot
        be infinite" as "an ``int`` is always in the domain" — the exact
        premise the float-only range check was built on, written down
        twice and therefore agreeing with itself.  A test derived from
        the implementation's own reasoning does not miss the defect, it
        certifies it; the refusals live in
        ``TestIntegerOverflowRefusal1306``.
        """
        assert first_domain_violation(1) is None
        assert first_domain_violation(-1) is None
        assert first_domain_violation(10**300) is None
        assert first_domain_violation([1, 2, 3]) is None
        assert first_domain_violation(10**400) == (
            non_finite_number_message("Infinity")
        )

    def test_a_bool_is_not_read_as_a_number(self) -> None:
        """``bool`` subclasses ``int``, not ``float``."""
        assert first_domain_violation([True, False]) is None

    def test_key_is_checked_before_its_own_value(self) -> None:
        assert first_domain_violation({"\ud800": "\udc00"}) == (
            lone_surrogate_message(0xD800)
        )

    def test_earlier_entry_wins_over_later(self) -> None:
        assert first_domain_violation({"a": "\udc00", "b": "\ud800"}) == (
            lone_surrogate_message(0xDC00)
        )

    def test_array_order_is_document_order(self) -> None:
        assert first_domain_violation(["ok", "\udfff", "\ud800"]) == (
            lone_surrogate_message(0xDFFF)
        )

    def test_the_two_kinds_share_one_document_order(self) -> None:
        """Whichever comes first names the refusal — no precedence table."""
        assert first_domain_violation(["\ud800", float("inf")]) == (
            lone_surrogate_message(0xD800)
        )
        assert first_domain_violation([float("inf"), "\ud800"]) == (
            non_finite_number_message("Infinity")
        )

    def test_boundary_code_points(self) -> None:
        """The surrogate block is D800-DFFF inclusive on both ends.

        D7FF and E000 are ordinary scalar values that a range test with
        the wrong comparison would reject.
        """
        assert first_domain_violation("\ud7ff") is None
        assert first_domain_violation("\ue000") is None
        assert first_domain_violation("\ud800") == (
            lone_surrogate_message(0xD800)
        )
        assert first_domain_violation("\udfff") == (
            lone_surrogate_message(0xDFFF)
        )
