"""Shared fixtures for the `json_parse` accept-domain batteries (#1306, #1308).

Two batteries observe the same property from different sides —
`tests/test_json_accept_domain_1306_1308.py` runs the reference host
alone, `tests/test_browser.py::TestBrowserJsonAcceptDomainParity1306_1308`
runs the identical `.wasm` under both runtimes — and they only mean the
same thing if they send `json_parse` the same bytes and read its answer
the same way.

Everything that decides those two things lives here, following the
`tests/codegen_helpers.py` pattern (a plain module, imported by name):

    vera_lit(raw)               escape a JSON document for a Vera literal
    accept_domain_src(raw_json) the probe program both batteries compile
    ok(text) / err(message)     the probe's output protocol
    INT_ROUNDS_TO_INFINITY      the integer overflow bound
    MAX_FINITE_AS_INT           the bound it must NOT be confused with

The escaper is the reason this module exists rather than two tidy
copies.  One backslash either way changes which bytes `json_parse`
receives — a surrogate escape and a literal backslash-u sequence differ
by exactly that — so two implementations that drift apart do not fail
loudly, they quietly leave one battery testing a different input than
its case table names.
"""

from __future__ import annotations

import sys

# The smallest magnitude whose nearest double is an infinity, and so the
# bound for a JSON integer literal.  Mirrors
# ``vera.wasm.json_serde._INT_ROUNDS_TO_INFINITY``; the batteries pin the
# derivation against ``float()`` as oracle rather than trusting either
# copy.
INT_ROUNDS_TO_INFINITY = 2**1024 - 2**970

# The largest finite double as an exact integer.  Strictly smaller than
# the bound above: integers between the two round DOWN to it and are
# accepted, which is what makes this the wrong bound and a necessary
# control.
MAX_FINITE_AS_INT = int(sys.float_info.max)

# The probe's output protocol.  Which arm `json_parse` took is reported
# as a prefix so one byte-identical stdout comparison covers the arm AND
# the message.
OK_PREFIX = "OK:"
ERR_PREFIX = "ERR:"


def ok(canonical_text: str) -> str:
    """The expected probe output for an accepted document."""
    return OK_PREFIX + canonical_text


def err(message: str) -> str:
    """The expected probe output for a refused document."""
    return ERR_PREFIX + message


def vera_lit(raw: str) -> str:
    """Escape ``raw`` for embedding in a Vera string literal.

    The batteries' inputs are JSON documents full of quotes and
    backslashes, and one backslash either way changes which bytes
    ``json_parse`` receives.  Converting once, here, is what keeps every
    call site honest about its own input.
    """
    return raw.replace("\\", "\\\\").replace('"', '\\"')


_PROBE_TEMPLATE = """
private fn probe(@String -> @String)
  requires(true) ensures(true) effects(pure)
{{
  match json_parse(@String.0) {{
    Ok(@Json) -> string_concat("{ok}", json_stringify(@Json.0)),
    Err(@String) -> string_concat("{err}", @String.0)
  }}
}}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  IO.print(probe("{text}"))
}}
"""


def accept_domain_src(raw_json: str) -> str:
    """A ``main`` that reports which arm ``json_parse(raw_json)`` took.

    Prints ``OK:<canonical text>`` or ``ERR:<message>``.  Both batteries
    compile this same program, so a difference between them can only be
    the host, never the program.
    """
    return _PROBE_TEMPLATE.format(
        ok=OK_PREFIX, err=ERR_PREFIX, text=vera_lit(raw_json),
    )
