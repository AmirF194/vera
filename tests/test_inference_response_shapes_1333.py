"""#1333 — `Inference.complete` must parse provider responses by SHAPE, not by position.

The reported failure: `examples/inference.vera` printed `'text'` and exited 1
against the Anthropic flagship.  `_call_inference_provider` read the Anthropic
Messages response as `data["content"][0]["text"]`, and `claude-opus-5` returns
`content` as a list of *typed* blocks that can lead with a non-text (thinking)
block.  `content[0]` therefore had no `"text"` key, the `KeyError('text')`
reached the host boundary's blanket `except Exception`, and `str(exc)` — the
bare repr of the missing key — became the whole `Result::Err` payload.

Three properties are pinned here, one per defect:

1. **Selection by type.**  The Anthropic branch collects every `type == "text"`
   block in order and joins them, so a leading thinking block is skipped rather
   than mis-read.  The OpenAI-style branch is hardened the same way: a
   `message.content` may be a string (the common case), a list of typed parts,
   or `null` on a reasoning/tool-call turn — the last of which previously
   returned the *string* `"None"` as a successful completion.

2. **Named failures.**  Every shape failure, and every HTTP rejection, names
   the provider AND the model that answered.  The maintainer's provider sweep
   for this issue misattributed the failure to xAI, because with
   `VERA_INFERENCE_PROVIDER` unset auto-detect takes the first configured key
   in registry insertion order and a still-exported Anthropic key won the
   "xAI run".  An error that names its own provider makes that class of
   misreading impossible.

3. **No bare Python spelling at the boundary.**  Only this module's own
   deliberate `RuntimeError`/`ValueError` messages pass through verbatim; any
   other exception type is labelled `Inference provider '<p>' failed:
   <Type>: <msg>`, so a future shape surprise can never again surface as
   `'text'`.

The headline cells run END TO END — a real Vera program through `execute()`
with `urllib.request.urlopen` mocked — because that is the path the maintainer
hit; `_call_inference_provider` unit cells cover the shape matrix beneath it.
No test here touches the network.
"""
from __future__ import annotations

import email.message
import io
import json
import urllib.error
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from vera.codegen import execute
from vera.runtime.inference import _PROVIDERS, _call_inference_provider

from tests.codegen_helpers import _compile_ok


# =====================================================================
# Fixtures: response bodies and a mock transport
# =====================================================================

#: A Vera program that prints whichever side of the Result it gets and
#: reports which side that was.  Ok -> 0, Err -> 1, exactly like
#: examples/inference.vera, so `stdout` carries the completion or the
#: Err string verbatim and `value` says which branch produced it.
_CLASSIFY_SOURCE = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference, IO>)
{
  let @Result<String, String> = Inference.complete("Is this positive?");
  match @Result<String, String>.0 {
    Ok(@String) -> {
      IO.print(@String.0);
      0
    },
    Err(@String) -> {
      IO.print(@String.0);
      1
    }
  }
}
"""


def _mock_response_bytes(raw: bytes) -> MagicMock:
    """A transport whose body is raw bytes — for shapes a `str` cannot express."""
    resp = MagicMock()
    resp.read.return_value = raw
    resp.__enter__ = lambda s: s
    resp.__exit__ = MagicMock(return_value=False)
    return resp


def _mock_response(body: str) -> MagicMock:
    """A minimal stand-in for the object `urlopen` returns."""
    return _mock_response_bytes(body.encode("utf-8"))


def _http_error(code: int, body: str, *, url: str = "https://example.invalid") -> urllib.error.HTTPError:
    """An `HTTPError` shaped the way `urlopen` raises one, body included."""
    return urllib.error.HTTPError(
        url=url,
        code=code,
        msg="Unauthorized",
        hdrs=email.message.Message(),
        fp=io.BytesIO(body.encode("utf-8")),
    )


def _anthropic_body(*blocks: dict[str, Any]) -> str:
    return json.dumps({"id": "msg_1", "type": "message", "content": list(blocks)})


def _openai_body(content: Any) -> str:
    return json.dumps({"id": "c1", "choices": [{"message": {"role": "assistant", "content": content}}]})


#: The thinking-block-first shape that broke the example.  The text block
#: is NOT first, so a by-position read lands on the thinking block.
_THINKING_FIRST = _anthropic_body(
    {"type": "thinking", "thinking": "The sentence is cheerful.", "signature": "sig"},
    {"type": "text", "text": "Positive"},
)


def _call(provider: str, body: str, model: str = "") -> str:
    """Drive `_call_inference_provider` with a mocked transport."""
    with patch("urllib.request.urlopen", MagicMock(return_value=_mock_response(body))):
        return _call_inference_provider(provider, "prompt", model, "sk-test")


def _call_raising(provider: str, exc: BaseException, model: str = "") -> str:
    with patch("urllib.request.urlopen", MagicMock(side_effect=exc)):
        return _call_inference_provider(provider, "prompt", model, "sk-test")


def _run_with_transport(
    body: str | None = None,
    *,
    env: dict[str, str] | None = None,
    raises: BaseException | None = None,
) -> tuple[int | float | None, str]:
    """Compile and run `_CLASSIFY_SOURCE` end to end over a mocked transport.

    Returns `(exit value, stdout)` — 0/completion on the Ok branch,
    1/Err-string on the Err branch.
    """
    result = _compile_ok(_CLASSIFY_SOURCE)
    transport = (
        MagicMock(side_effect=raises)
        if raises is not None
        else MagicMock(return_value=_mock_response(body or ""))
    )
    with patch("urllib.request.urlopen", transport):
        exec_result = execute(
            result,
            env_vars=env if env is not None else {"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
        )
    return exec_result.value, exec_result.stdout


# =====================================================================
# 1. Anthropic content blocks — selection by type
# =====================================================================


class TestAnthropicContentBlocks1333:
    """The Anthropic branch selects text blocks by `type`, not by index."""

    def test_thinking_block_first_yields_the_text_block(self) -> None:
        """THE REGRESSION: a leading thinking block is skipped, not read.

        Under the by-position parse this raised `KeyError('text')`.
        """
        assert _call("anthropic", _THINKING_FIRST) == "Positive"

    def test_single_text_block(self) -> None:
        """The common case — one text block — is unchanged."""
        body = _anthropic_body({"type": "text", "text": "Positive"})
        assert _call("anthropic", body) == "Positive"

    def test_two_text_blocks_are_joined_in_order(self) -> None:
        """Multiple text blocks concatenate in response order.

        The two fragments are asymmetric and separator-free, so a reversed
        join or an interposed newline both fail rather than coincide with
        the right answer.
        """
        body = _anthropic_body(
            {"type": "text", "text": "Positive"},
            {"type": "text", "text": " indeed"},
        )
        assert _call("anthropic", body) == "Positive indeed"

    def test_text_block_after_tool_use_is_still_found(self) -> None:
        """Selection scans the whole list, not just the first two entries."""
        body = _anthropic_body(
            {"type": "thinking", "thinking": "..."},
            {"type": "tool_use", "id": "t1", "name": "search", "input": {}},
            {"type": "text", "text": "Neutral"},
        )
        assert _call("anthropic", body) == "Neutral"

    def test_no_text_block_names_provider_model_and_block_types(self) -> None:
        """A text-free response is an error that says whose it was."""
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        with pytest.raises(RuntimeError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "thinking" in message
        # Not the bare Python key that #1333 reported.
        assert message != "'text'"

    def test_no_text_block_reports_the_model_actually_used(self) -> None:
        """`VERA_INFERENCE_MODEL`'s value, not the registry default, is named.

        A message that always prints the default would be actively
        misleading on exactly the runs where the model is the variable.
        """
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        with pytest.raises(RuntimeError, match=r"claude-opus-4-6"):
            _call("anthropic", body, model="claude-opus-4-6")

    def test_content_missing_is_a_named_error(self) -> None:
        """A response with no `content` key fails with the same named shape."""
        body = json.dumps({"type": "error", "error": {"message": "overloaded"}})
        with pytest.raises(RuntimeError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "content" in message

    def test_content_not_a_list_is_a_named_error(self) -> None:
        """`content` as a bare string (a shape no provider sends today)."""
        body = json.dumps({"content": "Positive"})
        with pytest.raises(RuntimeError, match=r"anthropic.*claude-opus-5"):
            _call("anthropic", body)

    def test_empty_content_list_is_a_named_error(self) -> None:
        body = _anthropic_body()
        with pytest.raises(RuntimeError, match=r"anthropic.*claude-opus-5"):
            _call("anthropic", body)


# =====================================================================
# 2. OpenAI-style message content — string, parts, or null
# =====================================================================


class TestOpenAiStyleContent1333:
    """The five OpenAI-style providers get the same by-shape hardening."""

    def test_string_content(self) -> None:
        """The common case — `content` is a string — is unchanged."""
        assert _call("openai", _openai_body("Positive")) == "Positive"

    def test_parts_list_is_joined_in_order(self) -> None:
        """A typed-parts `content` joins its text parts, skipping the rest."""
        body = _openai_body([
            {"type": "reasoning", "reasoning": "..."},
            {"type": "text", "text": "Positive"},
            {"type": "text", "text": " indeed"},
        ])
        assert _call("openai", body) == "Positive indeed"

    def test_null_content_is_a_named_error(self) -> None:
        """A reasoning/tool-call turn with `content: null`.

        Previously this returned the *string* `"None"` as a successful
        completion — a silent wrong answer, not merely a bad message.
        """
        body = _openai_body(None)
        with pytest.raises(RuntimeError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert message != "None"

    def test_parts_list_without_text_parts_is_a_named_error(self) -> None:
        body = _openai_body([{"type": "reasoning", "reasoning": "..."}])
        with pytest.raises(RuntimeError) as excinfo:
            _call("openai", body)
        assert "reasoning" in str(excinfo.value)

    def test_missing_choices_is_a_named_error(self) -> None:
        body = json.dumps({"error": {"message": "model not found"}})
        with pytest.raises(RuntimeError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert "choices" in message

    def test_empty_choices_is_a_named_error(self) -> None:
        body = json.dumps({"choices": []})
        with pytest.raises(RuntimeError, match=r"openai.*gpt-5\.6-sol"):
            _call("openai", body)

    def test_missing_message_is_a_named_error(self) -> None:
        body = json.dumps({"choices": [{"finish_reason": "length"}]})
        with pytest.raises(RuntimeError, match=r"openai.*gpt-5\.6-sol"):
            _call("openai", body)


# =====================================================================
# 3. HTTP rejections and non-JSON bodies
# =====================================================================


class TestHttpRejectionMessages1333:
    """`urlopen` raising `HTTPError` must not escape as `HTTP Error 401: …`."""

    def test_anthropic_error_body_message_is_surfaced(self) -> None:
        """Anthropic's `{"error": {"message": …}}` body is read and quoted."""
        body = json.dumps({
            "type": "error",
            "error": {"type": "authentication_error", "message": "invalid x-api-key"},
        })
        with pytest.raises(RuntimeError) as excinfo:
            _call_raising("anthropic", _http_error(401, body))
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "401" in message
        assert "invalid x-api-key" in message
        # The raw urllib spelling must not be what the user sees.
        assert message != "HTTP Error 401: Unauthorized"

    def test_openai_style_error_body_message_is_surfaced(self) -> None:
        """The OpenAI-shaped error body uses the same `error.message` path."""
        body = json.dumps({
            "error": {
                "message": "Incorrect API key provided: sk-xxx.",
                "type": "invalid_request_error",
                "code": "invalid_api_key",
            },
        })
        with pytest.raises(RuntimeError) as excinfo:
            _call_raising("openai", _http_error(401, body))
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert "401" in message
        assert "Incorrect API key provided" in message

    def test_non_json_error_body_falls_back_to_raw_text(self) -> None:
        """An HTML error page from a proxy still yields a named message."""
        with pytest.raises(RuntimeError) as excinfo:
            _call_raising("anthropic", _http_error(502, "<html>Bad Gateway</html>"))
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "502" in message
        assert "Bad Gateway" in message

    def test_long_error_body_is_truncated(self) -> None:
        """A megabyte of proxy HTML does not become the Err string."""
        with pytest.raises(RuntimeError) as excinfo:
            _call_raising("anthropic", _http_error(500, "x" * 5000))
        message = str(excinfo.value)
        assert len(message) < 500
        assert "500" in message

    def test_non_json_success_body_is_a_named_error(self) -> None:
        """A 200 whose body is not JSON names the provider too.

        Without this the `json.JSONDecodeError` (a `ValueError` subclass)
        would reach the boundary and — under an `isinstance` pass-through —
        surface as the bare `Expecting value: line 1 column 1 (char 0)`.
        """
        with pytest.raises(RuntimeError) as excinfo:
            _call("anthropic", "<html>gateway timeout</html>")
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "Expecting value" not in message

    def test_non_utf8_success_body_is_a_named_error(self) -> None:
        """A 200 whose body is not valid UTF-8 names the provider and the byte.

        The #591 handler is guarded in `tests/test_runtime_traps.py` by a
        SOURCE regex, which proves the `except UnicodeDecodeError` block
        exists but can say nothing about what it produces — and #1333 moved
        that decode inside a new outer `try` / `except HTTPError`, so the
        behaviour is pinned here as well.  A strict `.decode("utf-8")`
        published the raw codec text — byte offsets and Python-internals
        jargon — as the whole Err string.
        """
        # The bad bytes sit mid-body, so the reported position is a real
        # offset rather than the 0 a truncated or empty body would also give.
        with patch(
            "urllib.request.urlopen",
            MagicMock(return_value=_mock_response_bytes(b"hello \xff\xfe world")),
        ), pytest.raises(RuntimeError) as excinfo:
            _call_inference_provider("anthropic", "prompt", "", "sk-test")
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "not valid UTF-8" in message
        assert "position 6" in message  # len(b"hello ") — the first bad byte
        # The #591 property proper: none of Python's own codec spelling
        # survives into a value a Vera program can print or match on.  These
        # two guard a different regression from the assertions above — a
        # bare strict decode fails this cell at `pytest.raises`, before any
        # message is read, whereas a handler that keeps the catch and
        # interpolates the exception (`RuntimeError(f"... {ude}")`) would
        # satisfy every positive assertion and re-leak the codec text.
        assert "codec can't decode" not in message
        assert "invalid start byte" not in message


# =====================================================================
# 4. The host boundary — end to end, the path the maintainer hit
# =====================================================================


class TestInferenceBoundaryEndToEnd1333:
    """`vera run` over a mocked transport: the product path, not the helper."""

    def test_thinking_first_prints_the_completion(self) -> None:
        """THE REGRESSION, end to end: the example's shape now succeeds.

        Before the fix this printed `'text'` and returned 1.
        """
        value, stdout = _run_with_transport(_THINKING_FIRST)
        assert value == 0
        assert stdout == "Positive"

    def test_no_text_block_err_names_provider_and_model(self) -> None:
        """The Err string is self-diagnosing, and is never the bare key."""
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        value, stdout = _run_with_transport(body)
        assert value == 1
        assert stdout != "'text'"
        assert stdout.startswith("Inference provider 'anthropic' (claude-opus-5)")
        assert "thinking" in stdout

    def test_http_rejection_err_names_provider_and_code(self) -> None:
        body = json.dumps({"error": {"message": "invalid x-api-key"}})
        value, stdout = _run_with_transport(raises=_http_error(401, body))
        assert value == 1
        assert stdout.startswith("Inference provider 'anthropic' (claude-opus-5)")
        assert "401" in stdout
        assert "invalid x-api-key" in stdout

    def test_unforeseen_exception_is_labelled_with_its_type(self) -> None:
        """THE BOUNDARY GUARD: a `KeyError` can never again print as `'text'`.

        `_call_inference_provider` is patched to raise the exact exception
        the by-position parse used to raise, so this cell measures the
        boundary's formatting rather than the parse that no longer fails.
        """
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=KeyError("text"),
        ):
            exec_result = execute(
                result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
            )
        assert exec_result.value == 1
        assert exec_result.stdout != "'text'"
        assert exec_result.stdout == (
            "Inference provider 'anthropic' failed: KeyError: 'text'"
        )

    def test_value_error_subclass_is_labelled_not_passed_through(self) -> None:
        """The pass-through is by EXACT type, so a subclass cannot claim it.

        `json.JSONDecodeError` IS a `ValueError`, so an `isinstance` test at
        the boundary would publish `Expecting value: line 1 column 1
        (char 0)` as the entire Err string — the same class of bare Python
        spelling as `'text'`.  The parse already converts that particular
        failure into a named message at source, so only this cell measures
        the boundary rule itself.
        """
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=json.JSONDecodeError("Expecting value", "<html>", 0),
        ):
            exec_result = execute(
                result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
            )
        assert exec_result.value == 1
        assert exec_result.stdout.startswith(
            "Inference provider 'anthropic' failed: JSONDecodeError: "
        )

    def test_deliberate_runtime_error_passes_through_verbatim(self) -> None:
        """This module's own Vera-native messages are not re-labelled."""
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=RuntimeError("Inference provider 'anthropic' (m) says so."),
        ):
            exec_result = execute(
                result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
            )
        assert exec_result.value == 1
        assert exec_result.stdout == "Inference provider 'anthropic' (m) says so."

    def test_unknown_provider_value_error_passes_through_verbatim(self) -> None:
        """The registry's own `ValueError` keeps its wording and its list."""
        value, stdout = _run_with_transport(
            _THINKING_FIRST,
            env={
                "VERA_INFERENCE_PROVIDER": "nope",
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
            },
        )
        assert value == 1
        assert stdout.startswith("Unknown inference provider 'nope'.")

    def test_json_decode_failure_is_named_not_python_spelled(self) -> None:
        """A `JSONDecodeError` is a `ValueError` *subclass* — it must not
        take the verbatim pass-through an `isinstance` check would grant."""
        value, stdout = _run_with_transport("<html>gateway timeout</html>")
        assert value == 1
        assert stdout.startswith("Inference provider 'anthropic' (claude-opus-5)")
        assert "Expecting value" not in stdout


# =====================================================================
# 5. The provider sweep, as a regression
# =====================================================================


#: The maintainer's six-provider sweep, in registry order, each row carrying
#: the response shape that provider actually returns and its flagship model
#: spelled LITERALLY — deriving the model from `_PROVIDERS` would pin the
#: assertion to itself and stay green through any edit to the row.
_SWEEP: tuple[tuple[str, str, str, str], ...] = (
    ("anthropic", "VERA_ANTHROPIC_API_KEY", "claude-opus-5", _THINKING_FIRST),
    ("openai", "VERA_OPENAI_API_KEY", "gpt-5.6-sol", _openai_body("Positive")),
    ("moonshot", "VERA_MOONSHOT_API_KEY", "kimi-k3", _openai_body("Positive")),
    ("mistral", "VERA_MISTRAL_API_KEY", "mistral-large-latest", _openai_body("Positive")),
    ("xai", "VERA_XAI_API_KEY", "grok-4.6", _openai_body("Positive")),
    ("deepseek", "VERA_DEEPSEEK_API_KEY", "deepseek-v4-pro", _openai_body("Positive")),
)


class TestProviderSweep1333:
    """All six providers answer `Positive`, which is what the sweep showed
    for five of them and must now show for the sixth."""

    def test_sweep_covers_every_registered_provider(self) -> None:
        """A row added to `_PROVIDERS` without a sweep row fails here.

        Otherwise the sweep silently stops being a sweep.
        """
        assert [row[0] for row in _SWEEP] == list(_PROVIDERS)
        for name, env_key, _model, _body in _SWEEP:
            assert _PROVIDERS[name].env_key == env_key

    @pytest.mark.parametrize(
        ("provider", "env_key", "model", "body"),
        _SWEEP,
        ids=[row[0] for row in _SWEEP],
    )
    def test_provider_returns_its_completion(
        self, provider: str, env_key: str, model: str, body: str,
    ) -> None:
        """End to end, with the provider pinned — as the sweep should have run."""
        value, stdout = _run_with_transport(
            body,
            env={"VERA_INFERENCE_PROVIDER": provider, env_key: "sk-test"},
        )
        assert value == 0
        assert stdout == "Positive"

    @pytest.mark.parametrize(
        ("provider", "env_key", "model", "body"),
        _SWEEP,
        ids=[row[0] for row in _SWEEP],
    )
    def test_provider_names_itself_when_the_shape_fails(
        self, provider: str, env_key: str, model: str, body: str,
    ) -> None:
        """Every branch's shape failure names its own provider and model.

        A message hardcoding one provider's name would satisfy a
        single-row test; running the whole registry through it cannot be.
        """
        value, stdout = _run_with_transport(
            json.dumps({"unexpected": "shape"}),
            env={"VERA_INFERENCE_PROVIDER": provider, env_key: "sk-test"},
        )
        assert value == 1
        assert stdout.startswith(f"Inference provider '{provider}' ({model})")

    def test_auto_detect_misattribution_is_self_diagnosing(self) -> None:
        """The sweep's own trap: an exported Anthropic key wins the "xAI run".

        With `VERA_INFERENCE_PROVIDER` unset, auto-detect takes the first
        configured key in registry insertion order, so a cumulative shell
        runs anthropic while the operator believes they are testing xAI.
        The Err must name the provider that actually answered.
        """
        value, stdout = _run_with_transport(
            json.dumps({"unexpected": "shape"}),
            env={
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
                "VERA_XAI_API_KEY": "sk-xai-test",
            },
        )
        assert value == 1
        assert stdout.startswith("Inference provider 'anthropic' (claude-opus-5)")
        assert "xai" not in stdout
