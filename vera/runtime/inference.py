"""Inference effect host bindings.

Extracted from `execute()` in `vera/codegen/api.py` (#421).  Includes the LLM
provider registry and HTTP call helper, which are used only by this family.
"""

from __future__ import annotations

from dataclasses import dataclass

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _alloc_result_ok_string,
    _read_wasm_string,
)
from vera.runtime.http import _HTTP_TIMEOUT


@dataclass(frozen=True)
class _ProviderConfig:
    """Configuration for a single LLM inference provider."""

    env_key: str         # environment variable holding the API key
    url: str             # chat completions endpoint URL
    default_model: str   # provider's flagship model when VERA_INFERENCE_MODEL is unset
    auth_style: str      # "anthropic" | "bearer"
    response_style: str  # "anthropic" | "openai"


#: Registry of supported inference providers.
#: Adding a new OpenAI-compatible provider is a one-row change here.
#:
#: Each row's ``default_model`` is that provider's flagship general-chat
#: model, verified against the vendor's own live documentation when set.
#: A vendor's cheap tier is reachable through ``VERA_INFERENCE_MODEL``;
#: the default is not the place to trade capability for price, because a
#: program's contracts are written against what the default can do.
_PROVIDERS: dict[str, _ProviderConfig] = {
    "anthropic": _ProviderConfig(
        env_key="VERA_ANTHROPIC_API_KEY",
        url="https://api.anthropic.com/v1/messages",
        default_model="claude-opus-5",
        auth_style="anthropic",
        response_style="anthropic",
    ),
    "openai": _ProviderConfig(
        env_key="VERA_OPENAI_API_KEY",
        url="https://api.openai.com/v1/chat/completions",
        default_model="gpt-5.6-sol",
        auth_style="bearer",
        response_style="openai",
    ),
    "moonshot": _ProviderConfig(
        env_key="VERA_MOONSHOT_API_KEY",
        url="https://api.moonshot.ai/v1/chat/completions",
        default_model="kimi-k3",
        auth_style="bearer",
        response_style="openai",
    ),
    "mistral": _ProviderConfig(
        env_key="VERA_MISTRAL_API_KEY",
        url="https://api.mistral.ai/v1/chat/completions",
        default_model="mistral-large-latest",
        auth_style="bearer",
        response_style="openai",
    ),
    # New providers append here: insertion order is the auto-detect
    # precedence, so prepending would change which key wins when
    # several are set.
    "xai": _ProviderConfig(
        env_key="VERA_XAI_API_KEY",
        url="https://api.x.ai/v1/chat/completions",
        default_model="grok-4.6",
        auth_style="bearer",
        response_style="openai",
    ),
    "deepseek": _ProviderConfig(
        env_key="VERA_DEEPSEEK_API_KEY",
        url="https://api.deepseek.com/v1/chat/completions",
        default_model="deepseek-v4-pro",
        auth_style="bearer",
        response_style="openai",
    ),
}


#: Longest provider-supplied error text we quote back into a Vera-level
#: `Result::Err`.  A misconfigured proxy answers with a whole HTML page;
#: the useful signal is in its first line, and the Err string is a value
#: a Vera program may go on to concatenate, print, or match against.
_ERROR_BODY_CHARS = 200


def _truncate(text: str) -> str:
    """*text*, clipped to `_ERROR_BODY_CHARS` with the clipping made visible."""
    text = text.strip()
    if len(text) <= _ERROR_BODY_CHARS:
        return text
    return text[:_ERROR_BODY_CHARS] + "... (truncated)"


def _describe_keys(value: object) -> str:
    """The keys of *value* if it is an object, else what it actually is.

    Used only inside error messages: when a response does not have the
    shape the branch expects, naming what it DID have is the difference
    between a report the user can act on and one they have to reproduce
    under a debugger.
    """
    if isinstance(value, dict):
        return ", ".join(str(k) for k in value) or "(no keys)"
    return f"(not an object: {type(value).__name__})"


def _describe_types(items: list[object]) -> str:
    """The distinct `type` discriminators in *items*, in first-seen order.

    This is what turns #1333's failure into a self-explaining one: an
    Anthropic response with no text block reports `thinking` rather than
    an unqualified "no text".
    """
    seen: list[str] = []
    for item in items:
        kind = (
            str(item.get("type", "(untyped)"))
            if isinstance(item, dict)
            else f"(not an object: {type(item).__name__})"
        )
        if kind not in seen:
            seen.append(kind)
    return ", ".join(seen) or "(none)"


def _error_body_detail(raw: bytes) -> str:
    """The provider's own message out of an HTTP error body.

    Anthropic and every OpenAI-compatible provider spell a rejection as
    ``{"error": {"message": ...}}``, so one extraction serves both
    families.  Anything else — an HTML proxy page, an empty body — falls
    back to the raw text, truncated.  Decoded with ``errors="replace"``
    because a non-UTF-8 error body must still produce an error message
    rather than a second, unrelated failure.
    """
    import json as _json

    text = raw.decode("utf-8", errors="replace").strip()
    if not text:
        return "(empty response body)"
    try:
        parsed = _json.loads(text)
    except ValueError:
        return _truncate(text)
    if isinstance(parsed, dict):
        err = parsed.get("error")
        if isinstance(err, dict) and isinstance(err.get("message"), str):
            return _truncate(str(err["message"]))
        if isinstance(err, str) and err:
            return _truncate(err)
        if isinstance(parsed.get("message"), str):
            return _truncate(str(parsed["message"]))
    return _truncate(text)


def _call_inference_provider(
    provider: str,
    prompt: str,
    model: str,
    api_key: str,
) -> str:
    """Dispatch a completion request to the configured LLM provider.

    Looks up *provider* in ``_PROVIDERS``, builds the appropriate request,
    and returns the completion string.  Raises on network or API errors;
    the caller wraps the result in Ok/Err and writes it to WASM memory.
    """
    import json as _json
    import urllib.error as _urlerr
    import urllib.request as _urlreq

    cfg = _PROVIDERS.get(provider)
    if cfg is None:
        valid = ", ".join(sorted(_PROVIDERS))
        raise ValueError(
            f"Unknown inference provider '{provider}'. "
            f"Valid values: {valid}."
        )

    chosen_model = model or cfg.default_model

    if cfg.auth_style == "anthropic":
        headers = {
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        }
        body = _json.dumps({
            "model": chosen_model,
            "max_tokens": 1024,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")
    else:  # bearer
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        }
        body = _json.dumps({
            "model": chosen_model,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")

    req = _urlreq.Request(cfg.url, data=body, headers=headers, method="POST")  # noqa: S310
    try:
        with _urlreq.urlopen(req, timeout=_HTTP_TIMEOUT) as resp:  # noqa: S310
            raw = resp.read()
            # #591 — strict-mode `.decode("utf-8")` previously leaked
            # the raw `UnicodeDecodeError` message (including byte
            # offsets and Python-internals jargon) into the
            # `Result::Err` string the user sees from
            # `Inference.complete`.  An LLM-API response that isn't
            # valid UTF-8 is genuinely broken — we want to fail loudly
            # but with a Vera-native message, not Python noise.
            try:
                decoded = raw.decode("utf-8")
            except UnicodeDecodeError as ude:
                raise RuntimeError(
                    f"Inference provider '{provider}' returned a "
                    f"response body that is not valid UTF-8 "
                    f"(invalid byte at position {ude.start}).",
                ) from None
    except _urlerr.HTTPError as http_err:
        # #1333 — an unhandled HTTPError escaped as urllib's own
        # `HTTP Error 401: Unauthorized`, which names neither the
        # provider that rejected the request nor the reason it gave.
        # The status line is the least useful half of what the API
        # actually sent back.
        detail = _error_body_detail(
            http_err.read() if getattr(http_err, "fp", None) is not None else b"",
        )
        raise RuntimeError(
            f"Inference provider '{provider}' ({chosen_model}) rejected "
            f"the request: HTTP {http_err.code}: {detail}",
        ) from None

    try:
        data = _json.loads(decoded)
    except ValueError:
        # A gateway or proxy answering 200 with an HTML page.  Caught
        # here rather than at the host boundary because
        # `json.JSONDecodeError` is a `ValueError` SUBCLASS, and the
        # boundary's pass-through is what keeps this module's own
        # messages verbatim — see `register_inference`.
        raise RuntimeError(
            f"Inference provider '{provider}' ({chosen_model}) returned a "
            f"response body that is not JSON: {_truncate(decoded)}",
        ) from None

    # #1333 — select the completion by SHAPE, never by position.  The
    # Anthropic Messages API returns `content` as a list of *typed*
    # blocks, and a reasoning-capable flagship can lead with a
    # `thinking` block; `content[0]["text"]` therefore raised
    # `KeyError('text')`, which the host boundary stringified into the
    # Err payload `'text'`.  The OpenAI-style branch gets the same
    # treatment: `message.content` is a string on an ordinary turn, a
    # list of typed parts on some multimodal ones, and `null` on a
    # reasoning/tool-call turn — where the old `str(...)` produced the
    # literal completion `"None"`, a silent wrong answer.
    if cfg.response_style == "anthropic":
        content = data.get("content") if isinstance(data, dict) else None
        if not isinstance(content, list):
            raise RuntimeError(
                f"Inference provider '{provider}' ({chosen_model}) returned "
                f"no text block (no 'content' list in the response; "
                f"response keys: {_describe_keys(data)}).",
            )
        texts = [
            str(block["text"])
            for block in content
            if isinstance(block, dict)
            and block.get("type") == "text"
            and "text" in block
        ]
        if not texts:
            raise RuntimeError(
                f"Inference provider '{provider}' ({chosen_model}) returned "
                f"no text block (content block types: "
                f"{_describe_types(content)}).",
            )
        # Joined without a separator: consecutive text blocks are
        # fragments of one message, so concatenation reconstructs
        # exactly what the model emitted.
        return "".join(texts)

    # openai-style
    choices = data.get("choices") if isinstance(data, dict) else None
    if not isinstance(choices, list) or not choices:
        raise RuntimeError(
            f"Inference provider '{provider}' ({chosen_model}) returned no "
            f"completion text (no 'choices' list in the response; "
            f"response keys: {_describe_keys(data)}).",
        )
    first = choices[0]
    message = first.get("message") if isinstance(first, dict) else None
    content = message.get("content") if isinstance(message, dict) else None
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        parts = [
            str(part["text"])
            for part in content
            if isinstance(part, dict)
            and part.get("type") == "text"
            and "text" in part
        ]
        if parts:
            return "".join(parts)
        raise RuntimeError(
            f"Inference provider '{provider}' ({chosen_model}) returned no "
            f"completion text (no text parts in the message content; "
            f"part types: {_describe_types(content)}).",
        )
    raise RuntimeError(
        f"Inference provider '{provider}' ({chosen_model}) returned no "
        f"completion text (message content is {type(content).__name__}; "
        f"message keys: {_describe_keys(message)}).",
    )


def register_inference(
    linker: wasmtime.Linker,
    ops_used: set[str],
    env_vars: dict[str, str] | None,
) -> None:
    """Register the requested Inference host functions on `linker`."""
    if "inference_complete" in ops_used:
        def host_inference_complete(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            import os as _os

            prompt = _read_wasm_string(caller, ptr, length)
            _env = env_vars if env_vars is not None else _os.environ
            provider = _env.get("VERA_INFERENCE_PROVIDER", "").lower()

            # Auto-detect provider from whichever key is set,
            # respecting registry insertion order (anthropic first).
            if not provider:
                for _pname, _pcfg in _PROVIDERS.items():
                    if _env.get(_pcfg.env_key, ""):
                        provider = _pname
                        break

            if not provider:
                key_vars = ", ".join(
                    c.env_key for c in _PROVIDERS.values()
                )
                return _alloc_result_err_string(
                    caller,
                    f"No inference provider configured. "
                    f"Set {key_vars}.",
                )

            cfg = _PROVIDERS.get(provider)
            api_key = _env.get(cfg.env_key, "") if cfg else ""

            if cfg is not None and not api_key:
                return _alloc_result_err_string(
                    caller,
                    f"Inference provider '{provider}' selected but "
                    f"{cfg.env_key} is not set.",
                )

            try:
                model = _env.get("VERA_INFERENCE_MODEL", "")
                completion = _call_inference_provider(
                    provider, prompt, model, api_key,
                )
                return _alloc_result_ok_string(caller, completion)
            except Exception as exc:  # noqa: BLE001 — host boundary; any failure becomes Result.Err
                # #1333 — the Err payload is a Vera-level value, so a
                # bare `str(exc)` publishes whatever Python spelling the
                # failure happened to have: a `KeyError('text')` from the
                # response parse reached the user as the entire message
                # `'text'`, naming neither the operation nor the provider.
                #
                # EXACT type, not `isinstance`: this module raises plain
                # `RuntimeError` / `ValueError` for its own deliberate,
                # Vera-native messages, and every *subclass* of those —
                # `json.JSONDecodeError` most notably — is by definition a
                # shape surprise rather than a message written for a user.
                # An `isinstance` test would re-open the hole for exactly
                # the class of exception this guard exists to catch.
                if type(exc) in (RuntimeError, ValueError):
                    return _alloc_result_err_string(caller, str(exc))
                return _alloc_result_err_string(
                    caller,
                    f"Inference provider '{provider}' failed: "
                    f"{type(exc).__name__}: {exc}",
                )

        linker.define_func(
            "vera", "inference_complete",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_inference_complete, access_caller=True,
        )
