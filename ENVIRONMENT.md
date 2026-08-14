# Environment Variables

Vera reads a small set of `VERA_*` environment variables.  This document is the canonical reference; other docs (README, AGENTS, TESTING, CONTRIBUTING, SKILL, CLAUDE) link here for the full table and only mention individual variables where they're relevant in context.

| Variable | Purpose | Phase | Required |
|---|---|---|---|
| [`VERA_ANTHROPIC_API_KEY`](#inference-provider-keys) | Anthropic provider key for the `Inference` effect | runtime | one of the six provider keys, when running an `Inference` program |
| [`VERA_OPENAI_API_KEY`](#inference-provider-keys) | OpenAI provider key for the `Inference` effect | runtime | as above |
| [`VERA_MOONSHOT_API_KEY`](#inference-provider-keys) | Moonshot (Kimi) provider key for the `Inference` effect | runtime | as above |
| [`VERA_MISTRAL_API_KEY`](#inference-provider-keys) | Mistral provider key for the `Inference` effect | runtime | as above |
| [`VERA_XAI_API_KEY`](#inference-provider-keys) | xAI (Grok) provider key for the `Inference` effect | runtime | as above |
| [`VERA_DEEPSEEK_API_KEY`](#inference-provider-keys) | DeepSeek provider key for the `Inference` effect | runtime | as above |
| [`VERA_INFERENCE_PROVIDER`](#explicit-provider--model-overrides) | Force a specific provider rather than auto-detecting from the keys present | runtime | optional |
| [`VERA_INFERENCE_MODEL`](#explicit-provider--model-overrides) | Override the provider's default model | runtime | optional |
| [`VERA_DB_URL`](#vera_db_url) | Database connection for the `DB` effect | runtime | optional (defaults to `sqlite::memory:`) |
| [`VERA_JS_COVERAGE`](#vera_js_coverage) | Opt-in V8 coverage during browser-parity tests | dev / CI | optional |
| [`VERA_EAGER_GC`](#vera_eager_gc) | Force `$gc_collect` on every allocation — debugging knob for GC-rooting bugs | compile-time (dev) | optional |
| [`VERA_DEBUG_HOST_ERRORS`](#vera_debug_host_errors) | Re-raise a host callback's original exception instead of converting it — debugging knob for host-binding bugs | runtime (dev) | optional |

## Inference provider keys

The `Inference` effect ([spec/07-effects.md](spec/07-effects.md)) reaches an LLM provider over HTTP.  The runtime auto-detects which provider to use by checking which of these six variables is set:

- `VERA_ANTHROPIC_API_KEY`
- `VERA_OPENAI_API_KEY`
- `VERA_MOONSHOT_API_KEY` (Kimi)
- `VERA_MISTRAL_API_KEY`
- `VERA_XAI_API_KEY` (Grok)
- `VERA_DEEPSEEK_API_KEY`

The order above is the registry order, and detection walks it and takes the **first** provider whose key is set — so setting more than one key is deterministic rather than ambiguous, but silently ignores every key after the first.  Set exactly one, or use [`VERA_INFERENCE_PROVIDER`](#explicit-provider--model-overrides) to name the one you mean.  The conformance tests `tests/conformance/ch09_inference.vera` and `tests/conformance/ch09_http.vera` are skipped in CI because no provider key is set there; to run them locally:

```bash
export VERA_ANTHROPIC_API_KEY=sk-ant-...   # or any other key above, e.g. VERA_XAI_API_KEY=xai-...
vera run tests/conformance/ch09_inference.vera
```

The same export works for `examples/inference.vera` from `README.md`.

## Explicit provider / model overrides

- **`VERA_INFERENCE_PROVIDER`** — set to `anthropic`, `openai`, `moonshot`, `mistral`, `xai`, or `deepseek` to force the runtime to use that provider, overriding the auto-detect-by-key logic.  Useful when more than one provider key is set in the environment (e.g. a development shell), where auto-detection would otherwise take the first key in the order listed above.
- **`VERA_INFERENCE_MODEL`** — set to a provider-specific model identifier to override the default model.  Each provider has its own default; consult the provider's docs for valid model strings.

Both are optional.  When unset, the runtime uses auto-detection and the provider's default model.

## `VERA_DB_URL`

Chooses the database the `DB` effect connects to at runtime (`DB.query` / `DB.execute`; spec [§9.5.7](spec/09-standard-library.md)).

- **Unset** — an in-memory SQLite database (`sqlite::memory:`), created empty per run. Hermetic: nothing touches disk, so `vera test` and examples run without configuration.
- **`sqlite:///path/to/file.db`** — an on-disk SQLite file, e.g.:

  ```bash
  VERA_DB_URL=sqlite:///examples/sqlitedb.sqlite vera run examples/sqlitedb.vera
  ```

Phase: runtime (the connection is opened once at startup, during DB host-function registration — only for programs that use a `DB` operation — and reused for the rest of the run). In v1 the effect is SQLite-only and single-connection; a value that isn't one of the in-memory spellings or a `sqlite://` URL is treated as a SQLite file path, and an unopenable URL surfaces as the operation's `Err` result rather than a crash. Further backends are [#1143](https://github.com/aallan/vera/issues/1143). The browser runtime returns `Err` for every `DB` operation regardless of this variable, and the `wasi-p2` target rejects `<DB>` programs at compile time.

## `VERA_JS_COVERAGE`

Set to any non-empty value to enable V8 coverage collection during the browser-parity test suite (`tests/test_browser.py`).  Without it, the JavaScript runtime tests still run — they just don't emit a coverage report:

```bash
VERA_JS_COVERAGE=1 pytest tests/test_browser.py -v
```

CI sets this for the browser-parity job; local runs typically don't need it.  See [TESTING.md](TESTING.md) for the broader test layout.

## `VERA_EAGER_GC`

A diagnostic knob for hunting GC-rooting bugs in the WASM codegen.  Set to `1`, `true`, `yes` or `on` (case-insensitive, surrounding whitespace ignored) at **compile time** to make the emitted `$alloc` function call `$gc_collect` on every allocation, regardless of memory pressure:

```bash
VERA_EAGER_GC=1 vera run program.vera
```

Read by `vera/codegen/assembly.py::AssemblyMixin._emit_alloc`; affects the WAT that `vera compile` emits, not the runtime behaviour of an already-compiled module.

**When to use it.**  The conservative mark-sweep collector marks only from the shadow stack (`$gc_sp`); WAT locals are not roots.  If a heap pointer is held only in a WAT local across an allocation, the allocation can trigger a GC that reclaims the still-needed object — the resulting use-after-free typically only manifests at scale, when heap pressure is high enough to fire `$gc_collect` at the wrong moment.  Eager-GC collapses this from "fires occasionally at scale" to "fires on the very next allocation," giving a sharp signal for diagnosis.

This was the diagnostic that cracked [#593](https://github.com/aallan/vera/issues/593): the rebuilt minimum reproducer crashed at generation 0 under `VERA_EAGER_GC=1` rather than around generation 20 without it, and the much smaller stack trace pinpointed the missing return-value root in `_compile_lifted_closure`.

**Cost.**  Programs run orders of magnitude slower with `$gc_collect` on every allocation — never enable it in production or in normal test runs.  It's a debugging knob, not a release-build option.  Tests that exercise this knob live in `tests/test_codegen_closures.py::TestClosureReturnShadowPushBalance`.

## `VERA_DEBUG_HOST_ERRORS`

A diagnostic knob for debugging the host bindings themselves.  Set to `1`, `true`, `yes` or `on` — the same spellings [`VERA_EAGER_GC`](#vera_eager_gc) accepts, because both read the one predicate in `vera/envflags.py` — to make `execute()` re-raise a host callback's original Python exception instead of converting it to a `WasmTrapError`:

```bash
VERA_DEBUG_HOST_ERRORS=1 vera run program.vera
```

Read by `vera/codegen/api.py::execute`; affects how a failure is *presented*, never whether one happens.

**When to use it.**  [#1302](https://github.com/aallan/vera/issues/1302) made every exception escaping the guest invocation arrive as a classified Vera error — a one-line `Error:` with the host's own sentence, the captured `stdout`, and a source backtrace — because a user-level program must never produce a Python traceback regardless of what it does.  That is right for someone running a Vera program and unhelpful for someone who suspects the *binding* is wrong: the sentence survives, the Python frames that say where in the binding it came from do not.  They remain on the exception's `__cause__`, which serves a library caller and not a person reading a terminal.  This knob puts the frames back.

**Cost.**  None at runtime — the variable is read only on the failure path, and only after a host callback has already raised.  It is still a debugging knob rather than a mode, and it disables more than a message.  With it set, a program that would have exited with a clean Vera diagnostic exits with an interpreter traceback instead, so nothing that parses `vera run` output should be run under it — and `vera serve` reverts to its pre-[#1302](https://github.com/aallan/vera/issues/1302) behaviour, where the raw exception bypasses the `WasmTrapError` handler that answers the request, leaving the connection unanswered rather than returning a 500.  The knob turns off the stronger invariant, not just the prettier output.  Tests that exercise this knob live in `tests/test_runtime_traps.py::TestHostErrorDebugKnob1302`.

## Adding a new environment variable

When adding a new `VERA_*` variable to the codebase:

1. Add a row to the table at the top of this document.
2. Add a section explaining purpose, phase (compile-time / runtime / dev), and an example.
3. If it's user-facing (runtime), mention it in [README.md](README.md) and the relevant agent-facing docs ([SKILL.md](SKILL.md), [AGENTS.md](AGENTS.md)).  If it's dev-only, mention it in [CONTRIBUTING.md](CONTRIBUTING.md) and [TESTING.md](TESTING.md).  Other docs link here for the full reference rather than duplicating the explanation.

Keeping the catalogue centralised stops `VERA_*` variables from drifting into one-line mentions scattered across half a dozen documents — the failure mode that motivated creating this file in the first place.
