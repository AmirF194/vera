# tests/probes/ — adversarial-review probe corpus

A **probe** is a small Vera program written during adversarial review to
make one specific compiler behaviour observable: each file's leading
comment (or, failing that, its shape) states what it exercises and what
the expected-vs-observed behaviour was at the time it was written.  The
corpus deliberately includes programs that fail `check`, `verify`, or
`run` — kept as evidence of the defect they demonstrated — which is what
separates it from the curated, asserted suites: `tests/conformance/` and
the `tests/test_*.py` regression files assert current behaviour and run
in CI, while nothing under `tests/probes/` is wired into CI or asserted
by any harness.

The directory exists to keep the review corpus in-repo — greppable,
attributable, and promotable — rather than scattered across session
scratch space: the distinguishing probes are the promotion pool for the
conformance suite, and the rest document exactly which program shapes
each review round used to corner a defect.

Current corpus: [`state_handlers/`](state_handlers/README.md) — the
adversarial-review programs over the builtin `State`/`Exn` handler
machinery from PR #1202's review rounds, organised by the surface each
probe exercises, with a per-file index in its README.

## Lifecycle

**Lifecycle**: this directory is a transitional promotion pool with a defined end-of-life. Every probe is either promoted to CI or deleted; nothing stays here indefinitely. The [#1213](https://github.com/aallan/vera/issues/1213) burndown disposes of them issue by issue — the PR that closes an issue promotes that issue's distinguishing shapes into `tests/conformance/`, folds anything only expressible as a pytest differential into the maintained suites, and deletes the probes it dispositioned. When the last directory empties, this one goes with it; superseded evidence programs are preserved by git history.

What remains is pinned on the open issue [#1207](https://github.com/aallan/vera/issues/1207). The write-boundary shapes ([#1212](https://github.com/aallan/vera/issues/1212)) have been through the cycle — `write_guards/` is retired into `tests/conformance/` (`ch01_byte_literal_join_width`, `ch07_state_byte_join_writes`) and `tests/test_byte_literal_joins_1212.py`, with the rest already covered by the maintained differentials; see the directory README for the per-surface disposition. The slot-naming and cell-family shapes ([#1208](https://github.com/aallan/vera/issues/1208), [#1209](https://github.com/aallan/vera/issues/1209), [#1218](https://github.com/aallan/vera/issues/1218), [#1219](https://github.com/aallan/vera/issues/1219)), the handler-semantics shapes ([#1210](https://github.com/aallan/vera/issues/1210), [#1211](https://github.com/aallan/vera/issues/1211), [#1215](https://github.com/aallan/vera/issues/1215)) and the cross-module contract-reading shapes ([#1220](https://github.com/aallan/vera/issues/1220), [#1225](https://github.com/aallan/vera/issues/1225), [#1226](https://github.com/aallan/vera/issues/1226), whose shapes are pytest differentials over module sets and live in `tests/test_callee_contract_scope_1220_1225_1226.py`) have already been through the cycle and live in `tests/conformance/` and the maintained regression suites.
