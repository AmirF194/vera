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

What remains is pinned on the open issues [#1207](https://github.com/aallan/vera/issues/1207), [#1212](https://github.com/aallan/vera/issues/1212) and [#1218](https://github.com/aallan/vera/issues/1218). The slot-naming and cell-family shapes ([#1208](https://github.com/aallan/vera/issues/1208), [#1209](https://github.com/aallan/vera/issues/1209), [#1219](https://github.com/aallan/vera/issues/1219)) and the handler-semantics shapes ([#1210](https://github.com/aallan/vera/issues/1210), [#1211](https://github.com/aallan/vera/issues/1211), [#1215](https://github.com/aallan/vera/issues/1215)) have already been through the cycle and live in `tests/conformance/` and the maintained regression suites.
