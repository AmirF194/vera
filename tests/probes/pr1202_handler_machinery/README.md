# PR #1202 handler-machinery probe corpus

The adversarial-review probe programs from PR #1202's review rounds —
the raw corpus behind the roughly thirty defects that PR handled in the
builtin `State`/`Exn` handler machinery (type aliases × handler
combinatorics, clause-scope binding, dispatch-path parity, write-boundary
guards).  Kept verbatim as review evidence and as the promotion pool for
[#1213](https://github.com/aallan/vera/issues/1213): the conformance
suite never covered these shapes, and PR 1 of that consolidation
promotes the distinguishing ones into `tests/conformance/` with manifest
entries.

**Not wired into CI.** These are probe programs, not curated fixtures:
some deliberately fail (`check`, `verify`, or `run`) to demonstrate a
defect that is now fixed, some pin pre-existing open issues (#1207–#1212),
and some were superseded mid-round.  Each file's leading comment states
what it probes and what the expected-vs-observed behaviour was AT THE
TIME it was written; the tracked regression suites
(`tests/test_nat_narrowing_return_differential.py`,
`tests/test_verifier_fresh_scope.py`, `tests/test_checker_types.py`)
carry the maintained, asserted versions of the shapes that mattered.

Layout — one directory per review lens:

| Directory | Round | Lens |
|---|---|---|
| `round2_family/` | 2 | scalar-alias family collapse + E336 gate + E128/E533 probes |
| `round2_clauses/` | 2 | clause-scope slot binding vs the checker |
| `round3_naming/` | 3 | naming/resolution machinery (parameterised aliases, refined args) |
| `round3_clause_env/` | 3 | declaration-env threading, nesting, patternless clauses |
| `round3_gates/` | 3 | E337/E533/Byte-coercion/refined-equality gates |
| `session/` | 1–4 | the main session's own probes (issue repros, fix acceptance) |
