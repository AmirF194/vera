# State/Exn handler-machinery probe corpus

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

Layout — one directory per probed surface.  Each probe is filed by what
it exercises; the per-file index's Origin column records the
review-round directory it came from.

| Directory | What lives there |
|---|---|
| `alias_families/` | Scalar/refined/parameterised aliases as the `State<T>`/`Exn<E>` argument: family naming and collapse, WASM value types, family registration, cross-module alias tables, alias depth chains, composite and pair-type families |
| `clause_scoping/` | Clause slot binding: pattern/annotation names, mixed alias spellings, patternless clauses, De Bruijn order, declaration-scope resolution, clause-body lets/shadowing/closures, refined-class spellings, resume placement, with-update ordering, clause-env capture lifetime (GC rooting) |
| `dispatch_paths/` | Bare vs clause-inlined vs qualified `put`/`get` parity, user-fn shadowing of op names, re-entrant ops in clause bodies, ops performed from closures, stateless-handler dispatch |
| `write_guards/` | The #1203 write-boundary guards: `@Nat` narrowing and `@Nat`→`@Int` widening at init/put/resume/with, Byte literal widths at every boundary, refined-boundary disclosure, guard-obligation Tier-1 precision |
| `checker_gates/` | Diagnostic gates: E128 quantifier bounds, E336/E533 state-declaration divergence (incl. the generic-handler lie/honest pairs and their lib fixtures), E337 arity, E331/E335 interactions, builtin-effect redefinition, unresolvable-type diagnostics |
| `generic_handlers/` | `forall<T>` + `handle[State<T>]` shapes beyond the E533 gate probes: generic wrappers, instantiation-driving arguments, mono clones reaching codegen's per-family arms |
| `nested_handlers/` | Handler nesting: cell isolation and push/pop, per-family save/restore, registration-walk gaps, clause-body handles, cross-spelled nesting |
| `old_state/` | `old(State<T>)`/`new(State<T>)` snapshot probes in `ensures` |

Module fixtures (`statelib.vera`, `xmod_lib.vera`, `xmod_lib2.vera`,
`e533lib.vera`, `loclib.vera`) sit in the same directory as their
importers — imports resolve relative to the importing file — so each
importer/fixture pair is co-located in the importer's purpose directory.

## Per-file index

One line per probe.  Headed files are condensed from their leading
comment; headerless files are summarised from the program itself.  Origin
is the review-round directory the file lived in before the
purpose-directory reorganisation.

### alias_families/ (50 files)

| File | What it probes | Origin |
|---|---|---|
| `f1_cross_spelling.vera` | Helper declares `State<Option<Int>>`, handler spells `State<MaybeInt>` — do both sites join one cell? | round2_family |
| `g1_array.vera` | `Array<Int>` state cell: put `[5, 6]`, read an element back — heap-value cell baseline | round2_family |
| `p10_xmod_importer_alias.vera` | Importer-declared alias: `handle[State<Nid<Nat>>]` around a module fn declared plain `State<Nat>` | round3_naming |
| `p11_xmod_alias_collision.vera` | Importer's `Hid<T> = Option<T>` collides with the module's private `Hid<T> = T` — per-module tables | round3_naming |
| `p1205.vera` | #1205 repro: `State<Count>` (`Count = Nat`) canonical handler — the scalar-alias cell must collapse to Nat | session |
| `p12_cross_spelling.vera` | Helper declares `State<Count>`, handler spells `State<Nat>` — scalar-alias collapse across the fn boundary | round2_family |
| `p12a_verify_nat_cell.vera` | Obligation-parity baseline: plain Nat cell + a narrowing `let` in the handled body | round3_naming |
| `p12b_verify_alias_cell.vera` | Identical program spelled `State<Id<Nat>>` — the obligation stream must match p12a | round3_naming |
| `p13_exn_cross.vera` | Helper throws `Exn<Code>`, handler spells `Exn<Int>` — Exn scalar-alias cross-spelling | round2_family |
| `p15_generic_elem.vera` | `get(())` as an array element in a generic call, under an alias cell | round2_family |
| `p15b_append.vera` | `get(())` as an `array_append` argument under an alias cell — builtin call-site typing | round2_family |
| `p15c_direct.vera` | p15_generic_elem respelled with a plain `State<Nat>` cell — no-alias control | round2_family |
| `p16_family_split_crosstalk.vera` | Helper effects spelled `State<Id<Id<Nat>>>` vs `handle[State<Nat>]` — ops may silently bypass the cell | round3_naming |
| `p16c_family_split_control.vera` | Single-`Id` control for p16 (`State<Id<Nat>>` spelling) — must join the handler's cell | round3_naming |
| `p17_wrapper_alias.vera` | Wrapper alias `Two<T> = Id<Id<T>>` — head re-entry reached through one user application | round3_naming |
| `p17b_state_string_minimal.vera` | Minimal `State<String>` in a pure fn — pair-family registration refusal vs the emitted calls | round3_clause_env |
| `p22_param_alias.vera` | Parameterised alias cell `State<Id<Nat>>`, single application — put/get roundtrip | round2_family |
| `p23_alias_of_generic.vera` | Scalar alias OF a parameterised alias (`IdN = Id<Nat>`) as the cell type | round2_family |
| `p24_exn_generic.vera` | `Exn<Id<Int>>` with an alias-spelled throw pattern — parameterised-alias payload | round2_family |
| `p25_refined_cell.vera` | Refined-alias cell, in-bounds put — happy path | round2_family |
| `p2_chain.vera` | Two-hop scalar alias chain (`A = B`, `B = Nat`) as the cell — multi-hop family collapse | round2_family |
| `p2_family_nested_alias.vera` | `State<Id<Id<Nat>>>`: resolver seen-set stops at the 2nd `Id` (opaque family) vs full WASM-type recursion | round3_naming |
| `p2b_chain_fwd.vera` | Forward-declared alias chain (`A = B` before `B = Nat`) — declaration-order robustness | round2_family |
| `p2b_family_nested_alias_canonrefs.vera` | Same cell, refs spelled `Id<Nat>` (the both-sides key) — isolates the family-name/WASM-type question | round3_naming |
| `p2c_family_param_alias_control.vera` | `State<Id<Nat>>` single application — the commit's headline fixed case, must run to 7 | round3_naming |
| `p3_scalars.vera` | `Bool`/`Byte`/`Float64` scalar-alias cells in one program — per-family roundtrips | round2_family |
| `p3a_self_param_cycle.vera` | Self-referential parameterised alias `Loop<T> = Loop<T>` — reject, or codegen hang? | round3_naming |
| `p3b_byte_direct.vera` | Plain `State<Byte>` put/get roundtrip from a fn param — Byte width control | round2_family |
| `p3b_mutual_param_cycle.vera` | Mutual parameterised alias cycle `A<T> = B<T>`, `B<T> = A<T>` | round3_naming |
| `p3c_byte_alias.vera` | Byte behind a scalar alias (`Level = Byte`) — aliased Byte-cell roundtrip | round2_family |
| `p3d_bool_float.vera` | `Bool` + `Float64` alias cells only — non-Int scalar families without Byte | round2_family |
| `p6_main.vera` | Cross-module: imports `statelib` (`Count = Nat` there) beside a local `Count = Int` — per-module alias tables | round2_family |
| `p7_exn_scalar.vera` | `Exn<Code>` throw/catch with matching alias spellings and a delegated thrower | round2_family |
| `p7_fn_alias_state_arg.vera` | FnType-bodied alias as the State type argument — alias resolution returns None, opaque family fallback | round3_naming |
| `p7a_array.vera` | `get(())` as an array-literal element under an alias cell — result type must reach i64 via the family | round2_family |
| `p7b_match.vera` | `get(())` as a match scrutinee (int patterns) under an alias cell | round2_family |
| `p7c_composite_alias.vera` | Composite alias cell (`MaybeInt = Option<Int>`, opaque family) + match scrutinee | round2_family |
| `p7d_eq.vera` | `get(()) == get(())` equality dispatch under an alias cell | round2_family |
| `p8_exn_string.vera` | `Exn<Name>` (`Name = String`): string payload through an alias — pair-type payload | round2_family |
| `p8_xmod_alias_family.vera` | Module-private parameterised alias family — registration and lowering must agree it collapses to Nat | round3_naming |
| `p9_composite.vera` | Composite alias cell baseline: `put(Some(41))` + match | round2_family |
| `p9_exn_nested_alias.vera` | Exn twin of p2b: `Exn<Id<Id<Int>>>` — the tag family resolves through the same seen-set walk | round3_naming |
| `p9_refined_state_minimal.vera` | Minimal `State<refined alias>` — does it compile at all? | round2_family |
| `p_byte.vera` | `State<Byte>` fed via `int_to_byte` conversions — Byte roundtrip without bare int literals | session |
| `p_exnalias.vera` | `Exn<Code>` (`Code = Int`) with an alias-spelled throw pattern — Exn scalar-alias collapse | session |
| `p_nested_app.vera` | `State<Id<Id<Nat>>>` nested alias application — head-re-entry cell, fix acceptance | session |
| `statelib.vera` | Module fixture for p6_main: `bump()` handling `State<Count>` (`Count = Nat`) | round2_family |
| `x1_exn_string_alias.vera` | `Exn<Msg>` (`Msg = String`): pair-ness of the alias family — (ptr,len) desync probe | round2_family |
| `xmod_lib.vera` | Module fixture: `tally()` handles `State<Hid<Nat>>` via a private alias (support for p8/p11) | round3_naming |
| `xmod_lib2.vera` | Module fixture: `bump()` declaring plain `<State<Nat>>` effects (support for p10) | round3_naming |

### clause_scoping/ (62 files)

| File | What it probes | Origin |
|---|---|---|
| `a10a.vera` | Patternless `put()` + alias decl + fn `@Nat` param: with-expr `@Nat.0` = fn param vs codegen's arg fallback | round2_family |
| `a10b.vera` | Patternless `put()` with no outer Nat binding — with-expr `@Nat.0` must be E130 | round2_family |
| `a10c_stateless_patternless.vera` | Patternless `put()` under a stateless handler — fn param vs arg fallback, observed via division trap | round2_family |
| `a11_refined_pattern.vera` | Refinement-typed clause pattern `@Nat{self >= 0}` — both sides must erase to the base name | round2_family |
| `a1a.vera` | All names split: `State<Nat>` cell, `@Count` decl, `put(@Nat)` pattern, cross-name with-update | round2_family |
| `a1b.vera` | Swapped spellings: `State<Count>` cell, `@Nat` decl, `put(@Count)` pattern | round2_family |
| `a1c.vera` | Full collision under the alias (`Count` everywhere): `@Count.0` = state, `.1` = put arg | round2_family |
| `a1d.vera` | Collision at the base name (`Nat` everywhere) — De Bruijn order state-then-arg | round2_family |
| `a2a.vera` | Stateless get clause: `@Nat.0` = enclosing fn param, not a captured cell value | round2_family |
| `a2b.vera` | Stateless put clause: `@Nat.0` = the op arg, distinguished by a `10 / @Nat.0` trap | round2_family |
| `a3a.vera` | Keep-old-state `with @Nat = @Nat.0` under full name collision | round2_family |
| `a3b.vera` | Keep-old-state spelled via the alias declaration name (`@Count`) | round2_family |
| `a6a.vera` | Stateful get clause reading state by the declaration name (decl != cell spelling) | round2_family |
| `a6b.vera` | Get clause refs `@Nat.0` under a `@Count` decl + outer fn `@Nat` param — fn param, not the state | round2_family |
| `a9a.vera` | Call-site env shift: clause `@Nat.1` = fn param per checker; a body `let` must not shift it | round2_family |
| `a9c.vera` | Control for a9a: no fn Nat param, so clause `@Nat.1` must be E130 despite a body `let @Nat` | round2_family |
| `e1_exn_alias_arg.vera` | Exn clause pattern spells an alias arg (`@Option<Cnt>`): canonical payload key vs opaque codegen key | round2_family |
| `e1c_control.vera` | e1 without the fn `Option<Int>` param — a misbound payload ref must dangle loudly | round2_family |
| `e2_exn_patternless.vera` | Patternless `throw()` clause: `@Int.0` = fn param (checker) vs thrown payload (codegen fallback) | round2_family |
| `e2c_control.vera` | e2 without the fn Int param — a fallback-bound payload would make `@Int.0` dangle | round2_family |
| `e3_exn_scalar_alias.vera` | Scalar-alias throw pattern `@Code` (`Code = Int`): payload binds under "Code", mixed with a fn param | round2_family |
| `g1_stateless_gc.vera` | Stateless composite put clause that allocates — the arg must stay GC-rooted across the clause body | round2_family |
| `g2_stateful_gc.vera` | Stateful composite keep-old whose clause body allocates — the pre-store capture must survive GC | round2_family |
| `match_tail.vera` | Get clause resumes inside a match-arm tail (`@Int.0` = fn param) — tail descent through match | round2_clauses |
| `nested_int.vera` | Nested Nat/Int handlers: inner get clause reaches `@Int.1` (the fn param past the state slot) | round2_clauses |
| `p10_exn.vera` | Exn clause env: patternless `throw()` binds nothing (decl-let) vs a with-param payload variant | round3_clause_env |
| `p11_alias_with_clause.vera` | Mixed names: `@Count` decl, `put(@Nat)` pattern, `with @Count = @Nat.0` | round2_family |
| `p11_exn_resume.vera` | `resume` inside an `Exn` throw clause — checkable at all? | round2_family |
| `p12_getwith.vera` | Get clause WITH a with-update — clause value vs post-resume update ordering (50 then 60) | round3_clause_env |
| `p13_param_alias_arg.vera` | Parameterised alias in clause-pattern ARG position, single application — `.1` = put arg, value 9 | round3_naming |
| `p14_composite_gc.vera` | Composite cell clause under decl-env with an allocating body + closure — state capture must stay rooted | round3_clause_env |
| `p14_tuple_alias_arg.vera` | Tuple pattern with one alias component — `put(@Tuple<Cnt, Int>)` binds canonical `Tuple<Int, Int>` | round3_naming |
| `p15_resume_in_with.vera` | `resume` smuggled into the WITH expr — the lowerability scan counts only clause-body resumes | round3_clause_env |
| `p16_with_update.vera` | `with @Count = @Count.1 + @Count.0` — with-update mixing state and arg slots under an alias | round2_family |
| `p16b_noncomm.vera` | Non-commutative with-update (`@Count.0 * 2 + @Count.1`) — pins which index is state vs arg | round2_family |
| `p16c_mixed_names.vera` | `@Nat` decl under `State<Count>` with `put(@Count)` and a mixed-name with-expr | round2_family |
| `p18b_skew.vera` | Stateless get-only handler: clause `@Int.0` = fn param (42) — stateless clause-env skew | round2_family |
| `p1_decl_scope.vera` | Clause refs past its own bindings resolve at handler-DECLARATION scope, not the call site's lets | round3_clause_env |
| `p1a_nested_alias_clause_e699.vera` | Pattern `@Option<Id<Id<Int>>>`, body ref `.1` — a codegen misbind makes the ref dangle (E699) | round3_naming |
| `p1b_nested_alias_clause_value.vera` | Silent wrong-value twin: with-ref `@Option<Id<Int>>.0` — checker keep-old 5 vs misbound put-arg 9 | round3_naming |
| `p1b_two_sites.vera` | The same get clause inlined at two let-depths must behave identically (difference 0) | round3_clause_env |
| `p1c_keepold_canonical_control.vera` | Canonical spellings only: `with ... = @Option<Int>.0` is keep-old (5) — pins index 0 = state | round3_naming |
| `p1d_single_alias_ref.vera` | Single alias application with an alias-SPELLED with-ref — expected loud E699 (#1208 class) | round3_naming |
| `p21_handle_in_closure.vera` | Full handle inside a lifted closure — the clause reaches the closure's param as its decl scope | round3_clause_env |
| `p3_closure.vera` | Closure in a clause body capturing the state slot AND a decl-scope slot; body distractor must not leak | round3_clause_env |
| `p4_refined_arg_clause.vera` | Refined type-arg inside a composite (`Option<Pos>`) — predicate-elided bind key vs syntactic ref side | round3_naming |
| `p4a_composite_plain.vera` | Baseline: composite `State<Option<Int>>` with no aliases anywhere | round2_clauses |
| `p4b_alias_arg_pattern.vera` | Alias inside a composite clause pattern — checker-canonical slot key vs codegen's opaque key | round2_clauses |
| `p4c_alias_arg_dangling.vera` | Same shape, ref spelled `@Option<Int>.1` (checker: the put arg) — should dangle on the codegen side | round2_clauses |
| `p4d_alias_annotation.vera` | Alias inside the composite state DECLARATION — natural body ref misses codegen's opaque key | round2_clauses |
| `p4e_fn_param_baseline.vera` | Ordinary fn param `@Option<Cnt>` with a canonical-spelled ref — is the naming split pre-existing? | round2_clauses |
| `p5_e130_gate.vera` | With-expr ref past the clause scope (`@Int.2`) must be E130 — the old call-site env would resolve it | round3_clause_env |
| `p5_mainline_alias_arg_control.vera` | The commit's fixed mainline: `put(@Option<Cnt>)` + canonical `.1` ref — green, value 9 | round3_naming |
| `p5b_e130_clause_body.vera` | Clause-body ref past its own bindings with an EMPTY decl scope (`@Int.1`) — expect E130 | round3_clause_env |
| `p6_alias_of_composite_arg.vera` | Arg is an alias OF a composite (`MaybeInt = Option<Int>`) under an `Option<Option<Int>>` cell | round3_naming |
| `p6_two_puts.vera` | One put clause (with `with`) inlined at two call-site let-depths — with-expr scope stability | round3_clause_env |
| `p7_patternless_put.vera` | Patternless `put()` WITH state declared — the checker binds only the state, never the arg | round3_clause_env |
| `p8_match_tail.vera` | Tail resume under a single-arm match on a clause that ALSO has `with` — descent + update ordering | round3_clause_env |
| `p_annalias.vera` | Alias declaration (`@Count`) on a base-spelled `State<Nat>` cell | session |
| `p_effparams.vera` | User effect `Pair<A, B>` handled at `<Int, Bool>` — clause binding for a two-parameter user effect | session |
| `p_exnpat.vera` | `Exn<Code>` with the pattern spelled at the resolved base (`throw(@Int)`) | session |
| `p_putpat.vera` | Put pattern spelled `@Count` under a `State<Nat>` cell — the alias pattern must bind canonically | session |

### dispatch_paths/ (12 files)

| File | What it probes | Origin |
|---|---|---|
| `p12_delegated_put.vera` | Bare put in a delegating fn, caller handles with clauses — dispatch-path parity | round2_family |
| `p18_stateless.vera` | Stateless put-clause handler: `put(-7)` then `get` — uninitialised-cell read path | round2_family |
| `p20_closure_put.vera` | Closure in the handled body performing `put` — inlining in the lifted fn would bind the wrong decl-env | round3_clause_env |
| `p20b_applyfn_put.vera` | Let-bound effectful closure applied via `apply_fn` inside the handled body — admitted at all? | round3_clause_env |
| `p3_put_in_clause_body.vera` | `put` inside a get-clause body — clause-op env cleared, bare path despite an existing put clause | round2_family |
| `p9_cross_family.vera` | Bare `put` inside the nested handler's put clause — checker types it against the OUTER handler | round3_clause_env |
| `p_qualput.vera` | Qualified `State.put(4)` dispatching through a doubling with-clause — qualified/bare parity | session |
| `p_skew.vera` | Stateless put-clause handler asserting the arg (== 7) then `get` — stateless dispatch + uninit read | session |
| `p_stateless.vera` | Stateless `State<Int>` put/get: `put(7)` then `get` — minimal stateless baseline | session |
| `p_stateless_ref.vera` | Stateless put clause whose body re-puts `@Int.0 + 100` — a put from within the put clause itself | session |
| `w_put.vera` | Where-helper NAMED `put` — does the effect-op fallback misfire on a non-effect call? | round2_family |
| `w_resume.vera` | Where-helper named `resume` — reserved-name misfire twin | round2_family |

### write_guards/ (60 files)

| File | What it probes | Origin |
|---|---|---|
| `bare_obs.vera` | Bare `put(@Int.0)` into a Nat cell (get-only handler), observed via a `get(()) > 100` branch | round2_clauses |
| `byte_arg_if.vera` | If-expression flowing into a `@Byte` fn argument — literal width through a branch | round3_gates |
| `byte_bare33.vera` | Bare `put(33)` into a Byte cell (get-only handler) — Byte literal width on the bare path | round3_clause_env |
| `byte_bare_put.vera` | Bare `put(200)` (no put clause) into a Byte cell — in-range bare-path literal, expects 200 | round3_gates |
| `byte_delegated_put.vera` | `put(150)` delegated through a `<State<Byte>>` helper — cross-fn Byte literal width | round3_gates |
| `byte_init999.vera` | Byte cell init literal 999 — out-of-range width at the init boundary | round3_gates |
| `byte_init_if.vera` | Byte init from an if-expression — non-literal init width | round3_gates |
| `byte_let999.vera` | `let @Byte = 999` — out-of-range Byte literal in a plain let (control outside handlers) | round3_gates |
| `byte_let_if.vera` | `let @Byte =` an if-expression — branch-literal narrowing control | round3_gates |
| `byte_neg_composite.vera` | `put(0 - 5)` composite negative expression into a Byte cell | round3_gates |
| `byte_put42.vera` | Clause-dispatched `put(42)` into a Byte cell — literal width through the clause path | round3_clause_env |
| `byte_put999.vera` | Clause-dispatched `put(999)` — out-of-range literal through the clause path | round3_gates |
| `byte_put_arith.vera` | `put(1 + 2)` arithmetic expression into a Byte cell | round3_gates |
| `byte_put_if.vera` | `put(if ...)` branch expression into a Byte cell | round3_gates |
| `byte_refined_alias.vera` | Refined-Byte alias cell (`SmallByte`), in-range put — expects 3 | round3_gates |
| `byte_refined_violating.vera` | Refined-Byte alias (`Tiny < 10`) with init 200 — init violates the refinement | round3_gates |
| `byte_resume300.vera` | Get clause resumes 300 — out-of-Byte-range resume literal | round3_gates |
| `byte_resume9.vera` | Get clause resumes the literal 9 into a Byte cell — resume-boundary literal width | round3_clause_env |
| `byte_resume_arith.vera` | `resume(1 + 2)` arithmetic in a Byte get clause | round3_gates |
| `byte_resume_if.vera` | `resume(if ...)` branch expression in a Byte get clause | round3_gates |
| `byte_resume_lit.vera` | `resume(99)` in-range literal — expects 99, the resume-literal control | round3_gates |
| `byte_roundtrip.vera` | `put(200)` / `get` roundtrip — in-range Byte cell baseline, expects 200 | round3_gates |
| `byte_with77.vera` | `with @Byte = 77` — literal width at the with-update boundary | round3_clause_env |
| `byte_with_lit.vera` | `with @Byte = 42` literal with-update — expects 42 | round3_gates |
| `d1_literals.vera` | Literal negatives at all four `@Nat` write boundaries (init/put/resume/with) — all must be loud | round2_family |
| `d2_block_tail_resume.vera` | `resume` in a Block tail after a preceding `let` — narrowing guard still applied | round2_family |
| `mut_put.vera` | The project's `_PUT` differential fixture with its put clause removed — bare-path negative put | round2_family |
| `p1.vera` | `put(@Int.0)` into a Nat cell, get-only handler — bare intrinsic path, negative arg | round2_family |
| `p10_alias_nat_state.vera` | Unrefined alias cell (`MyNat = Nat`), bare-path put of an SMT-opaque negative | round2_family |
| `p1205_neg.vera` | The #1205 shape with the init taken from an `@Int` fn arg — negative-init guard on the alias cell | session |
| `p19_guard_bareput.vera` | Bare put of a negative via a delegated `<State<Count>>` effect, get-only handler — boundary guard | round2_family |
| `p1_put_no_clause.vera` | Bare-path put of an SMT-opaque runtime negative (`get() - 100`) — bare-path guard probe | round2_family |
| `p1_put_noclause.vera` | `put(@Int.0)` with an EMPTY clause list — clause-free handler still takes the bare path | round2_family |
| `p2.vera` | Negative through a `@Nat` cell observed as `get(()) < 0` — no later boundary guard can mask it | round2_family |
| `p20_guard_init.vera` | State init from a negative fn arg (`@Count = @Int.0`) — init-boundary narrowing trap | round2_family |
| `p21_guard_resume.vera` | Get clause resumes a negative fn arg — resume-boundary narrowing trap | round2_family |
| `p2_put_with_clause.vera` | p1_put_no_clause control WITH a put clause — the clause-inlined guard path (#1203) | round2_family |
| `p3.vera` | Tier-3 put arg (`Random.random_int` negative), bare path — fallback must record guarded=True | round2_family |
| `p4.vera` | p3 WITH a put clause — differential: clause-inlined guard vs the bare path | round2_family |
| `p4_custom_effect_resume.vera` | User effect op returning Nat; clause resumes a negative Int — guard on a non-builtin resume | round2_family |
| `p4_refined.vera` | Alias-of-refined-alias chain (`Pos2 = Pos`), requires-protected put — Tier-1 discharge through the chain | round2_family |
| `p4c_byte_with.vera` | Byte literal at every write boundary in one handler: init 1, put-arg 3, with-override 200 | round3_clause_env |
| `p5_exn.vera` | `resume` of a negative inside an `Exn` throw clause — is the fallback's guarded=True truthful? | round2_family |
| `p5_get_resume_guard.vera` | Get clause resumes an SMT-opaque negative (`@Nat.0 - 50`) — resume guard must trap | round2_family |
| `p6.vera` | Get clause resumes a Tier-3 Random negative — resume-boundary guard on an untranslatable value | round2_family |
| `p6_init_guard_control.vera` | SMT-opaque negative state INIT (outer `get() - 50`) — the init guard must trap | round2_family |
| `p7_with_update_control.vera` | `with @Nat =` an SMT-opaque negative — the with-update guard must trap | round2_family |
| `p8_refined_state.vera` | Refined-alias cell whose init violates the predicate at runtime (SMT-opaque) — does anything trap? | round2_family |
| `p8_resume_guard.vera` | Get clause resumes a negative fn arg through an alias cell — the Nat bind guard must trap | round2_family |
| `p8b_positive.vera` | p8_resume_guard with a positive arg — the guard must not false-trap | round2_family |
| `p_bytelet.vera` | `let @Byte = 7` then `byte_to_int` — plain Byte let-literal control | session |
| `p_bytewith.vera` | Byte literals at init (5), with-update (77), and put (1) — widths at every clause boundary | session |
| `p_qualput_neg.vera` | Qualified `State.put` of a negative with a get-only handler — qualified bare-path guard | session |
| `pr_alias.vera` | Negative put through an alias cell, observed as Bool — alias-path guard differential | round2_family |
| `pr_alias_min.vera` | Get-only alias cell observed as Bool — minimal alias control | round2_family |
| `pr_init.vera` | State-init guard vs the value riding the operand stack across the cell push | round2_family |
| `pr_init_req.vera` | An enclosing `requires(@Int.0 >= 0)` must discharge the init obligation Tier-1 — precision | round2_family |
| `pr_upd_req.vera` | Keep-old with-update obligation under a FRESH clause env — precision | round2_family |
| `pr_update.vera` | `with @Nat =` a Tier-3 Random negative — with-update narrowing guard | round2_family |
| `widen_ok.vera` | `@Nat` value into a `State<Int>` cell — the widen dual must not false-trap | round2_family |

### checker_gates/ (78 files)

| File | What it probes | Origin |
|---|---|---|
| `ctrl_unresolved_let.vera` | Neutral control: `let` bound to an unresolved call (`no_such_fn`), no handler involved | round2_family |
| `diverge.vera` | Divergent `@Int` decl on a `State<Nat>` cell (get-only, resumes 0) — decl/effect-arg split | round2_family |
| `diverge2.vera` | Divergent `@Int` decl; get clause resumes the state slot — echoes a negative init through the Nat cell | round2_family |
| `diverge3.vera` | Divergent `@Int` decl with a put-clause-only handler — bare `get` under a negative Int init | round2_family |
| `e128_array.vera` | E128 gate: `forall` over an `@Array<Int>` domain, predicate lambda carrying contract clauses | round2_family |
| `e128_bool.vera` | E128 gate: `@Bool` quantifier domain | round2_family |
| `e128_byte.vera` | E128 gate: `@Byte` quantifier domain | round2_family |
| `e128_byte_run.vera` | E128 gate: `@Byte` domain with a real predicate and `main` — runnable variant | round2_family |
| `e128_float.vera` | E128 gate: `@Float` quantifier domain | round2_family |
| `e128_float64.vera` | E128 gate: `@Float64` quantifier domain | round2_family |
| `e128_typevar.vera` | E128 gate: `@T` (TypeVar) domain in a generic fn, instantiated at Int | round2_family |
| `e128_unresolved.vera` | E128 gate: domain is an unresolved call — gate vs unresolved-name ordering | round2_family |
| `e336_flipped.vera` | Refinements `@Nat.0 < 10` vs `10 > @Nat.0` — semantically equal, syntactically flipped spellings | round3_gates |
| `e336_in_generic.vera` | Divergent `@Nat` decl under `handle[State<Int>]` inside a generic fn — the gate in generic context | round3_gates |
| `e336_nongeneric_verify.vera` | Divergent `@Int` decl under `State<Nat>` in a plain fn — the non-generic baseline | round3_gates |
| `e336_paren.vera` | Parenthesised vs bare refinement predicate — the equality must not be paren-sensitive | round3_gates |
| `e336_ws.vera` | Whitespace-only refinement spelling difference — must still be resolve-equal | round3_gates |
| `e337_bare_exn.vera` | `handle[Exn]` with no type argument — arity gate for Exn | round3_gates |
| `e337_bare_state_decl.vera` | Bare `handle[State]` with a state declaration — arity gate for State | round3_gates |
| `e337_exn_two.vera` | `Exn<String, Int>` — two type arguments on Exn | round3_gates |
| `e337_twoargs_badclause.vera` | `State<Int, Nat>` plus bogus clause refs (`@Int.5`, `@Bogus.0`) — arity gate before clause errors | round3_gates |
| `e337_user_effect_exn.vera` | User-declared `effect Exn` — builtin-effect redefinition gate | round3_gates |
| `e533_import.vera` | Generic state-decl lie imported cross-module — E533 must fire at the importer's instantiation | round3_gates |
| `e533_indirect.vera` | The lie reached through an intermediate generic fn — E533 through instantiation indirection | round3_gates |
| `e533_match_arm.vera` | The lying handler inside a match arm of the generic — the E533 walker must descend match arms | round3_gates |
| `e533_mixed.vera` | `@Int` decl under `State<T>`, instantiated at both Int and Nat — per-instantiation verdicts | round3_gates |
| `e533_nat.vera` | The canonical lie: `@Nat = 3` under `State<T>` instantiated at Int — mainline E533 probe | round3_gates |
| `e533_two_fail.vera` | Instantiated at Int and Float64, decl `@Nat` — two mismatching instantiations to report | round3_gates |
| `e533_uninstantiated.vera` | The lying generic is never called — is uninstantiated code gated? | round3_gates |
| `e533_where.vera` | The lie inside a where-helper generic — E533 in where scope | round3_gates |
| `e533lib.vera` | Module fixture: public generic `sneak` with the `@Nat` state-decl lie (support for e533_import) | round3_gates |
| `loc_import.vera` | Importer calling `loclib.bad` — cross-module location attribution for a verify failure | round3_gates |
| `loclib.vera` | Module fixture: generic `bad()` with a false `ensures(@Int.result == 2)` — the failure source | round3_gates |
| `mismatch.vera` | Is the state-decl type cross-checked against `State<T>`'s T at all? (`@Int` decl, Nat cell) | round2_family |
| `n1_e336.vera` | E336 sanity: divergent (non-resolve-equal) `@Int` decl under `State<Nat>` must be rejected | round2_family |
| `p10b_refined_cell_msg.vera` | Inline-refined cell with a plain `@Nat` decl — refined-vs-base divergence boundary/message | round2_family |
| `p1206.vera` | #1206 repro: divergent `@Int` decl under `State<Nat>`, observed via `get(()) < 0` | session |
| `p1_generic_divergent.vera` | Generic handler declaring `@Int = -7` under `State<T>` — state-decl lie at a Nat instantiation | round2_family |
| `p1b_generic_doc_lie.vera` | Generic `@Nat = 3` state-decl lie under `State<T>`, called at a negative Int (E533 shape) | round2_family |
| `p1c_generic_honest.vera` | Honest generic control `@T = @T.0` — a negative Int flows through legitimately | round2_family |
| `p1d_generic_doc_lie_int.vera` | The doc lie with an explicit Int-instantiating wrapper — E533 must catch the instantiation | round2_family |
| `p26_refined_diverge.vera` | Cell `Small`, decl `Big` (different refinements of Nat) — refined-divergence acceptance | round2_family |
| `p2_refined_refined.vera` | Inline-refined cell and inline-refined decl with divergent predicates | round2_family |
| `p2b_contradictory.vera` | Inline decl refinement `> 999` contradicts cell `< 10` (init 5) — decl predicate violated | round2_family |
| `p2c_matching_refined.vera` | Cell and decl spell the identical inline refinement — resolve-equal acceptance control | round2_family |
| `p2d_named_refined_alias.vera` | One named refined alias (`Small`) for both cell and decl — canonical happy path | round2_family |
| `p3_alias_pair.vera` | Sibling aliases of Nat: `A` cell, `B` decl, `put(@A)` — resolve-equal across distinct aliases | round2_family |
| `p3b_refined_alias_divergent.vera` | Refined aliases with opposite predicates (`P > 0` cell, `Q < 0` decl, init -5) | round2_family |
| `p4_user_state.vera` | User-declared `effect State` — builtin-effect redefinition gate | round2_family |
| `p5a_unknown_annot.vera` | State decl names an unknown type (`@Bogus`) — unresolvable-declaration diagnostic | round2_family |
| `p5b_unknown_cell.vera` | `State<Bogus>` unknown cell type — unresolvable-cell diagnostic | round2_family |
| `p6_bare_state.vera` | `handle[State]` with no type argument — bare-State arity gate | round2_family |
| `p7_two_args.vera` | `State<Int, Nat>` — two type arguments, arity gate | round2_family |
| `p7b_two_args_divergent.vera` | `State<Int, Nat>` plus a divergent `@Bool` decl — arity and divergence stacked | round2_family |
| `p8_dual_e331_e336.vera` | `@Int = true` under `State<Nat>` — decl/init clash and decl/cell divergence stacked (E331 vs E336) | round2_family |
| `p9a_where_helper.vera` | Divergent `@Int` decl inside a where-helper — the gate must fire in a nested fn context | round2_family |
| `p9b_closure.vera` | Divergent decl inside a let-bound closure body — the gate in a lifted-closure context | round2_family |
| `p9c_nested.vera` | Divergent decl on the INNER of two nested handlers | round2_family |
| `pF1.vera` | Refined lie: `Small` cell declared `@Big` (overlapping refinements) plus a put | session |
| `pF1_runnable_lie.vera` | Runnable refined lie: `Small` cell declared `@Big`, plus a put — pins the refined side of the decl gate | round2_family |
| `pF1b.vera` | `Small` vs `Small2` — identical predicates under different alias names, resolve-equal acceptance | session |
| `p_refalias.vera` | Refined alias `Pos` as cell with a matching `@Pos` decl — refined-alias happy path | session |
| `p_refann.vera` | Inline refinement as the state DECLARATION over a plain Nat cell | session |
| `p_refarg.vera` | Inline refinement as the cell TYPE ARGUMENT with a plain `@Nat` decl | session |
| `q_adt.vera` | Quantifier domain `@Option<Int>` — ADT domain for the E128 gate | round2_family |
| `q_bool.vera` | Quantifier domain `@Bool` | round2_family |
| `q_byte.vera` | Quantifier domain `@Byte` | round2_family |
| `q_float.vera` | Quantifier domain `@Float64` | round2_family |
| `q_fn.vera` | Quantifier domain is a lambda expression | round2_family |
| `q_map.vera` | Quantifier domain `@Map<String, Int>` | round2_family |
| `q_nat.vera` | Quantifier domain `@Nat` | round2_family |
| `q_refined_ok.vera` | Quantifier domain: refined-Int alias (`PosInt`) | round2_family |
| `q_refined_str.vera` | Quantifier domain: refined-String alias (`NonEmpty`) | round2_family |
| `q_string.vera` | `exists` over a `@String` domain | round2_family |
| `q_typevar.vera` | TypeVar domain instantiated to `Array<Int>` at the call site — legitimate generic domain | round2_family |
| `q_typevar_int.vera` | TypeVar domain instantiated to `Int` — is the mono program legitimate? | round2_family |
| `q_unit.vera` | Quantifier domain is the literal `()` | round2_family |
| `q_unknown.vera` | Quantifier domain is an unresolved call — gate vs unresolved-name ordering | round2_family |

### generic_handlers/ (3 files)

| File | What it probes | Origin |
|---|---|---|
| `p4d_generic_byte_with.vera` | Generic handler with literal init/with, instantiated at Byte — the mono clone must hit the byte arms | round3_clause_env |
| `p4e_generic_with.vera` | Generic `with @T = 201` at Byte — does the generic site skip E335 into codegen's byte-update arm? | round3_clause_env |
| `p_generic.vera` | Honest generic cell handler (`@T = @T.0`) used at Int — generic-handler acceptance control | session |

### nested_handlers/ (13 files)

| File | What it probes | Origin |
|---|---|---|
| `a5a.vera` | Nested same-family handlers (`Nat` outer, `Count = Nat` inner): save/restore + cell push/pop | round2_family |
| `a5b.vera` | Stateless inner handler inside a stateful outer of the same type — inner clauses must see no state slot | round2_family |
| `p11_init_nested.vera` | Full nested handler inside the OUTER state INIT expr — the import walker only descends the body | round3_clause_env |
| `p13_exn_in_clause.vera` | Full nested `Exn` handler inside a State get-clause body — the walker misses clauses, tag unregistered? | round3_clause_env |
| `p17_string_outer.vera` | Which instantiation types a bare `get` in a NESTED handler's clause? outer String vs nested Nat | round3_clause_env |
| `p17c_option_outer.vera` | p17 with a registerable `Option<Int>` outer — i32 vs i64 typing clash on the nested routing | round3_clause_env |
| `p18_byte_in_byte_clause.vera` | Byte handler nested in a Byte get clause — clause-family save/restore must keep both at i32 | round3_clause_env |
| `p19_seq_byte_int.vera` | Int handler nested in the Byte handler's BODY — per-clause family switch and restore | round3_clause_env |
| `p27_nested_cross.vera` | Nested handlers: `Count` outer, `Nat` inner (same family via the alias) — cross-spelled isolation | round2_family |
| `p2a_nest_diff.vera` | Nested Nat handler inside the outer Int GET clause — body lets must not leak into the clause env | round3_clause_env |
| `p2b_nest_same.vera` | Nested SAME-type handler inside the outer get clause — cell push/pop isolation | round3_clause_env |
| `p4a_int_in_byte.vera` | Int handler nested in a Byte GET clause — inner resume stays i64, outer literal path i32 | round3_clause_env |
| `p4b_byte_in_int.vera` | Byte handler nested in an Int GET clause — family restored to Int for the outer tail | round3_clause_env |

### old_state/ (5 files)

| File | What it probes | Origin |
|---|---|---|
| `p10_old_alias.vera` | `ensures` over `old/new(State<Count>)` — verified postcondition on an alias-spelled cell | round2_family |
| `p10b_old_mixed.vera` | `ensures` spells `State<Nat>` while `effects` spells `State<Count>` — mixed spellings must corefer | round2_family |
| `p10c_old_false.vera` | FALSE `ensures new == old` on a bumping fn — must fail verify (alias cell not decoupled) | round2_family |
| `p15_old_state_nested_alias.vera` | `old/new(State<...>)` typing over head-re-entry aliases (single `Id<Nat>` + double `Id<Id<Nat>>`) | round3_naming |
| `p_oldalias.vera` | `ensures new/old(State<Count>)` on an alias-spelled effect — `old()` snapshot naming over aliases | session |
