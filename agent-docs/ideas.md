# Ideas for future optimization passes

Rewritten from scratch (2026-07-18, entries 101–103 session). Every number here was re-measured
this session: fresh `opt-export` of all 100 SP1 rsp cases at each iteration, diffed per-case
against the checked-in `*.powdr_opt.json.gz` with canonical-polynomial comparison (mod p), plus
the PR #163 CI matrix (all five benchmark sets vs main). Older write-ups had stale or wrong gap
attributions; re-measure before trusting anything, including this file.

## Where we stand (post entries 101–103: interval forcing, basis justification, OR-identity checks)

| benchmark | axis | apc (agg) | powdr (agg) | status |
|---|---|---|---|---|
| sp1/rsp (100) | variables | 3.922× | 3.980× | gap 55 vars over ~20 cases; W/L/T 15/42/43 |
| | bus interactions | 2.703× | 2.822× | gap 319 = memory 180 + byte 139 |
| | constraints | 9.372× | 9.810× | gap 219 (lowest-priority axis) |
| sp1/keccak (1) | variables | 5.163× | 4.809× | **ahead** |
| | bus interactions | 3.017× | 3.137× | 2173 vs powdr's ~2100 |
| openvm-eth (100) | all axes | 4.553× / 3.558× / 10.845× | 4.092× / 3.480× / 5.853× | **ahead on all three** |
| keccak (OpenVM) | bus | 7.587× | 7.648× | 1748 vs 1734; vars/constraints exact parity |
| wasm-eth (100) | vars / con | 7.254× / 15.173× | 6.273× / 9.671× | **ahead** |
| | bus | 6.211× | 5.666× | ahead agg; geo 2.894× vs 2.868× ahead too |

**SP1 rsp is the remaining fight**, and within it: memory-chain telescoping blocked on quadratic
range knowledge (below), then the byte-bus checks, then the long variable tail. The three passes
this session (`intervalForce`, `basisJustified`, the OR-identity byte-check arms) closed var gap
442 → 55 and bus gap 765 → 319 with 0 per-case regressions; the mechanisms are general (each also
improved wasm-eth and/or OpenVM keccak).

## Open ideas, priority order

### 1. Quadratic root domains as bounds (`x·(x − c) = 0 → x ∈ {0, c}`)  ·  *bus + vars, sp1*  ·  high value / medium effort

The single biggest residual class. The un-telescoped SP1 memory chains that remain (apc_030's
register-16 `subw` chain +12, apc_097 +16, apc_037/031/063 +14 each — memory gap ~180 total)
carry data limbs like `subw_operation__value__0_49` whose 16-bit justification is not affine at
all: the value's range comes from **quadratic** relations the subw/comparison gadgets leave
behind, e.g. `(v₄₉ + v₅₁)² = 65536·(v₄₉ + v₅₁)` (so the sum ∈ {0, 65536}) together with borrow
booleanities. powdr's range solver reads quadratic roots; apc's `findVarBound` is bus-fact-only
and `findDomainAlg` only consumes single-variable constraints.

Concretely: an arm that recognizes a constraint linearizing (after normalize) to
`E² − c·E = 0` for an affine form `E` — giving `E ∈ {0, c}` — and feeds it as (a) a domain for
`domainBatch`-style case analysis, or (b) a bound `E ≤ c` consumable by `affineJustified` /
`basisJustified` / `intervalForce` as another basis form. (b) is the cheap slice: extend
`formBoundAt`-style facts with constraint-derived bounded forms (bound `c + 1` for the form `E`).
Same proof shape as `two-term`-era arguments: field equation + integral domain → root set.
The apc_048-style comparison gadgets (+27 vars, the largest single var case) are squared
differences `(a − b)²…` — the same machinery opens them, but the var win there also needs the
gadget collapsed (seqzCollapse-like), so size the bus slice first.

### 2. Basis justification for `SubsumedCheck` (redundant op-6 w=16 drops)  ·  *bus-5, sp1*  ·  medium value / medium effort

apc_024 keeps 75 op-6 w=16 checks vs powdr's 52: a w=16 check on an expression that finer checks
already imply (`d = 16384·F + h₀` with `F < 4` op-6-checked and `h₀ < 2¹⁴`) is redundant.
`SubsumedCheck` currently drops only `findVarBound`-justified (bare-variable) checks; giving it
the `basisJustified` arm — with a **non-circular base** (justify only against checks this pass
never drops, the `RedundantByteDrop` discipline) — would drop them. Byte-bus gap attributable to
this class ≈ 20–40. Watch the runtime: the coda-side plain `byteJustified` keeps the basis arm
disabled for a reason (measured 63 s/case when fed the whole region per query); reuse the
`buildFormIdx` untrusted-position-index pattern instead.

### 3. Census the op-3 packing parity  ·  *bus-5, sp1*  ·  low-medium value / low effort

Post entry 103, apc packs identity-OR byte obligations pairwise, but powdr still shows more op-3
pair checks (76 vs 44 on apc_024 pre-103; re-census). If apc still leaves unpacked singles (odd
leftovers per invocation, or singles the packer's pair scan doesn't reach across positions),
`byteCheckPackPass`'s pairing scan is the place. Pure layout; variable-neutral.

### 4. The variable tail (~55 over ~20 cases)  ·  *vars, sp1*  ·  case-by-case

- apc_048 (+27): quadratic comparison-gadget cluster (see idea 1's second half).
- apc_064/080/085 (+15/+15/+14): leftover `lower_limb`/`higher_limb`/result-byte families —
  likely partially unlocked by idea 1 (their chains still hold un-telescoped pairs whose death
  would disconnect the byte clusters); re-export and re-diff after idea 1 lands.
- apc_027 (+15): heterogeneous (rnc/addr/c_bits leftovers); census only if the above land.
- The ~30 cases at +1..+5: mostly one `state__clk`-family variable and a stray byte; powdr keeps
  a different-but-equal-count basis on many ties, so audit per case before building anything.

### 5. Constraint-axis gap (219, lowest priority)  ·  *constraints, sp1*  ·  only as tie-break

apc 9.372× vs powdr 9.810× aggregate. Never trade the higher axes for it; only touch if a pass
is otherwise neutral. Not yet attributed; the +27 on apc_027 and +15/16 on apc_030/070 suggest
the same quadratic gadgets from idea 1.

### 6. wasm-eth global range-obligation repack  ·  *bus, wasm*  ·  medium value / medium effort

Still open from the previous file (re-checked: still real). apc trails powdr's bus count only in
range-check *layout* on the big k256 cases (apc_037 +351, apc_012 +511 pre-102; entry 102's basis
arm already recovered −128 on apc_006, so re-measure first): powdr batches several decomposition
limbs into one tuple-range arg and uses byte-*pair* checks where apc emits per-limb checks. A
global rebuild — collect every surviving range obligation, drop solver-implied ones, re-pack
exact-cover — is bus-only and variable-neutral. Caution: 2–7-bit checks must not be packed as
bytes (weakens them).

## Structural follow-ups (from PR #177, 2026-07-22)

Consolidations analyzed but deliberately left out of #177 (worse risk/benefit; pick up when
touching these files anyway):

- **Classifier dispatch for the entailment recognizers**: `denseXorEq?`/`denseBoolEq?`
  (XorEqExtract) and `denseIdentityPairAt` (IdentitySubst) could recognize shapes via
  `denseByteShape?` and keep only their bespoke conclusions (entailed equality / var-equality).
  Est. −20..40 lines. The seqz build-and-compare path shares only the encode layout — leave it.
- **Keyed vs value-only compiled-eval twins**: `denseCompileE_eval`/`denseCompileEs_all`
  (Proofs/Reencode, keyed points) duplicate `denseCompileE_evalV`/`denseCompileEs_allV`
  (Proofs/DomainBatch, value-only) — one lemma over an abstract point/lookup interface with two
  instantiations. Est. −60..80 lines, but the abstraction must be stated carefully.
- **Enumeration-membership triplets**: `mem_assignmentsV` (DomainBatch), 
  `mem_denseAssignmentsV_of_sound` (DomainFold), `mem_denseAssignments` (RootPairUnify) are the
  same induction over three domain-element types. Est. −30.
- **`ofAddConstraints` with coverage**: busUnify's soundness needs `reg`/`hcov`, so it could not
  rewire through `DenseVerifiedPassW.ofAddConstraints`; a coverage-threading variant would let it
  drop its guard/covered/correct blocks. Est. −25.
- **Pass-removal probes**: never trust a small sample — digitFold looked identical on 13 cases
  and regressed 8/100 openvm-eth cases in the CI matrix (entries 124–125). Probe with the list
  entry removed, then let the PR CI matrix decide. Not yet probed: hintCollapse, rootPairUnify,
  flagUnify, bytePack (early instance), disconnected, splitBytePair, identitySubst,
  redundantByteDrop, subsumedRange, subsumedCheck, tupleRange, monicScale, busPairCancelLate
  (oneHotAnnihilate's probe was interrupted).

## Runtime

Rewritten 2026-07-18 from a fresh profiling session (per-pass `profile`, per-cycle timing, gdb
stack sampling, and a size-scaling sweep — all on this container, serial). **Runtime is
end-to-end quadratic in circuit size** (openvm-eth sweep: input 2.3k → 8.8k items costs
1.8 s → 24.6 s, exponent ≈ 1.95), and the largest inputs are exactly where it hurts: openvm
keccak (28.6k constraints / 13.3k interactions / 27.5k vars) takes **252 s**; openvm SHA is ~8×
keccak, so anything superlinear is fatal there.

### Where the time goes (measured)

- keccak per-pass (254 s profile): domainFold 48 s, domainBatch 48 s, reencode 42 s,
  busPairCancel 26 s, intervalForce 21 s, flagFold 16 s, busUnify 12.5 s, rootPairUnify 9.4 s,
  dedup 6.6 s, bytePack 5.5 s, gauss 4.5 s — no single villain; the cost is systemic.
- **Post entries 109–113** (same container, serial): keccak 215 s → ~150 s expected — domainFold
  47 → 14.2 s, busUnify 12.7 → 10.5 s, reencode's ~49 s was **1276-of-1276 degree-rejected
  re-encodings per run** (each paying the freshness scan + full `reencodeOut` + degree walk,
  retried every cycle) — killed by the `degPreReject` necessary-condition pre-gate. Remaining
  big rocks: domainBatch ~50 s (productive enumeration + per-target gathers), flagFold ~20 s
  (samples: `pdKeep` re-verification `findIdx?` deep-eq scans + boxTauto `mentions`/
  `findDomainAlg`), rootPairUnify ~7.6 s, busPairCancel ~7.4 s.
- keccak per-cycle (10 cycles): **cycles 0–2 are ~80 % of the total** (system still 28k→9.7k
  constraints there); the tail cycles 6–9 are ~1 % each. Fixing the big-system per-pass
  quadratics matters more than fixing the fixpoint tail.
- eth apc_100 (5.7k constraints, 24.6 s, 8 cycles): reencode 6.2 s is the top pass (unindexed —
  see idea R3); the last three cycles cost 20 % to remove 24 vars + 5 bus; the final (no-change)
  cycle burns 1.7 s.
- SP1 apc_030 (26.8 s): domainBatch 19 s, **all in one cycle** (the enumeration unlocks late);
  identitySubst 2.7 s.
- gdb samples (keccak, mid-run): `findConsumer` (busUnify), `reencodeLoop`, `foldLoopDirect`
  (domainFold's unindexed path), `collectForBus` — matching the analysis below.

### Where the time goes at SHA scale (2026-07-26, PRs #205–#210 + entries 142–144)

sha256_big (146k constraints / 71k interactions / 168k vars, `profile`, quiet 48-core box):
**989 s (main-of-2026-07-24) → 550 s** across #205 (registry array-copy, encode 80.5 → 0.8 s),
#206 (domainFold Array.modify accepts, 173 → 6.9 s, reencode −86 s from allocator pressure alone),
#208 (pointwiseDupDrop slot-0 index + hoisted singles, flagFold 85 → 15.6 s), #209 (rootPairUnify
per-variable bound indexes, 49.6 → 33.7 s), #210 (busPairCancel segment scans, 107 → 89.5 s), then
**524 → 445 s** with entry 142 (reencode's two per-candidate whole-system scans, 184 → 97 s) and
**445 → 404 s** with entry 143 (busPairCancel's per-query domain scans, 90 → 50 s) and
**404 → 378 s** with entry 144 (two-root map: address-scoped build + factors linearized once).
Remaining per-pass: **reencode 96 s, busUnify 40 s, busPairCancel 40 s, gauss 36 s, domainBatch
20 s (parallel), bytePack 17 s, flagFold 15 s, normalize1 14 s, rootPairUnify 13 s, carryBranch
13 s**; the tail below that is ~60 s over 25 passes. Cycles 0–2 are still ~78 % of the total.
Whole-run perf: ~25 % `lean_dec_ref_cold` + ~17 % allocator + ~8 % `lean_apply_1` — the budget is
still memory traffic, not arithmetic; the `ZMod.commRing` rebuild chain (R9) is ~5 %.
**reencode is again the top pass (96 s)** and its cost is now diffuse: `denseLookupIx` +
`denseAssignments` (the survivor enumeration) ~1.6 % of CPU, `DenseExpr.vars`/`hashedDedup` ~2 %
(per-target `c.vars.eraseDups` gates and the per-accept `denseBuildPruned`), `denseGroupRewrite` +
`denseDegPreReject` ~1.7 %.

**Measurement note:** the profiler's per-pass wall times and `perf`'s CPU shares are not the same
denominator — domainBatch is parallel, so it burns ~25 % of CPU for 4 % of wall. For a serial pass,
`perf` share × total CPU ≈ its wall time; check both before sizing a change.

### Open runtime ideas, priority order

Priority = impact at SHA scale (8× keccak) ÷ effort. The pattern for all index work stays the
entry-90 discipline: *untrusted, re-checked-at-use* candidate indexes (`buildFormIdx`,
`recvIndexAll`, `CoveredIndex`) — a wrong index entry costs time, never soundness, so most of
these need no new proof.

**R1. Kill the true O(N²) loops that dominate the big early cycles**  ·  mostly **done**:
   - ~~`busUnify.findConsumer` per-send forward scans~~ **done (entries 111–112)**: single
     left-to-right sweep per bus with canonical-address-keyed open windows (`sweepGo` —
     all-constant messages are provably invisible to other constant keys, so they cost one map
     probe; `checkPair` re-verifies every emitted candidate, so the sweep is untrusted beyond
     the split equations, which are recovered by drop arithmetic). `TwoRootMap`/`NonzeroWits`
     thunked; the pass body's per-invocation `HashSet.ofList cs.vars` replaced by the
     by-construction variable guarantee (`memEqConstraints_vars`) and the hash-bucket build
     gated on nonempty candidates. Output byte-identical.
   - ~~`busPairCancel`/`redundantByteDrop` byte-justification domain scans~~ **done (entry 143)**:
     `denseFindDomainAlg` is served from a `denseVarBucket` over the single-variable constraints
     (uncapped, order-preserving → identical first match), threaded as a *value* — a lookup closure
     in the thunk payload re-ran the whole index build per query (13× regression, see the entry).
     busPairCancel 90 → 50 s. `flagUnify`, `flagFoldDrops`, `boxRewrite`, `fxSubst` and
     `rootPairUnify` still call `denseFindDomainAlg` on whole lists; same fix applies if they show
     up in a profile (flagFold 15 s and rootPairUnify 13 s are the candidates).
   - `busPairCancel`: ~~`liveArr` materialization per candidate~~ **done (#210)** — see R8.
     The O(B²) *certificate* scans remain (R8 design (b)); in coda mode the `addrHash`
     bucket is O(B) per hot address — add a position cursor. ~~`dropWits` from-0 array scan per
     queried variable~~ **done (entry 105)**: per-variable position index (`buildBoundIdx`),
     re-checked at use.
   - ~~`dedup` constraint-side `List.dedup` O(C²·E)~~ **done (entry 104)**: bucketed
     proven-identical twin (`HashedDedup.hashedDedup`), keccak 6.6 s → noise.
   - ~~`intervalForce` seed filters / `eraseDups` / per-slot pattern re-maps~~ **done (entry
     104)**: keccak 20.7 s → 1.1 s. (`walk`'s O(t²) with `maxTerms = 32` cap remains — bounded,
     low value.)
   - ~~`rootPairUnify` re-linearization per candidate var~~ **done (entry 104)** — factors
     linearized once per constraint. `anyVarBound` memoization across pairs still open (only
     matters if key-matched pairs are common; measure first).
   - ~~`flagFold` triple `eraseDups` in `btPre`~~ **done (entry 104)**. `singleVarCs`/`btCert`
     still recompute per-constraint `eraseDups`, but only on gate-passing constraints (proofs
     unfold them — rework only if they show up in profiles).

**R2. domainBatch setup and enumeration**  ·  **mostly done (entries 104, 128–131)**. Entry 129
skips the Cartesian scan when every active filter is already discharged by
constant evaluation or exact `BusFacts` and extracts constant domains directly. Entry 130 stores
anchor buckets as arrays and summarizes inactive variable-free constraints once, so targets no
longer materialize candidate lists or walk the same inactive tail. Entry 131 advances range domains
in `ZMod` instead of recasting each element and compiles exact range/byte bus facts into scalar,
allocation-free checks, with the opaque evaluator retained as fallback. Remaining:
`constraintRedundant` full-box scans (they pay once to save per-target work), the list-shaped point
and candidate-mask scanner, and hot-variable bucket capping (not byte-identical — the gates read
`esFull`).

**R3. domainFold/reencode: fuse the duplicate whole-system scans; retire the 8192 raw-count
index gate**  ·  mostly **done (entries 105/107/109/145)**:
   - ~~domainFold's 8192 raw-count gate~~ **done (entry 145)**: replaced by a *candidate-group*
     count gate (`domainFoldTargetIndexThreshold := 2`). The direct path costs `groups × system`,
     so the raw constraint count was the wrong quantity to gate on — a small system with many
     groups needs the index, a huge one with a single group does not. Replica ladder: exponent
     **2.07 → 1.10**, `k=4` 29.0 → 0.74 s, total exponent 1.99 → 1.86. **Not byte-identical**, and
     the CI matrix charges a real (tiny) price: SP1 `rsp` constraints 9.372× → 9.365×, two of 100
     cases 175 → 177, variables and bus interactions identical on all six sets. It is a butterfly
     (`reencode` mints `rnc…_49_0` instead of `rnc…_37_0` and its greedy accept order shifts), not a
     systematic loss.
   - **Open — the byte-identical version of the same fix.** The two `domainFold` paths differ in
     *two* ways, so no gate tuning equates them: the direct path also constant-folds variable-free
     subexpressions in group-disjoint items, **and** `denseFoldOutV` moves the covered constraints to
     the end of the list while `denseFoldOutIdxV` rewrites in place. The fix that keeps the current
     output exactly is to leave the direct path's *transform* alone and index only its **no-op gate**:
     `denseSystemHasFoldableWV` is an `any`, so order and multiplicity are irrelevant, and
     `hasFoldableV xs survsV e = true → e.anyVarIn xs = true ∨ e.hasConstFoldableNode = true` (one
     induction — a `varsInF xs` node with no `xs` variable is variable-free, which is exactly
     `hasConstFoldableNode`). Scan the `xs` buckets plus a per-invocation list of positions carrying a
     variable-free node and the gate decides identically; take `es` from `denseCoveredIdx`
     (`denseCoveredIdx_eq_filter_of_complete`), which also retires the per-target `partition`. Rebuild
     both indexes per *accept* — free against the `O(system)` `denseFoldOutV` an accept already pays.
     Result: `O(accepts × system + groups × (bucket + foldable))` with the output preserved exactly.
     ~250–400 lines of proof; strictly better than the gate change above, which it would replace.
   - reencode: the pruned index (`CoveredIndex.buildPruned`, entry 105 — items with more than 8
     distinct variables can never be covered by a ≤8-variable target, so pruning keeps covered
     sets identical) stays, but **behind the 8192 gate again** (entry 107): CI measured
     always-indexed at 1.19× on the dense openvm-eth blocks with no keccak gain — the entry-73a
     direct-path trade-off is real. Do not retire the gate without a same-runner A/B on eth.
     **Re-confirmed on the ladder (entry 145)**: forcing `useIdx` on made reencode *worse*
     (82.4 → 97.5 s at `k=4`), because the accept path then also pays a per-accept
     `denseBuildPruned`. reencode's cost is not in the covered-set scan.
   - ~~domainFold's direct-path double `coveredBy` sweep~~ **done**: one `partition` per target
     feeds both the covered set and the no-op gate (`systemHasFoldableW`).
   - ~~both passes' doubled `c.vars.dedup` setup~~ **done** (`hashedDedup`, computed once).
   - ~~reencode's repeated finite-domain factorization across overlapping targets~~ **done (entry
     136)**: large indexed runs cache one compact root plan per source constraint, retaining source
     positions and clearing the cache after each accepted rewrite. A reuse gate keeps small/direct
     runs on the original path.
   - ~~domainFold's per-accept rebuild~~ **done (entry 109)**: `foldOut` is order-preserving
     (in-place rewrite), `FoldIdx` carries bucket-completeness invariants (stale supersets fine,
     re-checked at use), `refresh` keeps the buckets with no rebuild, and the fold itself is
     computed sparsely over candidate positions (`foldOutIdx`). keccak domainFold 47 s → 10.4 s.
     The **pattern generalizes**: any pass that rewrites items in place (shrinking variable
     sets) can keep one inverted index for its whole run via
     `coveredIdx_eq_filter_of_complete`; reencode is the next candidate (its rewrite *adds* bit
     columns and drops covered constraints, so it needs the remap or a pruned-completeness
     argument).
   - ~~reencode's per-candidate whole-system scans~~ **done (entry 142)**: the fresh-name prefix's
     `List.length` of both item lists and the degree pre-gate's `sharesVarIn` walk are gone
     (threaded counts + thunked posting index, both riding the "nonempty derivations = accept"
     marker). reencode 184 → 97 s. Note PR #194 (open, stale on `docs/`) indexes the same pre-gate
     with a per-invocation root-use plan plus a degree-only traversal twin — the traversal twin is
     the part entry 142 does *not* do (it still builds the rewritten tree to measure its degree).
   - **Still open — reencode's `checkReencode`** re-runs the covered scan after `buildReencode`
     (`Reencode.lean:852/858`); rarely reached (post-gates), so low value now.
   - **Still open — reencode's remaining 97 s**: `denseGroupSurvivorsE` filters the whole
     `denseAssignments` box (≤256 points × covered constraints) for every target, and
     `denseCoveredIdxPos` rebuilds a HashSet + `mergeSort` per target. The build path is
     proof-free (`denseCheckReencode` re-verifies), so a prefix-pruned DFS enumeration with an
     early abort once the survivor count passes `2 ^ (|xs| − 1)` (above which `k < xs.length`
     fails) needs no new proof — only the same survivor *list order* to stay byte-identical.
   - **Still open — reencode is the last exponent ≈ 2.3, and it is the *accept* path.** gdb
     attribution on the ladder's `k=4` rung (35 samples, all inside `denseReencodeStep`), with the
     indexed path forced on so the shape matches sha256's:
     `denseBuildPruned` 20 %, `denseDegPreReject` 20 % (of which the thunked `denseBuildUseIdx`
     rebuild 11 %), `denseReencodeOut` 17 %, `denseCheckReencode` 14 %, the remaining 23 % directly
     in the step (`toArray`, `HashSet.ofList ro.occ`, `withinDegreeB`). That is **~70 % in six
     whole-system passes per accepted re-encoding**, and accepts grow with the circuit, so the pass
     is `O(accepts × system)`.
     **Tried and reverted (no code change):** a `@[csimp]` twin walking the system *once* for all
     bits (`DenseExpr.anyVarIn bits`) instead of once per bit, plus the box cap tested before
     `denseGroupSurvivorsE` enumerates. Proven equal (`denseFreshScan_eq`, from
     `anyVarIn bits e = false ↔ ∀ b ∈ bits, e.mentions b = false`) and byte-identical on 8 fixtures,
     but interleaved best-of-3 on `openvm-eth/apc_005` is **6387/6697/6503 vs 6353/6696/6375 ms** —
     noise. Reason: the |bits| comparisons at the variable nodes stay, only the tree-walk overhead
     goes, and the conjunct is last in the `&&` chain so it is reached about once per accept. A
     sequential A/B looked like a 2–6 % win purely from run-ordering bias; always interleave.
     The version worth building instead decides freshness in `O(|bits|)` from the `varSet` the loop
     already threads (`varSet = Std.HashSet.ofList d.occ` is maintained exactly: accept sets it to
     `ofList ro.occ` with `d := ro`, every reject leaves both alone), which deletes the scan rather
     than speeding it up — but it needs a twin of `denseReencodeStep`/`StepCached`/`Loop`/
     `LoopCached`/`F` carrying that equation, since the equality cannot be stated on
     `denseCheckReencode` alone.
     Three of those six recompute `DenseExpr.vars` over the whole system independently
     (`denseBuildPruned`, `occ`, `denseBuildUseIdx`) — a shared per-item var list would cut ~25 % of
     the pass with a pure `@[csimp]` twin (the values must be *identical*, which a shared fold
     gives; `varSet` is compared as a `Std.HashSet`, so it cannot be replaced by an equivalent
     structure, only computed from shared inputs).
     Getting the **exponent** down needs `denseReencodeOut` to stop rewriting the whole system per
     accept, and that is blocked on one specific fact: `denseGroupRewrite` is *not* the identity on
     items sharing no variable with the group — `varsInF xs` is vacuously true for a variable-free
     subexpression, so the rewrite constant-folds those too. A sparse, index-driven rewrite is equal
     to the spec only under a **fold-normality** precondition (`hasConstFoldableNode = false`
     everywhere), which is checkable in one pass per invocation and, after an accept, on the touched
     items only — with a fall-back to the current loop when the check fails, so the twin stays
     byte-identical. Sketch: `denseUsePositions`-driven `zipIdx` rewrite (`use` is already built and
     forced per accept, so no new index), `L_id : hasConstFoldableNode e = false → anyVarIn xs e =
     false → denseGroupRewrite … e = e`, and the `denseCandidates` completeness already proven for
     `denseCoveredIdx_eq_filter_of_complete` (variable-free items land in `idx.varless`, so they are
     candidates and keep being dropped as covered). That removes 17 %; the other four per-accept
     sweeps additionally need position preservation (tombstoned `alive` mask + bool constraints
     appended to the array), which is the larger half of the project.

**R4. Constant-factor levers that touch every pass**  ·  *medium value, cheap*:
   - **Variable interning-lite, `Implementation/`-only**: parse-time interning is **done (entry
     106)**. The `powdrId?`-first `Hashable Variable` swap was **tried and reverted (entry
     116)**: hash values leak into `Std.HashMap`/`HashSet` iteration orders, and *some* consumer
     lets that order reach the output — sp1 apc_030's export changed (openvm-eth apc_100 was
     identical). Before re-proposing, find and order-normalize the leaking `toList`/`fold`
     (suspects: gauss's `Solved` reverse-dependency buckets, the pdDropSet sweep buckets) — the
     swap itself is otherwise sound and cheap.
   - ~~`identitySubst`~~ **done (entry 106)**: the 2.8 s was an **arity-expansion bug** — a
     `def … : X → Y := let heavy := …; fun y => …` re-evaluates `heavy` per call (the map was
     rebuilt per queried occurrence). 2827 ms → 9 ms on apc_030. **Working rule: bind heavy
     values in the fully-applied pass body and pass them as parameters** (the `FlagFold`
     comment's pattern); when a pass's profile makes no sense relative to its work, suspect this
     first and bisect with a skip-the-body experiment.
   - ~~`normalize` linearize fusion~~ **done (entries 115, 135)**: `normalizePass` uses
     `normalizeFused`, while Gauss keeps every affine source row, stored solution, touched-row
     rewrite, and Markowitz cache in canonical `DenseLinExpr` form. Expression trees survive only
     for genuinely nonlinear subtrees and at the final `substF` boundary, so pivot sweeps no
     longer rebuild affine trees merely to linearize them again.
   - ~~`iterateToFixpoint` sizeKey recomputation~~ **done (entry 115)**: the input's key is
     threaded (`iterateToFixpointFrom`), halving the per-cycle occurrence-list walks (~6 % of
     whole-run samples).
   - ~~gauss descriptor field-operation setup and repeated index reads~~ **done (entries
     118–119)**: proven `@[csimp]` fast twins box the canonical operations once and each pivot
     descriptor now reads its coefficient/count entry once. The broader dirty-sweep and
     allocation-free-pivot experiment in PR #156 was closed after too little whole-run benefit.
   - ~~gauss empty second sweep and variable-list materialization~~ **done (entry 119)**: an
     empty first solution map returns immediately, while productive runs retain both sweeps;
     occurrence and reverse-dependency construction fold expression leaves directly without
     building `DenseExpr.vars` and its append chains.
   - ~~gauss source-order sweeps~~ **done (entry 133)**: a dynamic global Markowitz scheduler
     keeps normalized rows, exact active incidence, all solvable pivots, and a lazy generation-
     checked heap. It updates only rows incident to each chosen pivot and ranks protected status,
     classical fill, stored-solution rewrite cost, and the prior local score lexicographically.
     Heap metadata remains untrusted: every selection is re-solved from the original constraint
     under the current substitution before adoption. Entry 134 keeps the exact source-order path
     below 8192 rows: the scheduler's fixed cost is not justified there, and changing the affine
     basis in nonlinear-connected components can worsen later syntactic cleanup.
   - **Still open — component-aware Gauss scheduling**: source-order and Markowitz eliminate the
     same number of pivots on the affected SP1 shapes, but choose different bases where affine rows
     share variables with nonlinear constraints. Preserve source order only in those connected
     components and use Markowitz in purely affine components; this could safely extend dynamic
     scheduling below the coarse 8192-row gate.

**R5. Framework: track "pass returned input unchanged" and skip the per-pass degree check**  ·
*medium value, one framework change*. Every pass is `guardDegree`-wrapped, and the guard runs
`withinDegreeB` — a full AST walk — on every pass output, ~30×/cycle, ~245×/run
(`FactPass.lean:98`), even though most invocations return `cs` itself (the #146 measurement: ~61 %
of invocations are no-op full scans). Add an `unchanged : Option (out = cs ∧ derivs = [])` field
(default `none`) to `PassResult`; no-op branches supply `some ⟨rfl, rfl⟩`; `guardDegree` returns
`r` directly when set (out = cs is within-degree by the pipeline invariant — provable, not
pointer magic); `andThen` propagates; `iterateToFixpoint` skips both `sizeKey` recomputations
when the whole cycle is unchanged, and carries the previous cycle's `sizeKey` forward instead of
recomputing `cs.sizeKey` (`FactPass.lean:77`, one redundant O(E) HashSet build per cycle today).

**R6. Cross-cycle dirtiness (the real fix for no-op rescans)**  ·  *large refactor; the cheap
slice is now a measured dead end*. **Do not build a cross-cycle negative-memo for domainBatch**:
per-target fingerprints (target vars + domain descriptors + covered es/bis content hashes) were
measured across invocations — keccak repeats only **62 of 16,748** enumerations with unchanged
inputs (0.4 %), apc_030 257 of 1,641 (16 %, and its expensive cycle-5 enumeration is first-time)
— gauss's per-cycle substitutions rewrite the covered sets, so the fingerprints churn. Any
cross-cycle scheme must therefore be *finer* than whole-target skipping (powdr-style dirty
worklists where a substitution dirties only the items mentioning substituted variables — the full
#146 architecture), and its payoff must be re-estimated per pass first: at target granularity the
~61 % invocation-level no-op measurement does **not** translate into reusable work. After entry
129's no-effective-filter skip, domainBatch's remaining enumeration is relational first-time work;
the levers there are effectiveness-side (replace enumeration classes with algebra, cf. the
quadratic-roots effectiveness idea 1) or intra-enumeration.

**R7. Intra-pass parallelism**  ·  partially **done (entries 114, 132)**: domainBatch's independent
enumerations use ordered parallel joins, with entry 132 preflighting every target and replacing
per-target tasks with at most 64 contiguous work-balanced chunks. Still open: domainFold's and
reencode's per-target *gating* work is also independent between accepts, but their loops rewrite
`cs` on accept, so parallelizing needs a speculative gather-then-replay structure — only worth it
if their serial remainder grows relative to the rest. busPairCancel/busUnify are inherently
sequential scans (window state).

**R8. busPairCancel residual quadratics** (formerly part of R1). Design (a) — array-segment
twins of `liveArr`+`shieldScan`/`List.all` (`denseLiveAllSeg`/`denseShieldScanSeg` with `…_eq`
lemmas) — is **done (#210)**: sha256_big busPairCancel 107 → 89.5 s, and entry 143 took the
justification's domain scans out (89.5 → 50 s). The remaining 50 s is the O(live²) certificate work
itself — `denseShieldScanSeg` is ~4 % of whole-run CPU: `shieldOk` still evaluates
`densePreRefuted` over the whole live prefix per candidate send, and `midRefuted` over the
between-region. Design (b) stands: the busUnify entry-111 treatment — `shieldOk` left-folds
to a single per-address-key `pending` bit, maintainable across one sweep — but the pass's
tombstone-and-restart structure (drops invalidate prefix state: removing a consumed receive
un-shields earlier messages) forces a recompute-on-drop scheme, bounded by #drops × O(B).

**R9a (done, entry 144).** `DenseTwoRootMap.addVars` re-linearized a product's factors per
variable; `addVarsFast` + `@[csimp] addVars_eq_fast` hoists them. The `@[csimp]` twin is the
zero-proof-churn way to swap an implementation — prefer it over threading a fast path through the
proofs. Same shape may still apply to `denseDeepEnumDoms`/`denseRootsIn`-style per-variable loops.

**R9. Stop rebuilding `ZMod.commRing` per helper call**  ·  *horizontal, medium value / medium
effort*. Any helper doing `ZMod` arithmetic without a threaded `DenseZModOps` re-materializes the
whole Mathlib `CommRing` structure (plus 3–4 hierarchy projections) **per call** — visible as
`lp_mathlib_ZMod_commRing` + projections at ~3 % (sha) to ~10 % (ecrecover) of whole-run CPU
*before* counting their allocator/dec_ref share; the generated C shows the rebuild at every entry
(e.g. `denseRootsOfTerms`). Hot chain: `denseLinearize`, `DenseLinExpr.norm/scale/coeff/others`,
`denseTwoRootOf?`, `DenseExpr.fold`, `denseRootsIn`, `denseBitCM` — called per constraint per
cycle by the TwoRootMap/AddrCerts/candidate builders of busUnify/busPairCancel/rootPairUnify.
Thread `ops` through `@[csimp]` fast twins (the gauss entries 118–119 pattern; rootPairUnify's
remaining 33 s is mostly this).

**R10. busUnify symbolic-window sweep at SHA scale**  ·  *52 s on sha256_big*. `denseSweepGo`
tests every symbolic-address message against every open window: `constOpen.toList` is rebuilt per
non-all-const message, and each open `symOpen` window pays the full `denseStepTest` certificate
chain per message. The sweep is an untrusted proposal (`denseCheckPair` re-verifies), **but its
consumer/excluded/blocker decisions choose which candidates are proposed**, so any restructuring
must keep decisions bit-identical — memoize `denseStepTest` only under full structural keys, or
index windows by address-expression hash with the existing tests re-run on hits.

**R11. `decide (A ∧ B)` evaluates both sides eagerly**  ·  *latent bignum landmine, cheap fix*.
`Decidable (A ∧ B)` instances are strict in both arguments in compiled code, so
`decide (widthValue.val ≤ 17 ∧ xValue.val < 2 ^ widthValue.val)`
(`DomainBatchRuntime.lean:166`, `.varRange` evaluator) computes `2 ^ widthValue.val` even when
the guard fails — for a symbolic width slot that is a 2^31-bit GMP number per evaluated point.
`OpenVmSemantics.lean:95` already uses the short-circuiting `decide … && decide …` form;
rewrite the evaluator arms the same way (`Bool.decide_and` bridges proofs). Audit other
`decide (… ∧ …)` in per-point code (`denseScaledSlotBound`'s guard is a cheaper instance of the
same pattern).

**R12. Array-index the dense per-variable maps**  ·  *speculative, measure first*. Every
`Std.HashMap`/`HashSet` operation dispatches `BEq`/`Hashable` through boxed closures
(`lean_apply_1/2`, ~8 % whole-run). `VarId.index` is dense and bounded by the registry size, so
the per-variable bucket maps (`DenseCovIndex.buckets`, `denseVarBucket`, `denseTouchedSet`) could
be `Array (List Nat)` / bitsets keyed directly — no hashing, no dispatch. Wide but mechanical;
worth a prototype on one index first.

### Runtime dead ends (measured; do not re-propose without new evidence)

- **Whole-system content-hash gating of passes across cycles**: catches ~0 % — the fixpoint only
  retains cycles that changed something, so some pass always dirties the hash (#146 measurement).
  Only fine-grained dirtiness (R6) reaches the ~61 % no-op invocations.
- **Unsafe pointer-identity freshness checks** (`@[implemented_by]` ptr-eq): rejected — breaks the
  fully-machine-checked, three-axioms-only guarantee (#145 discussion). The safe variant is the
  `unchanged` *proof* field of R5.
- **Eager per-sweep variable→bound witness maps in busPairCancel**: ~30× the work of the
  early-exit query-time scan on eth (entry 90). Query-time scans + per-variable *position*
  indexes are the pattern.
- **Feeding whole regions into per-query justification arms**: 63 s/case for −3 interactions
  (entry 102). Use a position index or nothing.
- CI notes (updated 2026-07-24): the effectiveness-matrix runtime row swung **+51 % → +15 % on
  identical code** for openvm-eth while its own per-pass table showed ≤1.04× — treat the wall row
  as ±50 % noise on the small parallel sets and read the per-pass table instead; the serial
  `Runtime Bench` workflow (dispatch-only, openvm sets only) is the real A/B. This container has
  ±15 % run-to-run variance; keccak numbers above were taken serially, and the per-cycle keccak
  run was inflated ~30 % by a concurrent gdb sampler — compare shapes, not absolutes, and let CI
  arbitrate.

## Measured dead ends (do not re-propose without new evidence)

- **OpenVM keccak below 1734 bus / 2021 vars / 186 constraints**: measured floor (XOR dag clean,
  memory exact-pair floor, range widths minimal). The 1748 → 1734 residual is 14 interactions of
  bus-3 layout parity, repeatedly measured as not worth a pass.
- **eth constant-decomposition folding beyond DigitFold**: constraint-side seeds measured +0 vars
  /+12 bus (Gauss pivot mangling *feeds* the payload-side fold; protecting seeds starves it).
- **Per-check folding of genuinely-all-byte ladders**: mod-p alias is admissible — a per-check
  fold is *incorrect*, not merely unproven (`isCompleteReplacementOf` quantifies over admissible
  assignments).
- **Timestamp-decomp / mem_ptr encodings**: count-neutral representation choices, verified 1:1.
- **Variable count via derived columns / functional dependence**: structurally impossible
  (variables are counted syntactically).
- **`identitySubst` in the cleanup cycle**: still a regression (re-encode explosion); its coda
  placement (now pre-drop/pack, entry 103) is the working point.
- **Feeding `rest` as the basis lookup in the coda's `byteJustified`**: 63 s/case for −3
  interactions (entry 102). Use an index or nothing.

## Working rules (accumulated)

- **Don't trust prior conclusions — re-measure.** Two of this session's three wins contradicted
  the previous file's "residual is X" attributions (the "carry/negative-coefficient" class was
  actually forced equalities the interval argument sees; the "memory telescoping needs
  architectural work" class fell to one justification arm).
- **Prefer generalizing an existing mechanism over a new pass**: entry 101 replaced ScaledZero
  with its generalization; entry 102 is an arm of the existing justification; entry 103 is two
  recognizer arms + a reorder. Each was cheaper to prove than a fresh pass and composes with the
  whole cascade.
- **Per-case diff before/after every candidate** (`opt-export` + canonical compare): aggregate
  effectiveness hides single-case regressions that the lexicographic merge rule forbids.
- **Runtime is a de-facto merge criterion**: build per-invocation indexes once; keep expensive
  arms out of hot per-query paths; put once-suffices passes in the coda.
- **Check open PRs / recent `claude/*` branches for duplicates before implementing.**

## Runtime ideas (2026-07-27 session, entry 148)

- **Per-drop `alive` copies in busPairCancel**: with the region scans now sparse, the heavy-drop
  cycle's residual includes `(alive.setIfInBounds iP false).setIfInBounds jP false` copying the
  71k-entry array per drop (alive is shared by the scan closures). ~12k drops ≈ 1.7 GB of copies.
  A persistent-friendly representation (e.g. a `Std.HashSet Nat` of tombstones consulted alongside
  a stable array, or batching drops per findCancel sweep) could cut most of it.
- **busUnify same-key mid verification**: `denseCheckPair` re-verifies each candidate's whole mid
  window (`mid.all`). The same constant-key argument as entry 148 applies: mid messages with a
  different constant key are refuted by the ConstsNeq arm. Needs the window's positions (the sweep
  recovers mid positionally from the stored suffix), so it wants the sweep to carry position
  ranges plus a `DenseKeyIdx`-style lookup; the sweep's `denseStepTest` per open symbolic window
  is the other half.
- **reencode cycle 0 (42–47 s to remove 128 vars)**: the remaining big certificate costs are the
  per-candidate covered-set scans (`denseCoveredCsOf d xs`, a full pass over d per candidate —
  the cached state's buckets could serve it with a threaded invariant) and the per-accept
  full-system gated rewrite (`denseReencodeOutFast` — the state's `useCs` buckets + `foldCs` cover
  exactly the positions the gate can fire on; needs a positions-driven twin with the state
  invariant threaded, ~200-400 lines).
- **domainBatch cycle 0 (26–28 s for 2.6k vars)**: gathers are bucket-served already; the cost is
  hot-variable buckets × many candidate groups. Maybe gate groups on a cheap upper bound of the
  gather size, or dedupe overlapping groups before gathering.
- **flagFold cycle 0 (24 s, zero effect)**: NOT the domain lookups (bucketing them changed
  nothing). Suspect `denseFuCandidates`' per-interaction `O.vars.eraseDups × splitAt` on large
  first-slot payloads, or the per-matched-pair box evaluation in `denseFuPairData?`. Sample the
  window before building anything.
