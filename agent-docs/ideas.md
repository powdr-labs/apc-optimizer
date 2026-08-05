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
still memory traffic, not arithmetic; the `ZMod.commRing` rebuild chain is gone (R9, entry 156).
**reencode is again the top pass (96 s)** and its cost is now diffuse: `denseLookupIx` +
`denseAssignments` (the survivor enumeration) ~1.6 % of CPU, `DenseExpr.vars`/`hashedDedup` ~2 %
(per-target `c.vars.eraseDups` gates and the per-accept `denseBuildPruned`), `denseGroupRewrite` +
`denseDegPreReject` ~1.7 %.

**Measurement note:** the profiler's per-pass wall times and `perf`'s CPU shares are not the same
denominator — domainBatch is parallel, so it burns ~25 % of CPU for 4 % of wall. For a serial pass,
`perf` share × total CPU ≈ its wall time; check both before sizing a change.

### Where the time goes after entries 160–175 (2026-08-04, whole local corpus)

Fresh `profile` sweep of all **303 local APCs** (OpenVM 293 + SP1 10) on a 20-core box, serial, one
shot each: **50.1 s wall, 43.2 s of it inside passes**. Per family: sha256 23.1 s, wasm-eth 12.5 s,
openvm-eth 8.0 s, SP1 rsp 2.9 s, OpenVM keccak 2.2 s, SP1 keccak 1.1 s — the corpus total is
sha256-weighted, so read it together with the per-case numbers.

**The per-pass profile is now flat and the largest line items are no longer inside any one pass.**
Corpus shares: domainBatch 8.8 %, busPairCancel 7.4 %, gauss 6.5 %, reencode 6.1 %, busUnify 4.9 %,
flagFold 4.8 %, domainFold 4.1 %, normalize1 3.4 %, carryBranch 3.2 %, rootPairUnify 3.0 %,
digitFold 3.0 %, degenRange 2.7 %, intervalForce 2.7 %, tupleRange 2.7 % (entry 175), zeroRegister
2.5 %, normalize2 2.4 %, flagUnify 2.1 %, then 22 passes below 2 %. Top ten = 54 % of wall, the
remaining thirty = 37 %, on sha256 `apc_001`, keccak `apc_001` and wasm-eth `apc_012` alike. Three
passes that were never in the old ranking are now in the top 20 (`tupleRange`, `zeroRegister`,
`flagUnify`), alongside `digitFold`, `degenRange` and `xorEqExtract`.

Against that flatness, two cross-cutting measurements dominate everything per-pass — see R15 and R5:

- **42 % of all pass wall (18.2 s of 43.2 s) is invocations whose output is structurally identical to
  their input**; 62 % of the 42 900 invocations. Net of the degree guard it is still 16.1 s (37 %).
- **The degree guard is 10 % of pass wall** (4.4 s): corpus 50.1 → 45.8 s (**0.914×**) with
  `withinDegreeB` stubbed to `true`, per case 0.907× (sha256 `apc_001`) / 0.924× (wasm-eth `apc_012`)
  / 0.930× (keccak) / 0.939× (openvm-eth `apc_071`).

Whole-run cost classes (sha256 `apc_001`, LBR, leaf-classified): pass logic 33.6 %, refcount 18.3 %,
alloc/free 15.3 %, list ops 10.7 %, lean runtime 9.7 %, hash/std 3.6 %, closure-apply 2.4 %,
field/instance 2.3 %. Top leaves: `lean_dec_ref_cold` 17.8 %, `mi_malloc_small` 7.9 %,
`DenseExpr.degree` **5.4 %** (95 % of its callers are `withinDegreeB`; `guardDegree` is also 21 % of
all `lean_dec_ref_cold` callers), `List.reverseAux` 3.3 % (30 % `appendTR`, 23 %
`DenseConstraintSystem.mapExpr`, 11 % `substF`). `mapExpr` has exactly two callers —
`denseNormalizePass` and `denseConstantFoldPass`, i.e. five pipeline entries and 3.3 s of corpus —
and rebuilds both item lists on every invocation whether or not an expression changed.

**Measurement caveat found in the same session:** `profile`'s reported *total* overstates `run` by
~4.5 %. `varCount`/`sizeKey` frames are 4.81 % of sha256 samples and **95 % of those carry a
profile-harness frame** (the per-cycle size line the profiler prints); the optimizer itself pays only
the fixpoint's own `sizeKey`. The per-pass columns are unaffected (entry 164). Also: a pointer-only
no-op probe reads 20.9 % where structural equality reads 42 %, because `normalize`/`constFold`/
`carryBranch`/`intervalForce`/`busPairCancel` rebuild their lists unconditionally — use structural
equality with a pointer-identity shortcut. (`degenRange` no longer does, entry 179: it returns the
input object when its sweep recognizes nothing.)

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
     busPairCancel 90 → 50 s. ~~`flagFoldDrops`~~ **done (entry 157)**: its box-tautology
     certificate re-derived the domains from the unbucketed single-variable list per candidate —
     9.2 s of a 13.7 s pass on sha256 `apc_001` — while the bucket built in the same function served
     only the prefilter in front of it. ~~`boxRewrite`, `fxSubst`~~ **done (entry 165)**: all of
     `flagFold` now reads one `VarId.index`-keyed table built once per invocation. `flagUnify` still
     calls `denseFindDomainAlg` on whole lists; same fix applies if it shows up in a profile.
     `rootPairUnify` keeps a `denseFindDomainMap` table already, and after entry 170 its domain path
     (the scaled slot bound) is never reached on the measured cases.
   - `busPairCancel`: ~~`liveArr` materialization per candidate~~ **done (#210)** — see R8.
     The O(B²) *certificate* scans remain (R8 design (b)); in coda mode the `addrHash`
     bucket is O(B) per hot address — add a position cursor. ~~`dropWits` from-0 array scan per
     queried variable~~ **done (entry 105)**: per-variable position index (`buildBoundIdx`),
     re-checked at use.
   - ~~`dedup` constraint-side `List.dedup` O(C²·E)~~ **done (entry 104)**: bucketed
     proven-identical twin (`HashedDedup.hashedDedup`), keccak 6.6 s → noise.
   - ~~`intervalForce` seed filters / `eraseDups` / per-slot pattern re-maps~~ **done (entry
     104)**: keccak 20.7 s → 1.1 s. ~~`walk`'s O(t²)~~ **done (entry 172)**, with the rest of the
     pass: the `occ` `HashSet` (vacuous — every seed variable comes from a term of an item of `d`),
     the `bHash` bucket build over every constraint, the duplicated interaction sweep, and the
     per-slot list pipeline are all gone. 0.32–0.34x on the pass; its residual is
     `BusFacts.slotBound` dispatch (see R13(b)).
   - ~~`hintCollapse`'s per-witness full-system `denseOccursOnlyInTarget` scan~~ **done (entry
     173)**, with the rest of the discovery layer: one `VarId`-indexed occurrence-code array
     (bus walk, then constraint walk) replaces the certified scan, the bus-variable `HashSet`, the
     per-constraint `vars.dedup` counter, the unconditional `denseBuild`, the `d.occ` freshness
     scan and the by-value target replacement. 0.11–0.17x on the pass. The certified scan was not
     just expensive but *implied* by the two prefilters already gating it — check for that shape
     elsewhere before indexing a scan.
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
allocation-free checks, with the opaque evaluator retained as fallback. Entry 152 compiles
arity-only lookups (OpenVM `pcLookup`, SP1 `pcLookup`/`instructionFetch`/`pageProt`) to `.always`
via a new `neverViolatesArity` fact, taking the opaque per-point `violatesConstraint` out of the
scan. Remaining: `constraintRedundant` full-box scans (measured 2.5–5.6 % of the pass — they pay
once to save per-target work), the list-shaped point and candidate-mask scanner (inside the 0.8–3.8 %
box-loop phase on the big cases), and hot-variable bucket capping (not byte-identical — the gates
read `esFull`). **The pass's remaining cost is not here — see R13.**

**R3. domainFold/reencode: fuse the duplicate whole-system scans; retire the 8192 raw-count
index gate**  ·  domainFold **done (entry 167)**, reencode open:
   - ~~domainFold's duplicated scans, its two paths, and the per-(target, variable) domain
     re-linearization~~ **done (entry 167)**: the pass is one invocation-wide set of
     `VarId.index`-keyed tables (per-item variable lists + candidate keys from one traversal, position
     buckets restricted to target variables, one `denseRootsIn` per target variable) plus one fused
     bottom-up traversal that carries each node's survivor value *and* its rewrite, so the no-op gate
     and the rewrite are the same walk. The unindexed path and the per-item `anyVarIn` gate are gone;
     effectiveness is identical on all 303 local corpus cases. Pass 0.23–0.36x, sha256 total 0.92x.
     The superseded plan ("index only the direct path's no-op gate to keep the output byte-identical")
     is retired: the two paths are now one, and the measured output is unchanged anyway.
   - ~~`denseRootsOfTerms` built the whole `CommRing` chain per call~~ **done (entry 167)**: the
     dictionary-free `@[csimp]` twin also skips `ZMod.inv`'s extended gcd for a monic coefficient.
     Shared, so flagFold gains too (sha256 1286 → 1095 ms).
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
   - ~~`normalize` linearize fusion~~ **done (entries 115, 135)**, then ~~the walk itself~~ **done
     (entry 171)**: Gauss keeps every affine source row, stored solution, touched-row rewrite and
     Markowitz cache in canonical `DenseLinExpr` form, so expression trees survive only for
     genuinely nonlinear subtrees and at the final `substF` boundary. Entry 171 rebuilt the walk
     itself (0.39–0.56x on both invocations): a two-constructor result with the linear form
     inlined, leaf children handled at the parent, a term accumulator instead of `++`, and a fused
     merge/drop-zero/`toExpr` materializer. Its residual is ~2.2x an identical-copy rebuild of the
     tree, i.e. one `DenseNrm` plus one cons+pair per term above the floor; the sized-but-unpursued
     items are in `normalizeRedesign.md`.
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
   - ~~gauss's per-variable scheduler indexes~~ **done (entry 158)**: `rowDeps`, `pivotRows`,
     `degrees` and `DenseSparseSolved.revDeps` are `VarId.index`-keyed arrays updated with
     `Array.modify`. **0.86x on the pass** (CI serial bench, sha256: 13.1 → 11.3 s; this container
     reads 0.70x repeatably, 4/4 pairs — see the entry), byte-identical, zero proof work. It is a
     **Markowitz-path win**: the openvm-eth corpus, whose gauss invocations are all source-order, is
     a wash (100 cases, 1.000x total, 0.984x gauss, no case worse than 1.047x). See R12 and the
     gauss residual below.
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
**Now the single largest line item of a rebuilt pass** (entry 173): after hintCollapse's rebuild the
guard is ~103 ms of its 178 ms on sha256 `apc_001` — **58 % of the pass**, and 9 of its 10
invocations return the input untouched. Every pass rebuilt to a cheap sweep hits this floor next.
**Sized corpus-wide 2026-08-04**: `withinDegreeB` stubbed to `true` (`@[implemented_by]`) is
**4.4 s of the 43.2 s of pass time (10 %)**, corpus wall 50.1 → 45.8 s (**0.914×**), per case
0.907–0.939×; 2.0 s of it is inside no-op invocations (R15). Per-pass guard share is worst exactly
where a pass has already been rebuilt to a cheap sweep: zeroMultBus **76 %**, oneHotAnnihilate 51 %,
hintCollapse 39 %, bytePack 34 %, xorEqExtract 26 %, degenRange 16 %, carryBranch 14 %, and 3–8 % for
the big passes. `DenseExpr.degree` is 5.4 % of whole-run samples and `guardDegree` is 21 % of all
`lean_dec_ref_cold` callers (`List.all` boxes a closure and a `Bool` per item).
**The guard half landed (entry 181): `guardDegree` now checks in lockstep against the pass input,
with axiom-free `withPtrEq` identity shortcuts** — 0.94–0.96x end-to-end on every representative
and sha256, output-identical. What remains of R5 — the `unchanged` field, the fixpoint `sizeKey`
skip, the guard's `inc_ref`/restore branch — is sub-bar alone; treat it as the substrate of the
R15 cross-cycle skip memo (with R14's state channel) and size the three together. Note the guard's
`dec_ref` attribution was mostly the old-generation free cascade landing in its frame, not
`List.all` boxing — de-boxing alone measured flat (entry 181's DROPPED list).

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

**R8. busPairCancel residual quadratics** (formerly part of R1) · **done (entries 141/143/148/153)**.
Design (a), array-segment twins of `liveArr`+`shieldScan`, landed in #210 (sha256_big 107 → 89.5 s);
entry 143 took the justification's domain scans out (89.5 → 50 s); entry 148's sparse same-key index
cut the region scans to the same-key + symbolic positions (0.54× on the big case). **Entry 153 closes
the O(live²) certificate work itself**: the shield fold is decided by the *topmost* visited live
position `q` with `¬P q ∨ Q q` (`ok = P q`), so a descending early-exit walk over the index arrays
computes the same boolean while touching only the positions above the last provable receive —
28.6 M → 0.86 M positions on sha256 `apc_001`, pass 19.3 → 6.4 s (0.33×), output byte-identical.
Design (b) (a maintained per-address-key `pending` bit with recompute-on-drop) is therefore
**retired**: the early exit gets the same asymptotics with no cross-candidate state, no drop
invalidation, and a value-identical transformation of the existing fold.
   **Entries 167 and 174 rebuilt the pass twice more** (windowed region scans + scoped two-root
   table + in-place tombstones, then the prepared checked-form memo + canonical affine keys + one
   shared prepared address array): sha256 `apc_001` 6.4 s → 1.65 s. What is left is in
   *busPairCancel residual after entry 174* below. The pre-167 list is kept for the shapes it names:
   **What was left in the pass (6.4 s on sha256 `apc_001`, measured post-153)**, in order:
   the surviving certificate evaluations — `denseAddrNonzeroNeqP` is allocation- and
   allocation-bound (`denseIsZeroLin`'s zero test is dictionary-free since entry 156, but
   `denseDiffSumP` still rebuilds the chain per subset, 4 subsets per compared pair on a
   two-slot address — R9b); the per-invocation index builds (`denseRecvIndexAll`, `denseKeyIdxBuild`,
   `denseBuildBoundIdx`/`FormIdx`, 5.4 % of the pre-153 pass); the per-drop `alive` copy (below);
   and `denseInteractionBound`'s per-variable pattern rebuild (R13b).

**R9a (done, entry 144).** `DenseTwoRootMap.addVars` re-linearized a product's factors per
variable; `addVarsFast` + `@[csimp] addVars_eq_fast` hoists them. The `@[csimp]` twin is the
zero-proof-churn way to swap an implementation — prefer it over threading a fast path through the
proofs. Same shape may still apply to `denseDeepEnumDoms`/`denseRootsIn`-style per-variable loops.

**R9 (done, entry 156).** The `ZMod.commRing` rebuild measured **17.7 % of the run** on sha256
`apc_001`, not the ~3–5 % recorded here. Fixed by primitives that case on `p` directly
(`zmodAddP`/`zmodZeroP`/`zmodIsZero`/… in `Encoding.lean`), a `denseZModOps` built from them (which
cheapens all 34 `…With ops` twins at once), and `@[csimp]` twins at the live sites: **0.68–0.90×
per corpus**. Three things worth carrying forward:

- **Reachability before conversion.** 149 of 288 chain-building functions in the IR are already
  `csimp`'d away and unreachable; a C sweep alone cannot tell. `gauss` looked like the biggest
  target and was already ops-threaded.
- **Definitional equality is the limit.** A site whose surrounding `@[csimp]`/`…With_eq` proof is
  `rfl` cannot take a primitive (`zmodZeroP p` is not definitionally `0`). Converting *every*
  remaining live site measured **+0.4 %** for ~25 broken proofs — not worth it.
- **Where a twin already exists, edit only the twin**; the in-place edit costs proof work and buys
  no runtime.

~~**R9e. Recognizer numerals on the entry path.**~~ · **done (entry 180)**, and the residual is
measured. A recognizer that *compares* an expression against a `DenseExpr.const` numeral pays the
`ZMod.commRing` chain at its **entry**, ahead of the branch test that would have rejected the
interaction — invisible in the Lean source, so read the C. Fixed with one `@[csimp]` twin per
recognizer testing literals through `DenseExpr.isConstZero`/`isConstOne` (`Encoding.lean`, the common
ancestor of both halves of the import graph; its two `_eq_decide` bridges are the whole proof
surface). **xorEqExtract 0.61–0.66x, digitFold 0.68–0.74x, subsumedCheck 0.66–0.78x, splitBytePair
0.55–0.74x; corpus wall ~0.983x.**

Measured and dropped — do not re-propose as stated: **`denseSubsumedRangeCheck?`** (flat, 0.993x:
subsumedRange's 417 ms is not in its recognizer) and **`IdentitySubst`** (flat, 0.967–1.085x). The
IdentitySubst result is the informative one: a variant that *also* hoisted the literal-`1`
multiplicity gate ahead of the `facts.byteXorSpec` lookup measured **0.761x**, so there the cost is
the *lookup ordering*, not the numeral — worth ~15 ms of corpus, which does not repay the
`if`-past-`match` commutation proof the hoist needs. Two twin shapes, very different proof costs:
structure-preserving (swap comparisons only) closes as a congruence with one `simp only`; hoisting a
gate out of a nested match must commute `if` past `match` by hand — `grind` fails and `cases` on the
scrutinee will not substitute under the twin's `if`.

Still unconverted, and now known to be **not worth converting on this evidence**: the construction
sites of R9b (below) and the `if (1 : ZMod p) ≠ 0` guard at the top of each pass transform
(`denseSplitBytePairF`, `denseIdentitySubstF`, …) — once per invocation, not per interaction.

~~**R9b. What is left, and why it is expensive.**~~ · **retired as a dead end 2026-08-05: its targets
do not execute.** Its `rootPairUnify` half was already **superseded by entry 170**, which rebuilt the
pass (0.13–0.53×). The remainder — convert the construction sites in `HintCollapse`, `SeqzCollapse`,
`ByteCheckPack`, `BoxRewrite`, at ~25 `…With_eq` bridge restatements off `rfl` — was measured by
attribution on sha256 `apc_001` (131 271 LBR samples, 21.3 s) and **every named construction site is
cold**: `denseSumExpr` 0 frame appearances, `denseCoeffVar` 0, `denseExtractLinear` 0, `densePolyOf`
0, `denseComplExpr` 0, `denseSeqzE*` 2. Not a naming artifact — `denseHintCollapse` itself appears
1021 times, so the pass is sampled and its R9b functions simply never run. Whole-item ceiling
**1.07 % of the run** charging *all* alloc+refcount inside those functions to the dictionary (a large
over-count: they exist to allocate expression trees), **0.18 %** at the direct chain-walk leaves —
either way consistent with R9's own measured `+0.4 %, not worth it`, and R9b's "a few percent" was
never supported. Do not re-open it without a case where one of those symbols is hot.

**What was actually hot there is R9e, not R9b.** The two groups carrying samples carry them in their
*comparison* logic: `denseXorEq?` (4100 appearances; XorEqExtract 342 ms on sha256, 851 ms corpus)
opens with `bi.multiplicity = DenseExpr.const 1` then `op = DenseExpr.const spec.xorOp` /
`o1 = DenseExpr.const 0` / `o1 = DenseExpr.const 255` — the degenRange rule0 pattern exactly, so
tag-matching fixes it with no proof movement. That makes **XorEqExtract the largest R9e target**,
ahead of SubsumedCheck. Its size is genuinely open: ~7 % of the pass at the direct leaves, ~39 % at
the generous ceiling, so size it (`@[implemented_by]`) before promising the ≥ 10 % per-pass clause.
The one true R9b-shaped hot site left is `denseIsByteCompl`'s own `.const (-1)` — one function, 1–2
bridges, not 25. Note also `Affine.trySolve`/`trySolveUnit` and `denseScaledSlotBound` need the ring
for `⁻¹`/`scale` regardless, so converting only their guards would never empty their entries.

**R9d (partly done, entry 170). The bound path is what is left of `rootPairUnify`** (sha256 918 ms:
preparation 274, `denseVarBucket` build 125, ~900 bound queries 122, `substF` 259). A
**candidate-restricted raw bound sweep** — one pass over the interactions recording, *for the
candidate variables only*, the first fact-bounded literal `.var x` payload slot, behind a `Thunk` so
the 8 of 11 sha256 cycles that never query a bound never build it — replaces both the bucket build
and the per-query walks with ~50–60 ms of sweeping in the three cycles that adopt (**~190 ms of
918**). It needs a first-yield sweep-equality lemma against `denseFindVarBound`, the shape of the
existing `denseFindDomainMap_getElem?`. Do **not** widen it to all variables: that is entry 170's
measured dead end (~1 M index entries to serve ~900 queries, worse on every case).

**R9c (done, entry 159).** `denseRpKeyHash` bucketed rootPairUnify's `seen` accumulator on
`(k, A.const, δ, A.terms.length)` while the scan re-verified with the exact whole-key test, so on a
circuit that repeats one instruction shape ~4 000 times the buckets held thousands of key-unequal
entries and ~5 % of the run went into a deep `List.beq` that decided nothing. Hashing the terms'
contents is **0.217x on the pass, 0.925x end-to-end on sha256 `apc_001`**, byte-identical on 14
cases, and needed **no proof work** (the bucket is untrusted metadata; the proofs never unfold the
hash). An audit of all 12 hash-keyed buckets under `OptimizerPasses/` found no second instance — see
the entry for the table and the rule (*a bucket key must hash everything the test behind it
compares, unless that test is semantic rather than syntactic*). Note flagFoldDrops already carries
the per-item signature idea (`DenseExpr.pdVarBloom`, `DensePdEntry.sigs`), which is why the variable
gates measure 0.0–0.7 % of the run and a general per-item summary record is **not** a live lever
(measured, entry 159 session).

~~**R10. busUnify symbolic-window sweep at SHA scale**~~ · **done (busUnify rebuild, 2026-08-01)**.
The pass is 0.10–0.18x on every representative (keccak 1594 → 167 ms, sha256 `apc_001`
7764 → 1243 ms, run 0.81x / 0.91x), output byte-identical. Prepared per-interaction records
(address slot constant value / linear form / two-root reductions, derived once instead of once per
compared pair), a sweep over an array of them proposing `(sendPos, recvPos)` index pairs, and the
affine and two-root arms decided on canonical (merged, zero-dropped, sorted) term keys with an
order-insensitive hash gating the list compare. See the entry in `log.md` for the phase table.
**What is left in the pass** (sha256 `apc_001`, `IO` phase timers, ~650 ms of real work under a
~680 ms floor of output forcing that every pass pays): verifier 226 ms, prep 99, sweep 100, the
address-variable scope + constraint filter 78, the already-present filter 77+13, table 47.

**R10b. The two-root certificate table is over-scoped and cubic — and busPairCancel still pays
it**  ·  *measured 2026-08-01, ~31 % of busPairCancel on wasm-eth `apc_012`*. Two independent
defects in `AddrDiseq.lean`, both fixed inside busUnify's own copy but not in the shared library:
   - **Scope.** `denseAddrSlotVars` collects address-slot variables over *every* interaction at
     *every* declared shape's slots, and `addVars` then inserts an entry for *every* variable of
     every constraint mentioning one of them. Only the variables of address expressions of
     interactions **on a memory bus, at that bus's own address fields** are ever looked up
     (`densePtrReductions` keys on the queried form's own variables, and every certificate arm is
     gated on the compared message being on the candidate's bus). wasm-eth `apc_012` last cycle:
     2 382 variables / 1 034 constraints / 2 100 entries → **61 / 60 / 60**.
   - **Cubic build.** `denseTwoRootOfLins l1 l2 x` recomputes `(l.others x).norm` — itself an
     `O(t²)` like-term merge — once per variable, so a product constraint costs `O(t³)`. It
     succeeds only when the two factors' normal forms agree away from `x` *and* at `x`, so when
     `n1.terms = n2.terms` every variable with a unit coefficient gets an entry directly
     (`A = ⟨l1.const, n1.terms.filter (· ≠ x)⟩`, `δ = l2.const − l1.const`) and the per-variable
     `norm` disappears; otherwise fall back to the current test.
   Together: the build for all invocations drops **586 → 18 ms** on wasm-eth `apc_012` and
   **101 → 18 ms** on keccak. busPairCancel's thunk is not always forced, so what it *actually*
   pays today is less than the full build: forcing it eagerly (output unchanged) costs
   994 → 1269 ms on wasm `apc_012` and 382 → 417 ms on keccak, which puts the paid share at
   **311 ms of 994 (31 %)** and **66 ms of 382 (17 %)**. Expect busPairCancel ≈ 0.71x on wasm
   `apc_012`, ≈ 0.87x on keccak. The port is mechanical (the code exists in `BusUnify.lean`);
   `buildForAddrs_sound` needs re-proving and every `denseAddrTwoRootNeq` call site in
   busPairCancel needs the same-bus gating argument checked.

**R11. `decide (A ∧ B)` evaluates both sides eagerly**  ·  *latent bignum landmine, cheap fix*.
`Decidable (A ∧ B)` instances are strict in both arguments in compiled code, so
`decide (widthValue.val ≤ 17 ∧ xValue.val < 2 ^ widthValue.val)` computes `2 ^ widthValue.val` even
when the guard fails — for a symbolic width slot that is a 2^31-bit GMP number per evaluated point.
`OpenVmSemantics.lean:95` already uses the short-circuiting `decide … && decide …` form; the
rebuilt `domainBatch` evaluator (`DomainBatch.lean`, `dbItemOk`) does too — audit the remaining
arms elsewhere the same way (`Bool.decide_and` bridges proofs). Audit other
`decide (… ∧ …)` in per-point code (`denseScaledSlotBound`'s guard is a cheaper instance of the
same pattern).

**R12. Array-index the dense per-variable maps**  ·  **no longer speculative — first instance landed
(entry 158, gauss 0.86x, byte-identical, zero proof)**. Every `Std.HashMap`/`HashSet` operation
dispatches `BEq`/`Hashable` through boxed closures (`lean_apply_1/2`, ~8 % whole-run), and a
*nested* index (`m.insert x ((m[x]?).getD ∅ |>.insert e)`) additionally **copies the inner set on
every update**, because the map still references the set that was just read out of it. `VarId.index`
is dense and bounded by the registry, so such an index becomes an `Array` keyed by `.index`, updated
with `Array.modify`, which hands the element over uniquely and mutates in place.
   Entry 158 did gauss's four (`rowDeps`, `pivotRows`, `degrees`, `DenseSparseSolved.revDeps`): the
   two mechanisms together were **28 % of that pass**, `hash/std` fell 15.7 → 10.3 % of it and
   `lean_copy_expand_array` 5.7 → 0.5 %. Two lessons carry:
   - **Pre-size or double.** Growing an index one variable at a time with `a ++ replicate k d` is
     quadratic; size it once from a known bound (gauss takes `1 + max index` over the rows it just
     built) or grow by doubling.
   - **Check whether the index is planning data first.** Gauss's scheduler appears in no correctness
     theorem, so the conversion needed *no* proof; only `revDeps`, which the entailment argument
     mentions, cost two restated hypotheses.
   Still open, same shape: `DenseCovIndex.buckets`, `denseVarBucket`, `denseTouchedSet`, and
   `DenseSolved.revDeps` (domainBatch / flagUnify / fxSubst / rootPairUnify). Also `occ`
   (`Std.HashMap VarId Nat`, threaded through four `csimp`'d descriptor twins — more edits, ~0.4 s).

**R13. domainBatch is per-target *setup*-bound, not enumeration-bound** (measured 2026-07-28, LBR
profiles over five OpenVM cases + SP1 keccak; entry 152). **Largely superseded by entry 162**, which
rebuilt the engine: the per-target compile is gone (items compile once per invocation), the coset is
streamed rather than materialized (retires (c)), the domain table is array-indexed (retires the
`T.doms` half of (e)), and the fan-out — with `DenseForcedScanV.work` — is deleted. (b) is still
open and is cross-pass; (d) is now a measured dead end. **The table below is CPU; for the wall,
see entry 155's `IO` phase timers** — the pass is 70 % serial and its largest single item, the
variable-free bus tail in the gathers, does not appear here at all (it is spread across the
`denseCompileCBiPredsV` and gather rows). Phase shares of in-pass samples:

| phase | sha256 apc_001 | keccak | SP1 keccak | eth apc_071 | wasm apc_005 |
|---|---:|---:|---:|---:|---:|
| per-target bus classification (`denseCompileCBiPredsV`) | **56.1** | **40.5** | 34.4 | 2.3 | 0.3 |
| opaque `.fallback` per point (`violatesConstraint`) | 14.0 | 18.0 | 17.9 | 1.7 | **63.2** |
| bus-sourced table build (`denseInteractionBound`) | 15.1 | 19.5 | 16.4 | 11.7 | 7.9 |
| byte-operand coset build (`denseByteOperandDomain`) | ~0 | 0.4 | **21.3** | ~0 | ~0 |
| box-loop machinery (`rangeFoldFrom`, mask) | 3.8 | 3.0 | 1.3 | **20.8** | 2.2 |
| gathers + preflight | 6.2 | 1.9 | 0.6 | 1.1 | 0.2 |

Pass-only cost classes on sha256: 32.5 % closure-apply + 25 % refcount — `BusFacts` closure calls and
the allocation traffic of their results. The `.fallback` row is **done (entry 152)**. Open, in order:

   - ~~**(a) Hoist the target-independent bus classification.**~~ **retired as a wall lever
     (entry 155)**. The 56–70 % is CPU *inside the fan-out*, which is 18 % of the pass's wall — and
     the hoist was built once and measured **1.01–1.04×**, because it drains parallel slack and
     moves the residue into the serial prologue. Entry 155 then deleted 8.93 M of the 9.07 M
     per-target classifications on sha256 by other means (the variable-free tail was 3 446 of the
     3 446 interactions each scan job compiled), so what is left to hoist is ~1 % of the pass. Keep
     it only as a CPU/CI-throughput item, and **time the phases before believing any share here**.
   - **(b) One constant pattern per interaction.** `denseInteractionBound` rebuilds
     `bi.payload.map DenseExpr.constValue?` per *queried variable*, and `denseAddBusVars` /
     `denseBiInformative` compute the same bound twice per variable. `denseInteractionBoundPat`
     (`BusPairCancelWits.lean:26`) is the hoisted twin already. The same specialized map is 6 % of the
     whole sha256 run, called from `denseFindVarBound` (intervalForce, 36.6 % of its calls),
     `denseAddVars`, `denseBoolCheck?`, `denseFormBoundAt`, `denseInteractionSeeds` — so the general
     fix is a per-invocation prepared-interaction record (pattern + constant multiplicity) shared
     across passes, in the `DenseAddrPre` mould. Heed entry 148: prepare only what a profile shows
     rebuilt.
   - **(c) Fuse or lazify the byte-operand coset** — 21.3 % of the pass on SP1 keccak (entry 151's own
     residual, now measured; the only live hit of the "dictionary rebuilt inside a loop" C sweep).
     `((List.range bound).map cast).map (fun z => (z - b) * a⁻¹)` is two passes plus a 256-element
     intermediate per affine byte operand; best form is a `FiniteDomain` arm carrying `(bound, a, b)`
     so `foldElts` advances in the field and the coset is never materialized.
   - **(d) Prefix-pruned / component-split enumeration**, the only lever left on the big-box OpenVM
     cases (`apc_071`: 74.7 % of in-pass samples under `rangeFoldFrom`). Test each compiled item as
     soon as its last variable is fixed (failing prefixes prune the suffix box), and split the
     gathered items into connected components over `xs` so `∏ |domᵢ|` becomes `Σ` per component (the
     unsat case must still force every key to 0). Both keep the survivor set, so the final mask is
     unchanged — but keep the `maxEnumWork`/`boxSize` gates on the *full* product or effectiveness
     moves. ~250–400 lines; **measure first** with a box-shape/point counter (entry 151 built one):
     if the wide boxes are single-variable, neither pays.
   - ~~**Per-target walk of the variable-free bus tail**~~ **done (entry 155)**: `denseGatherBusesV`
     folded `bisIdx.varless` into every target (3 446 interactions × 66 062 targets = 228 M gather
     steps on sha256 cycle 0, plus 8.93 M compiles and 26.8 M per-point evaluations of a
     point-independent value). A per-invocation `DenseBusVarlessSummary` seeds the gather instead;
     domainBatch **0.495×** on sha256 `apc_001`, 0.83–0.94× on every other representative, output
     byte-identical. The constraint side's `activeVarless` is ~2 items here and was left alone.
   - **(e) Cheap micros.** `BusMap` is an assoc-list lookup closure (`toBusMap`) queried per point and
     per fact call — 1–2 % of the run, and substituting an array-backed lookup at the `Main.lean` /
     `Ffi.lean` boundary needs **no proof** (every theorem is ∀ busMap). `DenseForcedScanV.work` (the
     parallel chunk budget) models `boxSize × items` only, but per-target cost has a large
     boxSize-independent term — adding it rebalances chunks with zero proof (order preserved).
     Preflight's `T.doms xs` is 6.8 % on sha256, all `Std.HashMap VarId` probes: the R12 array-indexed
     prototype belongs here first.

### disconnected residual after entry 166 (the union-find)  ·  *runtime, sha256*

The pass is 479 ms of sha256 `apc_001` and 37 ms of keccak. ~60 % of what is left is the union-find
build — one path-halving find per variable occurrence, which is the floor for computing connectivity
from scratch. Two things were looked at and left:

- **An allocation-free `dcFind`.** It returns `Array Nat × Nat`, so it allocates one tuple per
  variable occurrence. Splitting it into a pure `dcRoot` plus a path-rewriting `dcLink` trades that
  for four short array walks instead of two — a wash at these path lengths (1–2 after compression),
  and it makes the link-to-min invariant load-bearing rather than merely useful.
- **Sharing the zero-evaluations.** Removed items are evaluated twice (once to decide whether their
  component is poisoned, once by the re-check). Threading a cache into the guarded drop is exactly
  the argument the re-check exists *not* to trust, and the evaluation is dictionary-free now.

Reusing the partition across cleanup cycles (the pass runs 6–11 times per case) needs incrementality
the stateless pass framework does not have.

### gauss residual after entries 160–161 (the sparse engine)  ·  *runtime, sha256*

Entry 160 replaced the pass with a watch-driven sparse engine and entry 161 removed a pointer-sharing
copy from its scheduler: **gauss 8.8 → 2.5 s on sha256 `apc_001` (0.29x)**, −3 vars / −931 bus there,
and `Gauss.lean` 958 → 200 lines. Items 1–5 of the old residual list are all gone with it
(`fromExpr`'s double walk, the per-row `HashMap`, the index delta updates, the rekey fan-out, and the
eager back-substitution's exponent). What is left, LBR shares of the *new* pass on sha256:

- **the constraint walk 28.0 %** — one fail-fast pass over every constraint tree; irreducible unless
  the prologue is fused into it.
- **output `substF` 28.0 %** — the remaining lever is the **array-backed lookup** (domainBatch's
  `dbSubstFn`, entry 169: 365 → 318 ms there). The unchanged-node-preserving twin is a **measured
  dead end** — see the dead-ends list. **Cross-cutting**: domainBatch, flagUnify, fxSubst and
  rootPairUnify all call `substF`.
- **`occ`/`prot` prologue 21.8 %** — two array passes over the whole system; fuse into the build walk.
- develop/merge 6.8 %, adopt 4.9 %, scheduler 3.8 %, pick/solve 1.7 %. The elimination algebra is
  ~13 % of the pass; the rest is three whole-system traversals.
- **An array-backed row type is worth only 2 525 → 2 375 ms on sha256** (~6 %, measured with a
  `sorry`-ed prototype, identical output on four representatives) — *not* the 0.42x → 0.27x that entry
  160 recorded, which was this scheduler copy misattributed to the row representation. Each array
  primitive would need its own `toList`-correspondence proof, so rows stay `DenseLinExpr`. Below bar.
- **Reproducing Markowitz's exact key** above the gate would remove the one per-case effectiveness
  loss (wasm-eth `apc_006`, +1 bus) at the cost of sha256's −931 bus; it needs the per-variable
  active-degree index back. The scheduler is 3.8 % of the pass, so it is affordable — but measure the
  bus trade before doing it.

**R14. The per-invocation index lifecycle is the dominant cost of the index-heavy passes**  ·
*measured 2026-08-02, re-measured 2026-08-04 (entry 174); cross-pass, framework-level effort*.
On busPairCancel after **two** rebuilds the index builds are ~800 ms of its 1 647 ms on sha256
`apc_001` — seven of them (receive index, per-bus key index, one prepared address array,
bound-witness index, form-witness index, candidate-constraint index, single-variable domain buckets)
on **each of 11 invocations**, while the last five invocations produce **nine drops between them**.
Entry 174's counters make the waste concrete: `DenseVarCsIdx.lookup` is called 2 498 times in sha256
cycle 1, **0 times in cycles 8–10 and the coda, and once in the whole keccak run** — and the index is
built every time. (The obvious per-index fix, deferring the force to the first query, is a **measured
wash**: see the dead ends.)

Every index-heavy pass has the same shape — the indexes are a pure function of the system, the
system barely changes across the terminal cycles, and the pass framework's type
(`DenseVerifiedPassW`, morally `cs → cs`) gives a pass no way to carry anything from one invocation
to the next. The fix is a **state channel**: let a pass return an opaque per-pass cache alongside
its output, keyed by a cheap system fingerprint, and hand it back on the next invocation. Notes:

- It is *not* R6. R6 is about skipping recomputed **work** (per-target memoization, dirty
  worklists) and was measured to be a poor fit at target granularity. R14 is about not rebuilding
  **derived read-only structures** whose inputs are unchanged — a strictly simpler contract.
- Soundness is cheap if the cache is *untrusted*: every index in busPairCancel is already re-checked
  at use, so a stale entry costs time, never soundness. The trusted ones (`domIdx`, `cands`) carry
  a `∀ c ∈ lookup v, c ∈ cs.algebraicConstraints` obligation, which a fingerprint on
  `cs.algebraicConstraints` does not discharge — those either stay per-invocation or need the
  membership proof carried in the cache.
- Sizing before building: on sha256 `apc_001` busPairCancel would save on the order of 0.7 s of its
  1.65 s; the same lever exists in reencode, domainBatch, gauss and flagFold, whose per-invocation
  index builds were never separately attributed.
- The cheap slice that is already **done** and should be done first everywhere else: decide
  *eagerness* per invocation instead of caching across them (`denseThunkIf` + a cheap
  "will any candidate exist?" predicate, 0.84–0.92x on busPairCancel). See also the `Thunk` note
  below.

**`Thunk.get` marks its value multi-threaded — always** (verified in the 4.32.2 runtime
disassembly: `lean_thunk_get_core` calls `lean_apply_1` then `lean_mark_mt` unconditionally). So
forcing a thunk walks the whole freshly-built value graph and permanently flips every object in it
to atomic refcounting — `lean_dec_ref_cold` is 18–20 % of the *whole run's* samples, in `profile`
and in `run` alike. Consequences, all measured on busPairCancel:
   - a `Thunk` holding a large value that will certainly be forced is **slower** than building it
     eagerly (prepared records: 0.91x by switching to `Thunk.pure`);
   - but unconditional eagerness is worse still when some invocations never force it
     (3672 → 3966 ms);
   - so the decision belongs at the call site, per invocation (`denseThunkIf`, above). `Thunk.pure`
     and `Thunk.mk` have the same `.get`, so the choice is invisible to every proof.

**R15. Do not run a pass that cannot fire — 42 % of pass wall, 37 % net of the guard**  ·
*measured 2026-08-04, whole corpus; cheapest class of runtime work in the repo*. Probe: a structural
output-vs-input equality (pointer-identity shortcut) around every invocation in
`denseRunCycleTimed`, accumulating `(invocations, no-op invocations, ms, no-op ms)` per pass.
**18.2 s of the 43.2 s of corpus pass time, and 26 647 of 42 900 invocations, produce nothing** —
sha256 `apc_001` 45 %, SP1 keccak 46 %, wasm-eth `apc_012` 40 %, keccak 39 %. The 62 % invocation
share reproduces #146's; the *wall* share is the new number, and it is larger than any per-pass
residual. Net of R5 it is 16.1 s, so the two levers are essentially independent.

This is **not** R6: R6 memoized recomputed work at target granularity and measured a poor fit. This
is about not doing the work at all, and the framework already permits it — **a pass that declines to
run needs no soundness argument** (returning the input is a legal result, exactly what
`guardDegree`'s reject branch builds). A too-eager gate is an *effectiveness* regression only; a gate
that is a sound necessary condition changes nothing. Per-pass no-op ms, net of the guard: reencode
1479, domainBatch 1382, flagFold 1309, digitFold 1256, domainFold 1128, zeroRegister 1101, degenRange
1057, tupleRange 951 (fixed, entry 175), busUnify 967, flagUnify 895, carryBranch 683, rootPairUnify
589, busPairCancel 606, xorEqExtract 497, intervalForce 465, subsumedRange 414. Four mechanisms, in
increasing effort:

- **(a) Eager whole-system prologues most invocations never use** — sized by stubbing the prologue to
  `∅` via `@[implemented_by]` (upper bound; output wrong). ~~`digitFold` **1480 → 468 ms** (68 % of the
  pass)~~ **done (entry 176)**: 0.398x on the pass, every family improving, by planning the lookups in
  one recognize-and-linearize walk and bounding only the keys that plan can query. Two lessons carry —
  **fuse the planning walk with the work it plans** (keeping the pass's own walk alongside a separate
  candidate walk measured 1.08–1.13x on SP1, where dense byte-pair checks made the duplicated
  recognition cost more than the restriction saved), and **sweep the whole corpus per pass before
  believing a representative set** (the OpenVM representatives all read as clean wins). Its residual is
  in *digitFold residual after entry 176* below. ~~`flagUnify` **1073 → 456 ms** (58 %)~~ **done
  (entry 177)**, 0.546x on the pass: the scan runs first and the bucket is built only when it recorded a
  twin. **An earlier version of this item said a `Thunk` was the fix here; that was wrong.**
  `denseVarBucket` stores the *items themselves* (`VarBucket.lean:23`), so a bucket over
  `d.algebraicConstraints` aliases every expression tree in the system, and forcing a `Thunk.mk` over it
  `lean_mark_mt`s that whole graph — after which `lean_is_exclusive` is `false` for those objects forever
  and reset/reuse is dead for the rest of the run. Split the phases instead; its residual is in
  *flagUnify residual after entry 177* below. Audit every pass for this shape: an index built at the top
  of the body, consumed inside a certificate a prefilter rarely reaches — and check what the index
  *holds* before reaching for laziness.
- **(b) A quadratic rescan inside a no-op pass** — `tupleRange`, **done (entry 175)**, 0.08x on the
  pass. Worth re-checking for the same shape elsewhere: a per-candidate scan of the whole remainder
  whose failure the outer loop cannot learn from.
- **(c) Per-pass necessary-condition gates**, cheaper than the pass's own discovery. The ≥ 75 %-no-op
  passes are ~~`degenRange` (96 %, 1057)~~ **done (entry 179)**, 0.278x on the pass,
  ~~`zeroRegister` (96 %, 1101)~~ **done (entry 178)**,
  0.186x on the pass, `flagUnify` (95 %, 895), `digitFold` (91 %, 1256), `xorEqExtract` (77 %, 497),
  `subsumedRange` (100 %, 414), `zeroMultBus` (72 %), `oneHotAnnihilate` (67 %) — **≈ 5.3 s of corpus
  pass time**. Entry 179 is the case where the gate and the pass turned out to be the same code: once
  the sweep is one allocation-free tag-check pass that returns its input on a miss, no cheaper
  necessary condition beats it. A shared *per-cycle* digest is the wrong first step: the system changes between passes
  within a cycle, so a cycle-start digest is stale from the second pass on. Per-pass gates first, over
  the prepared interaction array of R13(b), which is what makes them cheap.
  **Two findings from entry 178 that generalize across this whole list.** (i) *Audit what a filter
  conjunct is tested against, not how it reads.* `zeroRegister`'s cheapest-looking check,
  `c.vars.all (· ∈ d.occ)`, was 55 % of the pass, because `d.occ` is whole-system — and the conjunct was
  *provably always true*, since the candidates come from interaction payloads. Grep every pass for
  `d.occ` at the top of a body. (ii) *`BusFacts` closures depend only on the bus id, and each call
  allocates a `ZMod` dictionary* — memoizing `facts.zeroCell` over the ≤ ~6 distinct bus ids, with the
  pinned constants pre-wrapped as `DenseExpr.const`, removed another 23 %. Soundness of such a memo
  ("every entry agrees with `facts`") is enough to make the first match usable, so no `Nodup` obligation
  is needed; completeness is only needed to justify *skipping*. This is R13(b) done per-pass, and
  `slotBoundImpl` (16.4 % of the dictionary chain) is the same shape one step larger.
- **(d) The discarded final cycle.** `denseIterateToFixpoint` returns the *pre-cycle* state when
  `sizeKey` does not decrease, so the whole last cycle is computed and thrown away: sha256 `apc_001`
  **646 ms (2.7 % of wall)**, wasm-eth `apc_012` 101 ms (3.9 %), keccak 36 ms. sha256's last two
  cycles cost 1.30 s and between them remove 1 variable, 3 interactions and 1 constraint. Nothing can
  know a cycle is fruitless without running it — this is not a separate lever, it is the argument for
  (a)–(c), since every pass in that cycle is a no-op invocation by construction.

### digitFold residual after entry 176 (the planned bounds map)  ·  *runtime*

570–591 ms corpus-wide, split with two more `@[implemented_by]` stubs: **linearize + ladder solve
~282 ms**, **the restricted bounds sweep 115** (`denseBuildWith → ∅`: 591 → 476, concentrated in
openvm-eth 54, keccak 19, SP1 rsp 19 — already ~10 ms each on sha256 and wasm-eth), **the degree guard
~108** (R5, now 19 % of this pass), **the bare interaction walk ~65** (recognizer → `none`: 570 → 173,
minus the guard). So the sweep — the obvious next target — is only 19 % of what is left, and the whole
addressable remainder is ~0.8 % of corpus wall: **deliberately stopped as sub-bar**. If a corpus ever
makes it matter: `denseTryLadder` sorts `l.terms` once per sign per form, and `denseAddVars` still
resolves `denseVarSlot` per kept variable for interactions whose multiplicity is non-constant, where
every bound is statically `none`. The lesson worth keeping is the method — stub the two halves
separately before designing, because the named half was not the expensive one.

### flagUnify residual after entry 177 (the scanned-then-built bucket)  ·  *runtime*

576 ms corpus-wide against a 456 ms `∅`-stub bound, and the whole gap is **sha256**. gdb hit counts on
`denseFuAdopt`: wasm-eth `apc_012` finds a twin in **0 of 9** invocations, keccak **0 of 10** — those
reach the bound, and what is left there is the scan itself — while sha256 finds matches in **6 of 11**,
**701 of them, every one failing the certificate**, so it still builds the bucket six times (0.587x on
that case, which is 571 of the 1054 ms baseline). Two levers, both unsized: a cheaper pre-filter before
the bucket is needed (701 matches producing 0 adoptions means `denseFuPairData?`'s
multiplicity/`slotBound`/`splitAt`/no-wrap prefix rejects *late*), or a bucket restricted to the joint
offset variables the certificate actually queries, which makes the build proportional to the match
rather than to the system — the entry-176 shape one level finer.

### zeroRegister residual after entry 178 (the prepared bus table)  ·  *runtime*

248 ms corpus-wide, and **71 % of what is left is not the pass**: stubbing the new body to `[]` still
reads 78 ms of sha256 `apc_001`'s 114, i.e. the `ofAddConstraints` record plus the degree guard (R5). The
pass's own two halves are 12 ms of `denseBusIds` + table build and 20 ms of the emit sweep, both linear in
the interaction count with a small constant. Fusing them into a single sweep (threading the bus-id memo
through the accumulator) is the only remaining idea and is worth ~11 ms of a 22 s run against a
threaded-state invariant in the proof — **deliberately left as sub-bar**. Two output-changing options
were also declined as effectiveness questions, not runtime ones: the emit filter cannot see earlier
survivors, so two interactions pinning the same expression emit the constraint twice; and the
`normalize.fold.isConstZero` test measured at ~0 ms, so a `const`/`var` fast path buys nothing.

### tupleRange residual after entry 175 (the single-pass scan)  ·  *runtime*

102 ms corpus-wide, 61 of it on the six cases where the pass *fires*. `denseDrainTuplePacks` restarts
`denseTryTupleBuses` at position 0 after every pack and recomputes `maxId` plus
`denseTupleBusCandidates` each step, so a firing drain is `O(packs × B)` (wasm-eth `apc_006` 24 ms,
`apc_012` 17). A position cursor is sound: `pre` holds no candidate of either recognizer and the
emitted tuple check is on neither's bus, so the next search may resume just after it. Hoisting the
candidate-bus list needs care — it is a pure function of `maxId`, which *shrinks* as interactions are
dropped, so hoisting from the initial list makes it a superset and could pack a pair the current code
never tries. `denseMatchByteSingle` also runs `denseByteShape?` per position with no `@[csimp]`
runtime twin (16 dictionary builds in the C, the highest count in the sweep), where its
`denseMatchRangeCheck` counterpart has one; that is what the surviving single pass costs.

**Effectiveness note, unmeasured:** slot 0 of a tuple check needs `x < 256`, and the pass accepts
only an XOR-bus byte *self-check* there (`denseByteShape?`, `.selfCheck`). A plain variable-range
check `[x, 8]` proves the same thing and is not considered, so two range checks whose widths match a
declared tuple bus's `(s1, s2)` — e.g. 8 and 11 on OpenVM bus 7 (`tupleRangeChecker 256 2048`) —
never pack. That needs no audited change and reuses `tupleRangeBus_sound`; how often such a pair
co-occurs is unknown. Note the arity ceiling is two and is *audited*: `OpenVmBusType.tupleRangeChecker`
carries exactly two sizes, the semantics send any other payload length to `False`, and the parser
rejects a `TupleRangeChecker` with any other arity — so packing three checks into one interaction is a
bus-vocabulary change, not a pass change.

### busPairCancel residual after entry 174 (the checked-form memo + canonical keys)  ·  *runtime*

The pass is 1 647 ms of sha256 `apc_001`, 140 ms of keccak, 238 ms of wasm-eth `apc_012`. Phase
timers put the sha256 remainder at: **index setup ~800 ms**, byte justification ~430, region tests
~230, `guardDegree` 85. Ranked, with what each needs:

- **R12 for `cands` and `domIdx`** — 294 ms of the setup in `Std.HashMap VarId` probes and inserts;
  `VarId.index`-keyed arrays should halve it. Both carry a `∀ c ∈ lookup v, c ∈ constraints`
  obligation, so each needs its builder's soundness restated over arrays.
- **The bound side of the justification, memoized like the form side** (entry 174 change 1).
  `bnd v = denseFindVarBound bs facts (wits v) v` is recomputed at every DFS node for every term, and
  each call re-runs `denseInteractionBound`'s `payload.map constValue?` plus a `slotBound`. A
  per-position `(multiplicity constant, constant pattern)` record is the shared R13(b) item.
- **An allocation-free basis channel.** `denseDropFormBasis` allocates a `flatMap` list per node; a
  higher-order channel (`VarId → ((DenseLinExpr × Nat) → Bool) → Bool`) removes it at the cost of an
  existential spec. Worth ~70 ms of the 430.
- **`bidx` is 200 ms of setup** and its per-(interaction, payload variable) `facts.slotBound` call is
  ~0.5 µs, most of it dispatch — R13(b) again, and (e)'s array-backed `busMap` lookup.
- The region tests' residual after canonical keys is the `denseShieldEarly` walk itself plus the
  constant-slot compares; there is no index left to sharpen without a *per-slot affine* key index
  (which would let wasm-eth's symbolic-address-key candidates use sparse buckets instead of `allA`).

### domainBatch: a staged evaluator for the box scan  ·  *runtime*  ·  medium value

After entry 169 the box scans are still ~26 % of the pass (594 of 2 285 ms on sha256), and the
shape that dominates them is a two-key `256 × 256` box whose single item mentions both keys and is
therefore tested at the innermost depth (`openvm-eth/apc_071`, 85 % scan, improved least; sha256
cycles 9–10, 6.7 M points each and zero forced). Split each item's expression at its **cut
points** — the maximal subtrees whose variables are all bound at an outer depth — and evaluate
those once per outer assignment into a memo array, so the inner loop only re-runs what depends on
the innermost key. Estimated −150 to −200 ms on sha256 and −25 % on `apc_071`. Needs a parallel
item type over a staged tree plus its evaluation-equality proof, which is why entry 169 stopped at
level-attachment (testing each item at the depth of its innermost key) and did not stage the
expressions.

A sharper variant on the same shape: an item that is **affine in the innermost key** determines it
— evaluate at two points to recover `a` and `b`, then `y = -b/a` and test only that one point
instead of 256 (~30× on those scans). It needs a per-item degree analysis and a "the skipped points
are non-survivors" argument (`a·y + b = 0` has at most one root when `a ≠ 0`).

### Runtime dead ends (measured; do not re-propose without new evidence)

- **A shrink-first pre-cycle** (entry 181: a `gauss → normalize → constFold → dedup →
  trivialConstr` fixpoint between prelude and cleanup, so the heavy passes see a smaller system):
  effectiveness-identical, but sha256 is a wash — the heavy passes get 20–30 % cheaper and the
  pre-stage consumes exactly what they save — and wasm-eth `apc_012` regresses **2.0x**, its
  main-cycle gauss exploding 215 ms → 2.7 s on the pre-shrunk system (basis/shape sensitivity, the
  entry-134 hazard). First-time shrink work costs the same wherever it runs; any revival needs a
  pre-stage strictly cheaper than the passes themselves (a fused-sweep shape) with gauss kept out.
- **De-boxing the guard loop without lockstep** (entry 181: monomorphic `all` loops + a capped
  allocation-free degree walk, proven csimp, verified live in the C): **flat** — the guard's cost
  is the tree walk's memory latency, not closures/`lean_apply_1`/Bool boxing. A variant returning
  `Option Nat` per node was 4–7 % *slower* everywhere: never introduce a per-node ctor return on a
  hot walk.
- **Capacity slack for reencode's `pushBool` seeds** (entry 181): the first push onto a
  `toArray`-seeded array copies it whole (24 % of `Array.push` samples), but that is ~11
  pointer-word memcpys per run — **flat**. `copy_expand` is ~0.7 % of the run; its other sites are
  amortized doubling on small buckets.

- **Deferring a per-invocation index's force to its first query** (entry 174, busPairCancel's
  `cands`): the counters say it is queried 2 498 times in sha256 cycle 1, 0 times in cycles 8–10 and
  the coda, and **once in the whole keccak run**, so its 198 ms of build looks pure waste. Passing
  `fun x => candsT.get.lookup x` instead of `candsT.get.lookup` (which forces the thunk where the
  *closure* is built) with `Thunk.mk` moves all 198 ms out of setup and into the first query — and
  the pass total is unchanged, 2 224 → 2 224 ms. `Thunk.get`'s `lean_mark_mt` walk over the index on
  the seven invocations that do query it costs what the four that do not save. The `Thunk` note below
  predicts this; the lesson is that it applies to *conditional* forcing too, not just to eagerness.
- **Merging busPairCancel's two byte-justification sweeps** (entry 174): `denseCheckCancel`'s last
  conjunct (`denseRecvSlotsJustified` = `slots.all justified`) and the `denseUnjustifiedSlots`
  (`slots.filter (¬ justified)`) on the next line are the same per-slot predicate at the same
  `wits`/`fbasis`, and the phase timers had `chk` ≈ `unjust` in **every** invocation — so splitting
  `denseCheckCancel` at that conjunct and reading the verdict off `unjust.isEmpty` was worth ~570 ms
  of the pass. Sequencing killed it: with the prepared checked-form memo in place first, both sweeps
  share the memo and the second costs what the first does, so the merge is worth ~50 ms and not its
  own split lemma. Re-propose only if the justification ever becomes expensive again.

- **Scanning constraints before the bus in hintCollapse's code array** (entry 173), to skip the bus
  walk when nothing can fire: rejected on the structure of the codes, not on a timing. Without the
  bus marks first, a `2 + i` code means only "in one constraint", which every memory limb satisfies
  (one constraint plus its bus interactions) — so essentially every system still has entries with
  two such variables and pays the bus walk anyway, while the constraint sweep does strictly more
  writes and the candidate list grows from ~4 entries to tens of thousands. Bus-first is what makes
  a `2 + i` code mean *witness*, and it is why the survivors need no filter at use.
- **Collapsing every candidate target per hintCollapse invocation** (entry 173) instead of the
  first: the pass fires ~1× per run on the measured cases, and its cost is the sweeps plus the
  degree guard, not the collapses — so this buys no runtime while changing the intermediate system
  the other 26 cleanup passes see. An effectiveness change to argue, not a runtime one.
- **A dictionary-free `denseExtractLinear`** (entry 173): the generated C rebuilds the whole
  `ZMod.commRing → … → MulZeroClass` chain at the head of *every* recursive call (for its
  `.const 0` / `.const 1` leaves), which the mechanical C sweep flags — but the peel runs only on
  candidate constraints and measured **0 ms** on sha256. Per-candidate cost is not per-system cost;
  size a C-sweep hit against the phase timers before acting on it.

- **A per-`(busId, multiplicity, pattern)` memo of the whole slot-bound vector** (entry 172,
  intervalForce): rejected on the *keys*, not on a timing. `slotBoundImpl` reads one pattern
  position per bus type (memory slot 0, bitwise slot 3, range-checker slot 1), but memory payloads
  also carry constant pointers and timestamps that differ per interaction — so a memo keyed on the
  whole pattern misses on nearly every hit that would matter, and keying on the relevant positions
  is `BusFacts`-specific knowledge a pass does not have. The fix belongs at the interface (R13(b)).
- **An `Array`-backed raw-term buffer for intervalForce's linearization** (entry 172), with an
  in-place region scale for `mul` instead of the list accumulator. Built and measured first: keccak
  63 vs 68 ms, wasm-eth `apc_012` 74 vs 81, identical output — real, but ~5 ms on a 2.4 s run
  against the whole `Array.modify`/`toList`/index-arithmetic layer in the proof *plus* a
  from-scratch `denseMergeTerms` equality. The list form is `denseLinearizeAcc` plus one changed
  arm, so it inherits `Affine`/`Normalize`'s lemmas wholesale. Revisit only for a corpus with large
  affine slots (present maximum 24 merged terms).

- **An in-place `Array` like-term merge in normalize's materializer** (entry 171): a linear scan +
  `Array.set` buffer folded straight into the `toExpr` spine, instead of the shipped
  `denseMergeTerms` over a counted prefix. Implemented and measured **5–8 % better on the pass**
  (keccak 101 vs 110 ms, wasm-eth `apc_012` 131 vs 145, identical output) — real, but below the
  land bar alone and ~150 lines of `take`/`drop`/`set` index proof. Merging the prefix *in list
  form* without the `List.take` copy (`denseNrmMergePre`) measures the same as `take`: the win is
  the in-place update, not the copy. Revisit only if a corpus appears with large affine forms (the
  present maximum is 24 terms, mean 1.6).
- **An eager raw-slot bound index over every variable** (entry 170, rootPairUnify): a sweep building
  `VarId → List (busId, mult, Thunk pattern, slot)` so a raw bound query costs one `BusFacts` call
  with no payload walk and no re-derived slot pattern. Worse on **every** case — sha256 `apc_001`
  1220 → 1324 ms, keccak 93 → 100, wasm-eth `apc_012` flat — because it inserts ~1 M
  (variable, interaction) entries per invocation to serve **~900 queries in the whole run**. Eager
  indexing loses whenever the query set is orders of magnitude smaller than the index; restrict the
  sweep to the variables that will be queried (R9d) or leave it lazy.
- **A memoizing bound table for rootPairUnify** (entry 170): `Std.HashMap VarId (Thunk (Option Nat))`
  over the candidate variables, forced on first use, to stop a `seen` entry re-deriving its bound
  once per compared pair. **Exactly 0** on sha256 (886 vs 887 ms) and noise on keccak: the queries
  are already almost all for distinct variables, because the bound gate keeps same-key non-twins out
  of the certificate. A memo needs repeated *keys*, not repeated call sites.
- **A constant-only pre-walk to skip linearizing** (entry 170, `denseRpConstOf`): computing a
  factor's linearized constant and term-emptiness without allocating, to decide `δ = 0` before the
  merge. On sha256 cycle 0 it filters 104 264 products to 40 958 and costs **59 ms against the 68 ms
  of linearizing all of them** — the tree walk is the expensive half of `denseLinearize`, the
  allocation is not.

- **An unchanged-node-preserving `DenseExpr.substF` twin** (entry 169): returning the input node
  when no descendant changed cut domainBatch by 144 ms and cost **+2.5 s across every other pass**
  on sha256 `apc_001` (30.4 → 32.9 s, +10–20 % on essentially all of them, identical per-cycle
  sizes). Sharing keeps the input expressions' refcounts above one, which disables Lean's
  reset/reuse in-place rebuild in every downstream pass that rewrites expressions. The array-backed
  lookup is the part that pays; the sharing is not.
- **A strided-diagonal pre-probe of domainBatch's box** (entry 169): point `i` gives key `d` the
  element `(i·(2d+1)) mod size_d`, to kill keys before the lexicographic sweep. A loss on every
  case — sha256 19.44 M → 24.30 M points enumerated, because the probe rarely reaches `live == 0`
  and the scans it cannot finish pay its full length on top of the sweep. Survivors do not lie on a
  generic line. Relatedly, *reversing* domainBatch's key order is best on sha256 (11.77 M) but 2.7×
  worse on keccak; only the stable descending-by-domain-size sort improves every case (shipped).
- **Applying bytePack's packs positionally into an array** (entry 168): `Array (Option
  BusInteraction)` with `set!` at the two packed positions, then a filtered rebuild. Measures the
  *same* as the shipped re-checking sweep (sha256 `apc_001` 242 vs 254 ms, identical output), but
  its correctness needs index distinctness and in-range obligations about the plan — i.e. the plan
  becomes trusted, for ~1 % of runtime. Prefer a re-checked proposal whenever the check is O(1) per
  action.
- **Fusing bytePack's plan pass into its applier** (entry 168): the pairing parity is
  left-to-right information and the applier must run right-to-left (so the closer's value is in
  hand when the opener is reached). Fusing them means emitting the pair check at the *closer's*
  position, which changes the output list order — an effectiveness change, not a runtime one.

- **Solving domainFold's last enumerated key instead of scanning its domain** (entry 167): an affine
  filter with invertible leading coefficient determines its largest key, so the level could evaluate
  once and test membership. Implemented and **reverted — it regressed**: keccak 134 → 149 ms (1.11x),
  wasm-eth `apc_036` 90 → 93, openvm-eth `apc_009` 29 → 31. The covered constraints are *quadratic or
  worse in their largest key* (83 % in the first cleanup invocation, **100 % in every later one** —
  products, not sums), and where a filter is affine the last-level domain holds 2–3 values, so one
  evaluation plus an inverse plus a membership test saves nothing while the coefficient extraction
  costs a walk per filter per target. Needs a corpus with affine covered constraints to revisit.
- **Prefix pruning in domainFold's box enumeration** (entry 167): 119 231 extensions against a
  108 708-point box on keccak, i.e. *no* pruning — 66 % of the filters close at the last level
  (widths 3–8 keys over 4–5-key targets). Keeping the level structure is free; reordering keys to
  close filters early is worth at most ~2x (the last level is half the tree) and would thread a
  permutation through the compile, the survivor columns and the proof.

- **A three-bit `UInt8` summary walk for disconnected's fused re-check** (entry 166): one walk
  computing has-a-variable / some-removable / some-not measures the *same* as two separate
  `dcAnyVar` / `dcAllVar` walks (keccak 35 vs 37 ms, identical output) and costs ~3x the proof
  (bitmask reasoning against `vars` instead of two `List.any`/`List.all` inductions). Two walks win
  on their own terms: `dcAnyVar` exits on the first variable of a removed item, and is the only walk
  a kept item pays.

- **Dropping gauss's second source-order sweep** (entry 160): looks provably fruitless over a prime
  field, and measures openvm-eth `apc_037` gauss **170 → 317 ms** with changed output — 35 % of that
  case's pivots come from it, all nonlinear→affine transitions.
- **Source order at every system size in gauss** (entry 160): **1.88x slower** on wasm-eth `apc_012`,
  98 % of the pass in the like-term merge, because eagerly maintaining a reduced σ in source order
  inflates a stored solution to 586 terms before it cancels back to 7.
- **Removing gauss's 8192 gate** (entry 160): runtime-neutral on OpenVM (corpus 1.006x) and slightly
  better there, but **regresses 8 of 100 SP1 `rsp` cases by +88 variables** — the primary axis. Entry
  134's warning, now measured.

- **Signature-*gating* busUnify's exact verifier arms** (2026-08-01): keeping
  `denseConstDiffNZ` behind an order-insensitive term-hash comparison measures **neutral to
  worse** (sha256 `apc_001` verify 226 vs 201 ms ungated, keccak 58 vs 55). In a `mid` scan every
  position must be *refuted*, so the deciding arm is the one that **succeeds** — where the gate
  always passes and only adds a compare. The win is in *replacing* the test with a canonical-key
  comparison, not gating it (done, 0.86x on the pass).
- **Hash-consing busUnify's prepared address slots** (2026-08-01): memoizing `denseBUSlotPrep` by
  `DenseExpr.bHash` with a structural re-check made prep **99 → 367 ms** on sha256 `apc_001`. The
  address-slot derivations (`constValue?`, `denseLinearize`, `densePtrReductions`) cost ~0.7 µs
  per slot; a `Std.HashMap` probe plus a deep expression compare costs more than that. Distinct
  address *tuples* being few (587 for 29 372 messages) does not make the memo pay.
- **Dropping busUnify's `mentionsAny` pre-filter before the two-root build** (2026-08-01): the
  builder already filters per variable, so the filter looks redundant — but folding the raw
  constraint list instead measures **scope+build 8 → 26 ms on keccak and 9 → 55 ms on wasm-eth
  `apc_012`** (identical map), because every product constraint then pays two `denseLinearize`s.
  The fail-fast tree walk is cheaper than linearizing.
- **A same-key sparse `mid` scan for busUnify's verifier** (entry-148 pattern): the two cycles
  where the verifier is expensive on sha256 `apc_001` (88 and 84 ms) are 12 % all-constant
  addresses, while the two cycles that are 96 % all-constant cost 30 and 39 ms. The index would
  help exactly where the scan is already cheap.
- ~~**Indexing `densePdKeep`'s re-verification**~~, ~~**flagFold's `boxTautoDrop` prologue**~~ and
  ~~**dropping flagFold's domain memo**~~: all three superseded by **entry 165**, which rebuilt the
  pass (0.17–0.32x). The re-verification was not worth indexing — it was worth *not triggering*: it
  was refuting the sweep's own exact-duplicate proposals, which `densePdKeep` can never accept
  (it is value-scoped, so the earlier copy is the position it tests at). The prologue's pieces landed
  as one shared table plus an allocation-free rejection gate. The memo question was re-measured and
  the answer flipped for the same reason as before: a `Thunk`-per-variable *lazy* table loses 4 %,
  because the gate forces essentially every entry — an eager build over the buckets is right.
- **flagFold's remaining `denseRootsIn`** (entry 165): 292 ms of the post-rebuild 1 278 ms on sha256
  `apc_001`, 23 489 single-variable constraints at ~2.8 µs each, essentially all consumed. A
  specialized single-variable root finder (a direct `(a, c)` walk instead of `denseLinearize` +
  `norm` + `denseRootsOfTerms`, three times over for a product) would cut most of it, but it must
  return the *identical* list and `denseRootsIn` is shared with domainFold/rootPairUnify — its own
  change, with its own proof.
- **Short-circuiting flagFold's re-verification with the sweep's witness**: `densePdKeep bi = false`
  follows from one `densePdFirst` check on the representative that matched, instead of a prefix
  scan. ~25 ms, and only on invocations that drop something — openvm-eth `apc_067` is the only
  measured case (its pass is 0.55x where the others are 0.17–0.24x).

- **Retiring domainBatch's task fan-out** (`parallel := false`): 0.96× sha256 / 0.91× keccak against
  the pre-entry-155 baseline, but **+700 ms on top of entry 155** (measured twice) and a wash on
  keccak. The fan-out loses only on cycle 0 — whose work entry 155 deleted — and wins on the
  box-heavy tail cycles (cycle 5: 182 ms parallel vs 919 ms serial). The live lever is
  `DenseForcedScanV.work`, which models `boxSize × items` and ignores the boxSize-independent
  per-item compile term; it appears in no soundness lemma, so re-weighting it is proof-free.
- **Entry 154's work-gated gathers (`denseCapStep`, PR #250) on top of entry 155**: 8944 vs 8983 ms
  on sha256 and ≤ 1 % on six other cases, both signs — noise. Its 0.81× came from the cap aborting
  inside the 3 446-item variable-free tail; with the tail an O(1) seed there is nothing left to
  abort. Subsumed, not complementary.

- **Adopting the Markowitz row's maintained `reduced` form instead of re-substituting the source
  constraint** (gauss): the from-source `denseSparseSubstF dσ.fn c` on selection measures **134 ms
  per big invocation, ~0.27 s over the sha256 run (2.2 % of the pass, entry 158)** — sub-bar, and it
  is what makes every heap decision untrusted (the pass's soundness story is "re-solve from the
  source under the current substitution before adopting"). Reusing the maintained row would move the
  entailment obligation onto a per-row scheduler invariant for 2 % of the pass.
- **Bundling gauss's array conversion with algorithm changes** (PR #193, 2026-07-23): exact live
  reverse dependencies + streaming pivot selection + specialized final substitution + no solution
  materialization, all at once, measured a **regression** (3 954 vs 3 287 ms on wasm-eth `apc_037`)
  and never landed. The representation-only slice of the same idea is 0.86x (entry 158). Land the
  piece you can measure alone.
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
- **LBR attribution is unusable on a deeply recursive pass** (2026-08-01): on busUnify only
  **4.4 % of samples carried a pass frame against 21.7 % of wall** — the sweep recurses deeper
  than the LBR buffer, so the pass-restricted table is off by 5x, not by a margin. Every number in
  the busUnify rebuild came from `IO` phase timers. `OptimizingRuntime.md`'s truncation warning
  understates this case; check the gated `tot` against the pass's share of wall *before* reading
  any pass-restricted table.
- CI notes: **the effectiveness matrix's `main` side is a downloaded artifact, and it can be stale
  by days** (`Latest-main binary` step: `gh run list --branch main --status success --limit 1` then
  `gh run download`). Measured on PR #278 (entry 173): that cell reported wasm-eth
  `145.9 s → 14.2 s (-90 %)` and SP1 rsp `41.1 s → 2344 ms (-94 %)` for a change worth ~4 %, and
  flagged "sizes changed on 3 of 200 cases" — while the *same* three cases are identical between the
  branch and CI's own current-main artifact (checked with CI's own `compare`, 15 repeats, and five
  consecutive main builds, none of which produces the reported `main` values). A ~6-day-old main
  build does produce one of them and is 4–5× slower per case, which with the parallel contention
  accounts for the row. **So a flagged size change or a spectacular runtime row in that cell means
  "check the baseline first": re-run the size comparison against a freshly built main (or the newest
  `apc-optimizer-bin` artifact) before believing either.** The serial `Runtime Bench` workflow builds
  both sides from source on one runner and is unaffected — on #278 it read 0.96× total / 0.11× on the
  pass, matching the local interleaved bench exactly.
- CI notes (updated 2026-07-29): the effectiveness-matrix runtime row swung **+51 % → +15 % on
  identical code** for openvm-eth while its own per-pass table showed ≤1.04× — treat the wall row
  as ±50 % noise on the small parallel sets and read the per-pass table instead; the serial
  `Runtime Bench` workflow (dispatch-only, openvm sets only) is the real A/B. **Entry 153 re-confirmed
  this quantitatively**: the row read wasm-eth +20 %, SP1 rsp +67 %, openvm-eth +5 % for a change that
  the serial `Runtime Bench` on the same runner put at **0.99× total / 0.83× on the pass**, and that a
  local serial interleaved re-run of all three sets (300 cases) put at **0.951× wall / 0.570× on the
  pass**, with every case ≥ 50 ms of pass time improving. The row's per-case outliers are 8–80 ms
  cases carrying 0–5 ms of the pass: on SP1 rsp, 28 cases came out >5 % slower and 30 >5 % faster.
  `benchmark.py` runs cases with `--jobs = cpu_count`; the runtime it prints is scheduling, not work.
  Peak RSS is worth one check when the row moves (entry 153: 241.7 → 228.1 MB on wasm-eth apc_012),
  since memory pressure is the one mechanism that *would* make a parallel-only regression real. This container has
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
- **domainBatch: prefix-pruned or component-split enumeration** (was R13(d)): the wide boxes on the
  big OpenVM cases are single-variable, so neither the pruning nor the `∏ → Σ` split has anything to
  cut. Measured on a box-shape counter, entry 162.
- **domainBatch: fusing the three per-constraint prologue walks into one** (entry 162): one walk
  returning a tuple allocates per node and replaces two allocation-free walks — sha256 4 254 → 4 321
  ms. Same for a flat scalar item table in place of the compiled tree, a fail-fast root miner, and
  sampling the box instead of sweeping it. Restructuring a traversal loses to removing work from it.
  (Entry 169 *did* fuse the two traversals that each already walk the whole item — item compile with
  the flag computed alongside it — which is removing a traversal, not restructuring one; and it
  dropped the compiled tree entirely, which measured neutral but deletes a proof layer.)

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
- **Count the change before proving it.** Entry 153 validated a fold reformulation with a throwaway
  `dbg_trace` probe that ran the proposed function *next to* the real one on every candidate of the
  worst case: identical verdict on 14 433/14 433 and a 33× drop in visited positions, both known
  before a line of proof. A counter probe is cheaper than a prototype and strictly more informative
  than a sample share.
- **Re-attribute after every landing; a pass's residual moves.** Entry 148's closing note put
  busPairCancel's remaining cost in "per-drop `alive` copies, `denseCheckCancel`, `denseFirstMatchAt`";
  measured in entry 153 those are 2.1 %, ~0 % and ~0 % — the cost had never left the region scans, it
  had only moved from "every prefix position" to "every same-key-or-symbolic prefix position".
- **`Array` sharing hygiene decides whether array indexes are fast at all** (entries 160–161, measured
  on keccak and sha256). Three traps, all the same cause: `{ S with f := g S.f }` leaves `S.f` shared,
  so the write copies the whole array (**7x on the pass** when the array is per-variable); projecting
  `.1`/`.2` out of a returned tuple does the same; and **reading a field for a before/after comparison
  across a call that updates it** keeps it shared for the whole call — `let n := S.order.size; let S :=
  gTake … S …; S.order.size != n` cost **34 % of gauss on sha256**, one O(|order|) copy plus
  element-wise free per adoption. Destructure the record (or the tuple) first; derive "did it change?"
  from state read *after* the call, never from a value captured before it. A profile showing
  `lean_copy_expand_array` next to `lean_dec_ref_cold` is this bug, not real work.
- **`Task.spawn` is not free to try.** It marks every shared heap object multi-threaded
  *permanently*, so all later refcount operations on them are atomic — in the spawning pass and in
  every pass after it. Measure the whole run, not the parallel section (entry 162).
- **Structural sharing in a pass's output is a downstream tax.** Returning shared subterms costs the
  pass nothing and defeats Lean's reset/reuse in every later pass that rewrites those nodes: 4.5 s
  on sha256 for a sharing substitution that looked free (entry 162).
- **A/B the total against the baseline binary, not just the pass's column.** A constant downstream
  penalty is invisible to within-engine comparisons (entry 162).
- **`partial def` admits no equation lemmas** — nothing can be stated about it, so a loop that will
  ever need a proof must carry a termination measure from the start (entry 162).
- **Check open PRs / recent `claude/*` branches for duplicates before implementing.**

## Runtime ideas (2026-07-27 session, entry 148)

- **Per-drop `alive` copies in busPairCancel**: **measured (entry 153) at 2.1 % of the pass**
  (~410 ms of 19.3 s on sha256 `apc_001`), 97 % of it `lean_copy_expand_array` — the array is still
  referenced by the loop frame, so the first `setIfInBounds` copies all 71 402 entries (≈ 8 GB of
  memcpy over 14 418 drops). Below the land bar on its own; bundle it with a bigger change. Cheap
  forms: a `ByteArray` (1 byte per entry, 8× less copying) or handing both tombstone positions to
  `denseCancelLoop`, which owns the array uniquely. **Do not** switch to a `Std.HashSet Nat` of
  tombstones: liveness is *read* tens of millions of times per invocation.
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
- ~~**domainBatch cycle 0 (26–28 s for 2.6k vars)**: the cost is hot-variable buckets × many
  candidate groups; gate groups on a gather-size bound or dedupe overlapping groups~~ **wrong,
  measured (entry 152)**: gathers are 4.6 % of the pass at sha scale and target dedup 0.4 %; the
  per-target cost that follows them is the survivor *compile* (56 %), not the gather or the scan.
  See R13.
- ~~**flagFold cycle 0 (24 s, zero effect)**: NOT the domain lookups (bucketing them changed
  nothing). Suspect `denseFuCandidates`' per-interaction `O.vars.eraseDups × splitAt`~~ — **both
  halves wrong, measured (entry 157)**. It *was* the domain lookups: `denseBtPre` and `denseBtCert`
  are the same predicate over different domain sources, and the earlier session bucketed the
  prefilter while the certificate kept scanning all 23 489 single-variable constraints per queried
  variable. Fixed, 0.349x on the pass. And `denseFuCandidates` is **166 ms of the whole sha256 run**
  (50 ms in cycle 0): the per-variable `splitAt` really does allocate a full copy of the slot-0
  payload just to test `R.vars.isEmpty`, and a coefficient-plus-`hasVar` twin would avoid it, but
  `fxSubst`'s entire real cost is ~0.85 s and `denseFuPairData?` never fires on this APC
  (`solved = 0` on every invocation). Sub-bar; do not build it without a case where `fxSubst`
  dominates.
  **The lesson worth keeping: when two functions compute the same predicate, an index wired into
  one of them buys nothing.** Check which one the hot path calls.

### domainBatch residual after entry 151 (byte-operand domains)  ·  *runtime, sp1*  ·  medium value
Entry 151 BISECTED domainBatch (the ideas' "58% is the domain-table build/cache" guess was WRONG — the
build is ~2%, the box SCANS are ~94%, all in cleanup cycle 4) and cut the dominant cost 4x by mining
byte-operand bounds into the table (585 single-var 2^16 brute-force scans → 256-element cosets). What
remains for a next pass:
- **Two-variable deep scans** (cycle 4 had ~108 of them, boxes up to 65536 = ~256×256): entry 151's
  coset shrink is single-var-operand; if BOTH operands of a byte/tuple interaction are affine in
  distinct vars, each var could still get a coset, shrinking the 2-D box. Verify how many 2-var deep
  scans survive after entry 151 (re-run the point counter) before implementing — the same counter
  R13(d) needs.
- **Fuse the coset build** — now measured at **21.3 % of the pass on SP1 keccak** (entry 152), the top
  SP1 item; see R13(c) for the preferred lazy-`FiniteDomain` form.
- ~~**Skip byte-domain work when it can't shrink**~~ **done**: `denseAddByteVarDoms` builds the coset
  only when `spec.bound < d0.size`.
- Post-entry-151 the SP1 pass profile matches OpenVM's: box scans are 1.3 % and the cost has moved to
  the per-target classification and the coset build (R13).
