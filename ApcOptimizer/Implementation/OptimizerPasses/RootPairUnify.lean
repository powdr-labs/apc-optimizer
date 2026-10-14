import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup
import ApcOptimizer.Implementation.OptimizerPasses.VarBucket

set_option autoImplicit false

/-! # Dense two-root decomposition unification

Recognizes pairs of two-root-decomposed constraints sharing a root gap and unifies them via a
substitution. Impl-only: the top transform `denseRootPairUnifyF` is shaped like `denseBusUnifyF`
(`BusUnifyNative.lean`), so `Proofs/RootPairUnify.lean` wraps it with `DenseVerifiedPassW.of`.

`ZMod p`'s `Inv` is total for every `p`, so nothing here needs `[Fact p.Prime]` to compute; only
soundness does. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Constant-coefficient decomposition (`DenseExpr.splitAt`, shared dense helper)

Unlike `denseLinearize`, the remainder may be nonlinear, so this succeeds where the affine machinery
gives up. -/

def DenseExpr.splitAtImpl (x : VarId) : DenseExpr p → Option (ZMod p × DenseExpr p)
  | .const n => some (zmodZeroP p, .const n)
  | .var y =>
      if y = x then some (zmodOneP p, .const (zmodZeroP p))
      else some (zmodZeroP p, .var y)
  | .add a b =>
      match a.splitAtImpl x, b.splitAtImpl x with
      | some (ca, ra), some (cb, rb) => some (zmodAdd ca cb, .add ra rb)
      | _, _ => none
  | .mul a b =>
      if a.mentions x || b.mentions x then
        match a.constValue? with
        | some k =>
            match b.splitAtImpl x with
            | some (cb, rb) => some (zmodMul k cb, .mul a rb)
            | none => none
        | none =>
            match b.constValue? with
            | some k =>
                match a.splitAtImpl x with
                | some (ca, ra) => some (zmodMul k ca, .mul ra b)
                | none => none
            | none => none
      else some (zmodZeroP p, .mul a b)

/-- Decompose `e` as `k·x + r`: `k` a field constant, `r` not mentioning `x` (by construction). -/
def DenseExpr.splitAt (x : VarId) : DenseExpr p → Option (ZMod p × DenseExpr p)
  | .const n => some (0, .const n)
  | .var y => if y = x then some (1, .const (zmodZeroP p)) else some (0, .var y)
  | .add a b =>
      match a.splitAt x, b.splitAt x with
      | some (ca, ra), some (cb, rb) => some (ca + cb, .add ra rb)
      | _, _ => none
  | .mul a b =>
      if a.mentions x || b.mentions x then
        match a.constValue? with
        | some k =>
            match b.splitAt x with
            | some (cb, rb) => some (k * cb, .mul a rb)
            | none => none
        | none =>
            match b.constValue? with
            | some k =>
                match a.splitAt x with
                | some (ca, ra) => some (k * ca, .mul ra b)
                | none => none
            | none => none
      else some (0, .mul a b)

@[csimp] theorem DenseExpr_splitAt_eq_impl : @DenseExpr.splitAt = @DenseExpr.splitAtImpl := by
  funext q x e
  induction e with
  | const n => simp [DenseExpr.splitAt, DenseExpr.splitAtImpl]
  | var y => by_cases h : y = x <;> simp [DenseExpr.splitAt, DenseExpr.splitAtImpl, h]
  | add a b iha ihb => simp only [DenseExpr.splitAt, DenseExpr.splitAtImpl, iha, ihb, zmodAdd_eq]
  | mul a b iha ihb =>
      simp only [DenseExpr.splitAt, DenseExpr.splitAtImpl, iha, ihb, zmodMul_eq, zmodZeroP_eq]

/-! ## Bounds through scaled range checks

The low mem-ptr limb's range check carries not the raw limb but a scaled slot `4⁻¹·(x − F)` for a
small flag polynomial `F`. The slot value is still fact-bounded, so `x = k⁻¹·slot − k⁻¹·R` is
bounded once the offset part `R` enumerates over its (tiny, provable) flag domains. -/

/-- Bound `x` through one interaction: find a slot whose expression is affine in `x` with a unit
    coefficient and a bus-fact value bound; enumerate the remaining variables' proven finite domains
    for the offset part. Returns `B` with `x.val < B` under acceptance. -/
def denseScaledSlotBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (domCs : List (DenseExpr p)) (bi : BusInteraction (DenseExpr p)) (x : VarId) :
    Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none else
    (List.range bi.payload.length).findSome? (fun slot =>
      match bi.payload[slot]? with
      | none => none
      | some O =>
        match facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot with
        | none => none
        | some bound =>
          match O.splitAt x with
          | none => none
          | some (k, R) =>
            let m := k⁻¹
            let others := R.vars.eraseDups
            let doms := others.filterMap (fun v =>
              (denseFindDomainAlg domCs v).map (fun d => (v, d)))
            if k * m = 1 ∧ doms.map Prod.fst = others ∧
                (doms.map (fun vd => vd.2.length)).prod ≤ 16 then
              if m.val * (bound - 1) + ((denseAssignments doms).map
                    (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 < p then
                some (m.val * (bound - 1) + ((denseAssignments doms).map
                  (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 + 1)
              else none
            else none)

/-! ## Value bound lookup -/

/-- The value bound of `x` derived from the first bus obligation that bounds it. -/
def denseFindVarBound (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → VarId → Option Nat
  | [], _ => none
  | bi :: rest, x =>
    match denseInteractionBound bs facts bi x with
    | some bound => some bound
    | none => denseFindVarBound bs facts rest x

/-- Bound `x` from a raw slot (`denseFindVarBound`) or, failing that, through a scaled slot
    (`denseScaledSlotBound`). -/
def denseAnyVarBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (x : VarId) : Option Nat :=
  match denseFindVarBound bs facts bis x with
  | some B => some B
  | none => bis.findSome? (fun bi => denseScaledSlotBound bs facts domCs bi x)

/-! ## The pair certificate (dense) -/

/-- Decidable certificate that constraints `cX` (in `x`) and `cY` (in `y`) are two-root twins and
    both variables are range-bounded below the root gap, with the two value bounds served by
    `bnd` (`denseRpCheckPair` instantiates it with the scanning lookup). -/
def denseRpCheckPairB (bnd : VarId → Option Nat) (cX cY : DenseExpr p) (x y : VarId) : Bool :=
  match denseTwoRootOf? cX x, denseTwoRootOf? cY y with
  | some (k, A, δ), some (k', A', δ') =>
    decide (k' = k) && decide (A'.terms = A.terms) && decide (A'.const = A.const) &&
    decide (δ' = δ) && decide (k * k⁻¹ = 1) &&
    decide (x ∈ cX.vars) && decide (y ∈ cY.vars) &&
    (match bnd x, bnd y with
     | some Bx, some By =>
       decide (max Bx By ≤ (k⁻¹ * δ).val) && decide (max Bx By ≤ p - (k⁻¹ * δ).val)
     | _, _ => false)
  | _, _ => false

/-- The pair certificate with both bounds derived by scanning the full interaction list. -/
def denseRpCheckPair (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) (domCs : List (DenseExpr p))
    (cX cY : DenseExpr p) (x y : VarId) : Bool :=
  denseRpCheckPairB (denseAnyVarBound bs facts bis domCs) cX cY x y

/-! ## Candidate preparation (dense)

A two-root candidate is a `(constraint, variable)` pair whose key `(k, A.terms, A.const, δ)` is
matched against earlier candidates' keys. Both factors are merged **once** per constraint and each
candidate reads its data off the merged pair: for a linearized factor `l`,
`(l.others x).norm.terms` is exactly `(merge l.terms) \ x` — `denseMergeTerms` keeps
first-occurrence order, so filtering before or after the merge gives the same list. Nothing here is
trusted; `denseRpCheckPairB` re-derives every proposed pair's two-root data. -/

/-- No entry of `ts` carries `v`. -/
def denseRpNoVar (v : VarId) : List (VarId × ZMod p) → Bool
  | [] => true
  | (w, _) :: rest => !(w.index == v.index) && denseRpNoVar v rest

/-- Whether a term list is already a normal form: distinct variables, no zero coefficient. Checking
    this costs index compares only, where the general merge allocates a list per term. -/
def denseRpTermsClean : List (VarId × ZMod p) → Bool
  | [] => true
  | (v, c) :: rest => !(c.val == 0) && denseRpNoVar v rest && denseRpTermsClean rest

/-- The normal form of a linearized factor's terms, sharing the input when it is already normal. -/
def denseRpMerged (ops : DenseZModOps p) (ts : List (VarId × ZMod p)) : List (VarId × ZMod p) :=
  if denseRpTermsClean ts then ts else denseDropZeroWith ops (denseMergeTermsWith ops ts)

/-- The coefficient `x` carries in a normal form. -/
def denseRpCoeffIn : List (VarId × ZMod p) → VarId → Option (ZMod p)
  | [], _ => none
  | (v, c) :: rest, x => if v.index == x.index then some c else denseRpCoeffIn rest x

/-- Whether `l1 \ x` and `l2 \ y` are equal, by one simultaneous walk skipping each side's own
    candidate entry (the offset-form comparison behind a key match). -/
def denseRpSkipEq : List (VarId × ZMod p) → VarId → List (VarId × ZMod p) → VarId → Bool
  | [], _, [], _ => true
  | (v, c) :: r1, x, l2, y =>
      if v.index == x.index then denseRpSkipEq r1 x l2 y
      else match l2 with
        | [] => false
        | (w, dd) :: r2 =>
            if w.index == y.index then denseRpSkipEq ((v, c) :: r1) x r2 y
            else v.index == w.index && c.val == dd.val && denseRpSkipEq r1 x r2 y
  | [], x, (w, _) :: r2, y => if w.index == y.index then denseRpSkipEq [] x r2 y else false
  termination_by l1 _ l2 _ => l1.length + l2.length

/-- `none` when the two normal forms are identical — every variable is a candidate; otherwise the
    at most two variables a candidate can still be. Entries before the first difference are equal,
    so removing a variable occurring there removes the same position from both lists and leaves the
    difference in place: only the differing position's own variables can qualify. -/
def denseRpDiffVars : List (VarId × ZMod p) → List (VarId × ZMod p) → Option (List VarId)
  | [], [] => none
  | (v, c) :: r1, (w, dd) :: r2 =>
      if v.index == w.index then
        (if c.val == dd.val then denseRpDiffVars r1 r2 else some [v])
      else some [v, w]
  | (v, _) :: _, [] => some [v]
  | [], (w, _) :: _ => some [w]

/-- A candidate's shared per-constraint data: the constraint, the first factor's normal form (the
    key's offset terms with `x` still in), the key's constant and root offset, and a multiset hash
    of the terms, from which each candidate's bucket hash is one subtraction. -/
structure DenseRpSrc (p : ℕ) where
  c : DenseExpr p
  terms : List (VarId × ZMod p)
  aconst : ZMod p
  δ : ZMod p
  tsum : UInt64

/-- A candidate, and once bucketed a previously seen one: its constraint's shared data, its
    variable and coefficient, its bucket hash, and the root gap `g = k⁻¹·δ` as the two `Nat` bounds
    the certificate compares against. -/
structure DenseRPSeen (p : ℕ) where
  src : DenseRpSrc p
  x : VarId
  k : ZMod p
  h : UInt64
  gval : Nat
  gco : Nat

/-- The constraint a candidate came from. -/
def DenseRPSeen.c (e : DenseRPSeen p) : DenseExpr p := e.src.c

/-- Hash of one term of a key's offset form. -/
def denseRpTermHash (v : VarId) (c : ZMod p) : UInt64 := mixHash (hash v.index) (hash c.val)

/-- Multiset hash of a term list: a sum, so dropping the candidate's own term is a subtraction. -/
def denseRpTermsSum : List (VarId × ZMod p) → UInt64
  | [] => 0
  | (v, c) :: rest => denseRpTermHash v c + denseRpTermsSum rest

/-- Bucket hash of the key `(k, A.terms, A.const, δ)`, `asum` being `A.terms`' multiset hash.
    Bucketing never hides a twin — equal keys hash equal — and the scan's exact test separates
    collisions. -/
def denseRpBucketHash (k aconst δ : ZMod p) (asum : UInt64) : UInt64 :=
  mixHash (hash k.val) (mixHash (hash aconst.val) (mixHash (hash δ.val) asum))

/-- The candidate variables of one constraint, with their coefficients: `cands` is the first
    factor's own normal form when the two forms agreed (shared, not rebuilt). -/
structure DenseRpPre (p : ℕ) where
  src : DenseRpSrc p
  cands : List (VarId × ZMod p)

/-- The candidate variable and coefficient for one explicitly proposed variable: it must carry the
    same coefficient in both normal forms, which must agree away from it. -/
def denseRpCandOne (terms n2 : List (VarId × ZMod p)) (x : VarId) : Option (VarId × ZMod p) :=
  match denseRpCoeffIn terms x, denseRpCoeffIn n2 x with
  | some k, some k2 =>
      if k.val == k2.val && denseRpSkipEq terms x n2 x then some (x, k) else none
  | _, _ => none

/-- One constraint's two-root data: the first factor's normal form, the candidate variables with
    their coefficients, the key's constant and the root offset. A product of two affine factors
    whose normal forms differ only in their constant contributes one candidate per variable; a
    nonzero constant gap `δ` is necessary (the root gap `k⁻¹·δ` would otherwise be `0`), and is
    checked before merging. -/
def denseRpDataOf (ops : DenseZModOps p) (c : DenseExpr p) :
    Option (List (VarId × ZMod p) × List (VarId × ZMod p) × ZMod p × ZMod p) :=
  match c with
  | .mul f1 f2 =>
    (match denseLinearizeWith ops f1, denseLinearizeWith ops f2 with
     | some l1, some l2 =>
       let δ := ops.add l2.const (ops.mul ops.negOne l1.const)
       if δ.val == 0 then none else
       let n1 := denseRpMerged ops l1.terms
       let n2 := denseRpMerged ops l2.terms
       match denseRpDiffVars n1 n2 with
       | none => if n1.isEmpty then none else some (n1, n1, l1.const, δ)
       | some vs =>
         match vs.filterMap (denseRpCandOne n1 n2) with
         | [] => none
         | cands => some (n1, cands, l1.const, δ)
     | _, _ => none)
  | _ => none

/-- Every constraint's candidate variables, in source order. -/
def denseRpPres (ops : DenseZModOps p) : List (DenseExpr p) → List (DenseRpPre p)
  | [] => []
  | c :: rest =>
    match denseRpDataOf ops c with
    | some (terms, cands, aconst, δ) =>
        (⟨⟨c, terms, aconst, δ, denseRpTermsSum terms⟩, cands⟩ : DenseRpPre p) ::
          denseRpPres ops rest
    | none => denseRpPres ops rest

/-! ### Root gaps

A candidate's root gap `g = k⁻¹·δ` decides whether it can ever be unified: the pair condition
`B ≤ min(g.val, p − g.val)` cannot hold for a useful bound `B` when the gap is tiny, and booleanity
constraints `b(b−1) = 0` would otherwise make every boolean variable a (never-unifiable,
expensive-to-reject) candidate. `ZMod`'s `Inv` is an extended gcd — the single most expensive
operation in the pass — and a coefficient repeats across every constraint of the same instruction
shape, so the inverses are tabulated once per invocation by value. -/

/-- One inverse per distinct candidate coefficient. -/
def denseRpInvTable (pres : List (DenseRpPre p)) : Std.HashMap Nat (ZMod p) :=
  pres.foldl (fun m pre =>
    pre.cands.foldl (fun m t =>
      if m.contains t.2.val then m else m.insert t.2.val t.2⁻¹) m) ∅

/-- The candidate record for `x` with coefficient `k`, unless its root gap is tiny. -/
def denseRpCandAt (ops : DenseZModOps p) (inv : Std.HashMap Nat (ZMod p)) (src : DenseRpSrc p)
    (x : VarId) (k : ZMod p) : Option (DenseRPSeen p) :=
  let g := ops.mul ((inv[k.val]?).getD k⁻¹) src.δ
  let gv := g.val
  let gc := p - gv
  if 256 ≤ gv && 256 ≤ gc then
    some ⟨src, x, k, denseRpBucketHash k src.aconst src.δ (src.tsum - denseRpTermHash x k), gv, gc⟩
  else none

/-- The candidate records of one constraint that survive the root-gap test. -/
def denseRpGroupOf (ops : DenseZModOps p) (inv : Std.HashMap Nat (ZMod p)) (src : DenseRpSrc p) :
    List (VarId × ZMod p) → List (DenseRPSeen p)
  | [] => []
  | (v, k) :: rest =>
    match denseRpCandAt ops inv src v k with
    | some e => e :: denseRpGroupOf ops inv src rest
    | none => denseRpGroupOf ops inv src rest

/-- The nonempty candidate groups, in source order. -/
def denseRpGroupsOf (ops : DenseZModOps p) (inv : Std.HashMap Nat (ZMod p)) :
    List (DenseRpPre p) → List (List (DenseRPSeen p))
  | [] => []
  | pre :: rest =>
    match denseRpGroupOf ops inv pre.src pre.cands with
    | [] => denseRpGroupsOf ops inv rest
    | g => g :: denseRpGroupsOf ops inv rest

/-- Every constraint's two-root candidates, grouped by constraint, in source order. -/
def denseRpGroups (ops : DenseZModOps p) (cs : List (DenseExpr p)) :
    List (List (DenseRPSeen p)) :=
  let pres := denseRpPres ops cs
  denseRpGroupsOf ops (denseRpInvTable pres) pres

/-- Hash of the part of a key shared by a whole group: a pair match needs equal `A.const` and equal
    `δ`, i.e. equal factor constants. -/
def denseRpSigHash (e : DenseRPSeen p) : UInt64 :=
  mixHash (hash e.src.aconst.val) (hash e.src.δ.val)

/-- How many groups carry each signature. -/
def denseRpSigCounts (gs : List (List (DenseRPSeen p))) : Std.HashMap UInt64 Nat :=
  gs.foldl (fun m g =>
    match g with
    | [] => m
    | e :: _ => let s := denseRpSigHash e; m.insert s (m.getD s 0 + 1)) ∅

/-- Drop the groups whose signature no other group shares: they can match nothing, so bucketing and
    scanning them is pure cost (two candidates of the same group never pair — the scan only looks at
    earlier constraints). -/
def denseRpLiveGroups (gs : List (List (DenseRPSeen p))) : List (List (DenseRPSeen p)) :=
  let counts := denseRpSigCounts gs
  gs.filter (fun g =>
    match g with
    | [] => false
    | e :: _ => 2 ≤ counts.getD (denseRpSigHash e) 0)

/-! ## The scan and the pass (dense) -/

/-- Prepend seen-entries into their bucket, preserving per-bucket insertion order. -/
def denseRpInsertAll (m : Std.HashMap UInt64 (List (DenseRPSeen p)))
    (es : List (DenseRPSeen p)) : Std.HashMap UInt64 (List (DenseRPSeen p)) :=
  es.foldr (fun e acc => acc.insert e.h (e :: acc.getD e.h [])) m

/-- Whether two candidates carry the same key `(k, A.terms, A.const, δ)`. -/
def denseRpKeyEq (e cand : DenseRPSeen p) : Bool :=
  e.k.val == cand.k.val && e.src.aconst.val == cand.src.aconst.val &&
    e.src.δ.val == cand.src.δ.val && denseRpSkipEq e.src.terms e.x cand.src.terms cand.x

/-- The certificate's bound clause, on the candidates' own gap. It is a necessary condition of
    `denseRpCheckPairB`, so gating on it cannot accept a pair the certificate rejects — and it
    rejects a same-key non-twin for two bound lookups instead of two two-root re-derivations. -/
def denseRpBoundGate (bnd : VarId → Option Nat) (e cand : DenseRPSeen p) : Bool :=
  match bnd e.x, bnd cand.x with
  | some Bx, some By => decide (max Bx By ≤ cand.gval) && decide (max Bx By ≤ cand.gco)
  | _, _ => false

/-- Scan the candidate groups in source order: for each candidate, look for an earlier twin with the
    same key whose pair certificate passes, and adopt the entailed equality into the solution map. -/
def denseRpScan (bnd : VarId → Option Nat) :
    List (List (DenseRPSeen p)) → Std.HashMap UInt64 (List (DenseRPSeen p)) → DenseSolved p →
      DenseSolved p
  | [], _, σ => σ
  | g :: rest, seen, σ =>
    match g.findSome? (fun cand =>
        (seen.getD cand.h []).findSome? (fun e =>
          if denseRpKeyEq e cand && !(e.x.index == cand.x.index) &&
              denseRpBoundGate bnd e cand &&
              denseRpCheckPairB bnd e.c cand.c e.x cand.x
          then some (e, cand.x) else none)) with
    | some ex =>
        denseRpScan bnd rest
          (denseRpInsertAll seen (g.filter (fun cand => !(cand.x.index == ex.2.index))))
          (σ.insertAll [(ex.2, DenseExpr.var ex.1.x)])
    | none => denseRpScan bnd rest (denseRpInsertAll seen g) σ

/-- The solution map the scan adopts over a whole system. -/
def denseRpSigma (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseSolved p :=
  denseRpScan (denseAnyVarBound bs facts d.busInteractions d.algebraicConstraints)
    (denseRpLiveGroups (denseRpGroups denseZModOps d.algebraicConstraints)) ∅ DenseSolved.empty

/-- For twin constraints `(a+k·x)(a+δ+k·x)=0` and `(a+k·y)(a+δ+k·y)=0` — each pinning its variable
    to one of two roots a fixed gap `g = k⁻¹·δ` apart — when both variables are range-bounded below
    the gap they must land on the same root, so `x = y`; the pass substitutes `y := x` everywhere.
    Identity unless `p` is prime; each substitution is a bare variable, so degree never grows. -/
def denseRootPairUnifyF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseRpSigma bs facts d
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

/-! ## Indexed bound lookups (runtime twins)

`denseAnyVarBound` is queried per candidate pair with the *full* interaction and constraint lists:
`denseFindVarBound` walks every interaction, and on failure `denseScaledSlotBound` walks every
interaction again, resolving finite domains with an O(constraints) `denseFindDomainAlg` scan per
offset variable. The twins below serve the same queries from a per-variable interaction index and
a tabulated first-yield domain map, both built once per pass invocation.
`denseRootPairUnifyF_eq_fast` (`Proofs/RootPairUnify.lean`) proves the pass equal and installs it
via `@[csimp]`. -/

/-- One tabulation step: record `c`'s root domain for `v` unless an earlier constraint already
    yielded one. -/
def denseDomStep (c : DenseExpr p) (m : Std.HashMap VarId (List (ZMod p))) (v : VarId) :
    Std.HashMap VarId (List (ZMod p)) :=
  if m.contains v then m
  else match denseRootsIn v c with
    | some d => m.insert v d
    | none => m

/-- `denseFindDomainAlg all` tabulated for every variable by one in-order sweep; insert-if-absent
    keeps the first yielding constraint, matching the scan's first-hit semantics. -/
def denseFindDomainMap (all : List (DenseExpr p)) : Std.HashMap VarId (List (ZMod p)) :=
  all.foldl (fun m c =>
    (HashedDedup.hashedEraseDups (hash ·) c.vars).foldl (denseDomStep c) m) ∅

/-- `denseScaledSlotBound` with the offset variables' domains served by `dom`. -/
def denseScaledSlotBoundD (bs : BusSemantics p) (facts : BusFacts p bs)
    (dom : VarId → Option (List (ZMod p))) (bi : BusInteraction (DenseExpr p)) (x : VarId) :
    Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none else
    (List.range bi.payload.length).findSome? (fun slot =>
      match bi.payload[slot]? with
      | none => none
      | some O =>
        match facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot with
        | none => none
        | some bound =>
          match O.splitAt x with
          | none => none
          | some (k, R) =>
            let m := k⁻¹
            let others := R.vars.eraseDups
            let doms := others.filterMap (fun v => (dom v).map (fun d => (v, d)))
            if k * m = 1 ∧ doms.map Prod.fst = others ∧
                (doms.map (fun vd => vd.2.length)).prod ≤ 16 then
              if m.val * (bound - 1) + ((denseAssignments doms).map
                    (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 < p then
                some (m.val * (bound - 1) + ((denseAssignments doms).map
                  (fun pt => ((-m) * R.eval (denseEnvOfFast pt)).val)).foldl max 0 + 1)
              else none
            else none)

/-- `denseAnyVarBound` served from the per-variable index `witsOf` and the domain lookup `dom`. -/
def denseAnyVarBoundIdx (bs : BusSemantics p) (facts : BusFacts p bs)
    (witsOf : VarId → List (BusInteraction (DenseExpr p)))
    (dom : VarId → Option (List (ZMod p))) (x : VarId) : Option Nat :=
  match denseFindVarBound bs facts (witsOf x) x with
  | some B => some B
  | none => (witsOf x).findSome? (fun bi => denseScaledSlotBoundD bs facts dom bi x)

/-- `denseRootPairUnifyF` with the per-variable interaction index and the tabulated domain map. -/
def denseRootPairUnifyFFast (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    -- Thunked: bound queries only happen on key-matched candidate pairs, so systems without
    -- two-root twins never pay for the index builds.
    let witsIdx : Thunk (Std.HashMap VarId (List (BusInteraction (DenseExpr p)))) :=
      Thunk.mk fun _ => denseVarBucket denseBIVars d.busInteractions
    let domMap : Thunk (Std.HashMap VarId (List (ZMod p))) :=
      Thunk.mk fun _ => denseFindDomainMap d.algebraicConstraints
    let bndIdx : VarId → Option Nat := fun x =>
      denseAnyVarBoundIdx bs facts (fun v => denseVarBucketLookup witsIdx.get v)
        (fun v => (domMap.get)[v]?) x
    let gs := denseRpLiveGroups (denseRpGroups denseZModOps d.algebraicConstraints)
    let σ := denseRpScan bndIdx gs ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

def denseRootPairUnifyFHints (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : RecoveryMap p :=
  if pw.isPrime = true then
    let σ := denseRpSigma bs facts d
    if σ.map.isEmpty then .identity else .ofFn (substitutionHints σ.fn)
  else .identity

end ApcOptimizer.Dense
