import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.DropPasses
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp

set_option autoImplicit false

/-! # Dense bounded-payload digit fold (runtime). Bounds map `denseBuild` proved sound in
`Proofs/DigitFold.lean`. -/

/-! ## ℕ-side ladder arithmetic and solution grid (representation-independent) -/

namespace DigitFold

/-! ### ℕ-side ladder arithmetic -/

/-- Little-endian base-256 positional value of a digit list. -/
def ladderVal : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 256 * ladderVal xs

/-- Decode `T` as `Bs.length` base-256 digits (little-endian) with exclusive digit bounds `Bs`,
    requiring the final quotient to vanish; `none` if any digit breaches its bound. -/
def unpack? : List ℕ → ℕ → Option (List ℕ)
  | [], T => if T = 0 then some [] else none
  | B :: Bs, T =>
    if T % 256 < B then (unpack? Bs (T / 256)).map (T % 256 :: ·) else none

/-- Decoding is a retraction of the positional value on bounded digit lists. -/
theorem unpack?_ladderVal : ∀ (xs Bs : List ℕ), List.Forall₂ (· < ·) xs Bs →
    (∀ B ∈ Bs, B ≤ 256) → unpack? Bs (ladderVal xs) = some xs := by
  intro xs Bs h
  induction h with
  | nil => intro _; rfl
  | @cons x B xs Bs hxB _ ih =>
    intro hB
    have hx256 : x < 256 := lt_of_lt_of_le hxB (hB B (by simp))
    have hmod : (x + 256 * ladderVal xs) % 256 = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx256]
    have hdiv : (x + 256 * ladderVal xs) / 256 = ladderVal xs := by
      rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256), Nat.div_eq_of_lt hx256, Nat.zero_add]
    simp only [ladderVal, unpack?, hmod, hdiv, if_pos hxB,
      ih (fun B hBmem => hB B (by simp [hBmem]))]
    rfl

/-- Positional value is monotone into the bound box. -/
theorem ladderVal_le_box : ∀ (xs Bs : List ℕ), List.Forall₂ (· < ·) xs Bs →
    ladderVal xs ≤ ladderVal (Bs.map (· - 1)) := by
  intro xs Bs h
  induction h with
  | nil => exact le_refl _
  | @cons x B xs Bs hxB _ ih =>
    simp only [ladderVal, List.map_cons]
    have hx : x ≤ B - 1 := Nat.le_sub_one_of_lt hxB
    exact Nat.add_le_add hx (Nat.mul_le_mul_left _ ih)

/-! ### The (byte, wrap) solution grid -/

/-- All digit vectors compatible with "the checked value is a byte": for each byte `b` and wrap
    count `m`, decode `tval b + m·p` as a `g`-scaled bounded ladder (`tval b` = the ℕ-residue the
    ladder sum must have when the byte reads `b`). -/
def solutions (p : ℕ) (tval : ℕ → ℕ) (g : ℕ) (Bs : List ℕ) (maxM : ℕ) : List (List ℕ) :=
  (List.range 256).flatMap fun b =>
    (List.range (maxM / p + 1)).filterMap fun m =>
      let M := tval b + m * p
      if M % g = 0 ∧ M ≤ maxM then unpack? Bs (M / g) else none

/-- Completeness of the grid: the digit vector of any assignment whose ladder sum `g·ladderVal xs`
    has residue `tval b` (for its byte value `b < 256`) and fits under `maxM` is enumerated. -/
theorem solutions_complete (p : ℕ) (tval : ℕ → ℕ) (g : ℕ) (Bs : List ℕ) (maxM : ℕ)
    (_hp : 0 < p) (hg : 0 < g)
    (xs : List ℕ) (hxB : List.Forall₂ (· < ·) xs Bs) (hB : ∀ B ∈ Bs, B ≤ 256)
    (b : ℕ) (hb : b < 256)
    (hmod : (g * ladderVal xs) % p = tval b) (hle : g * ladderVal xs ≤ maxM) :
    xs ∈ solutions p tval g Bs maxM := by
  set S := g * ladderVal xs with hS
  have hSsplit : tval b + S / p * p = S := by
    rw [← hmod, Nat.mod_add_div' S p]
  have hm : S / p < maxM / p + 1 :=
    Nat.lt_succ_of_le (Nat.div_le_div_right hle)
  refine List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, ?_⟩
  refine List.mem_filterMap.2 ⟨S / p, List.mem_range.2 hm, ?_⟩
  have hMg : S % g = 0 := by
    rw [hS]; exact Nat.mul_mod_right g _
  have hMdiv : S / g = ladderVal xs := by
    rw [hS]; exact Nat.mul_div_cancel_left _ hg
  rw [hSsplit, if_pos ⟨hMg, hle⟩, hMdiv]
  exact unpack?_ladderVal xs Bs hxB hB

/-- The payoff: a singleton grid forces the digit vector. -/
theorem solutions_forced (p : ℕ) (tval : ℕ → ℕ) (g : ℕ) (Bs : List ℕ) (maxM : ℕ)
    (hp : 0 < p) (hg : 0 < g) (ds : List ℕ)
    (hsol : solutions p tval g Bs maxM = [ds])
    (xs : List ℕ) (hxB : List.Forall₂ (· < ·) xs Bs) (hB : ∀ B ∈ Bs, B ≤ 256)
    (b : ℕ) (hb : b < 256)
    (hmod : (g * ladderVal xs) % p = tval b) (hle : g * ladderVal xs ≤ maxM) :
    xs = ds := by
  have := solutions_complete p tval g Bs maxM hp hg xs hxB hB b hb hmod hle
  rw [hsol, List.mem_singleton] at this
  exact this

variable {p : ℕ}

/-! ### Ladder recognition on linear forms (representation-independent coefficient layer) -/

/-- The ℕ-coefficient of a term under a sign interpretation: `c.val` when the ladder is added to
    the constant, `(-c).val` when it is subtracted. -/
def coeffNat (pos : Bool) (c : ZMod p) : ℕ := if pos then c.val else (-c).val

/-- The ladder's sign as a field element. -/
def signum (pos : Bool) : ZMod p := if pos then 1 else -1

@[simp] theorem signum_true : (signum true : ZMod p) = 1 := rfl
@[simp] theorem signum_false : (signum false : ZMod p) = -1 := rfl

/-- The ℕ-residue the ladder sum must have when the byte-checked value reads `b`. -/
def tval (pos : Bool) (K : ZMod p) (b : ℕ) : ℕ :=
  (if pos then (b : ZMod p) - K else K - (b : ZMod p)).val

end DigitFold

namespace ApcOptimizer.Dense

open DigitFold

variable {p : ℕ}

/-! ## Per-interaction bound machinery -/

def denseIsVarOf (i : VarId) : DenseExpr p → Bool
  | .var j => j = i
  | _ => false

/-- The first payload slot index literally `.var i`. -/
def denseVarSlot (i : VarId) : List (DenseExpr p) → Option Nat
  | [] => none
  | e :: rest => if denseIsVarOf i e then some 0 else (denseVarSlot i rest).map (· + 1)

/-- `denseInteractionBound` with the `mval = 0` test taken on `ZMod.val`, which needs no
    `CommRing (ZMod p)` dictionary. -/
def denseInteractionBoundImpl (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) : Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval.val = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot

/-- One value bound for `i` from a constant-nonzero-multiplicity interaction carrying `.var i`
    in a fact-bounded raw payload slot. -/
def denseInteractionBound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) : Option Nat :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) slot

@[csimp] theorem denseInteractionBound_eq_impl :
    @denseInteractionBound = @denseInteractionBoundImpl := by
  funext q bs facts bi i
  simp [denseInteractionBound, denseInteractionBoundImpl]

/-- Probe payload: constant slots at their constants, slot `i` at the candidate, others `0`. -/
def denseProbeBase (payload : List (DenseExpr p)) (i : Nat) (v : ZMod p) : List (ZMod p) :=
  (payload.map (fun e => (DenseExpr.constValue? e).getD 0)).set i v

/-- A probed value bound for `i`. -/
def denseProbedSlotBoundAt (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (j : Nat) : Option Nat :=
  if p = 0 then none
  else
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some s =>
        if s = j then none
        else
          match facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) s with
          | none => none
          | some B₀ =>
            if 256 < B₀ then none
            else
              match facts.slotFun bi.busId (bi.payload.map DenseExpr.constValue?) j with
              | none => none
              | some f =>
                match bi.payload[j]? with
                | none => none
                | some e =>
                  match denseLinearize e with
                  | none => none
                  | some l =>
                    match l.terms with
                    | [(y, c)] =>
                      if y = i ∧ (List.range bi.payload.length).all (fun k =>
                          k == s || k == j ||
                            ((bi.payload[k]?.map
                              (fun e' => (DenseExpr.constValue? e').isSome)).getD false)) then
                        capBound (probeMax (fun v =>
                          f ((denseProbeBase bi.payload s ((v : ℕ) : ZMod p)).set j 0)
                            == l.const + c * ((v : ℕ) : ZMod p)) B₀) B₀
                      else none
                    | _ => none

/-! ## Dense bounds map (`Std.HashMap VarId Nat`); soundness in `Proofs/DigitFold.lean`.

Everything an interaction's bound derivations need that does not depend on the payload variable —
the constant multiplicity, the payload's constant pattern, the pattern's non-constant slot indices
and the probe payload's constant base — is derived once per interaction into a `DenseBiPrep` and
threaded down, instead of being re-derived once per raw variable (and, for the probe base, once per
probed value). The soundness proof only constrains *which* bounds are inserted
(`denseSlotBoundAt_eq`, `denseProbedSlotBoundAtP_eq`), never how the candidates are enumerated. -/

/-- Keep the smaller of two bounds for `i`. -/
def denseInsertEntry (T : Std.HashMap VarId Nat) (i : VarId) (b : Nat) : Std.HashMap VarId Nat :=
  let keep : Bool := match T[i]? with
    | some b0 => decide (b < b0)
    | none => true
  if keep then T.insert i b else T

/-- The raw-variable payload entries. -/
def denseRawVarsOf (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.payload.filterMap (fun e => match e with | .var i => some i | _ => none)

/-- Payload slots whose affine form is a single term, as `(variable, slot)` from `j` on, with
    `seen` the variables of the earlier raw slots.

    A `.var` or `.const` slot is decided by shape, so the linearization runs only on compound slots.
    A `.var y` slot at `y`'s *first* occurrence is dropped: the probe looks the bound up at
    `denseVarSlot y`, which is then this very slot, and `denseProbedSlotBoundAtP` rejects `s = j`.
    Candidates are unconstrained by soundness — dropping one can only lose a bound, and this one
    was never derivable. -/
def denseProbeCandsGo (seen : List VarId) (j : Nat) :
    List (DenseExpr p) → List (VarId × Nat)
  | [] => []
  | e :: rest =>
    match e with
    | .var y =>
      if seen.any (fun v => v == y) then (y, j) :: denseProbeCandsGo (y :: seen) (j + 1) rest
      else denseProbeCandsGo (y :: seen) (j + 1) rest
    | .const _ => denseProbeCandsGo seen (j + 1) rest
    | _ =>
      match denseLinearize e with
      | some l =>
        match l.terms with
        | [(y, _)] => (y, j) :: denseProbeCandsGo seen (j + 1) rest
        | _ => denseProbeCandsGo seen (j + 1) rest
      | none => denseProbeCandsGo seen (j + 1) rest

/-- The probed-bound candidate `(VarId, slot)` pairs. -/
def denseProbeCandidatesOf (bi : BusInteraction (DenseExpr p)) : List (VarId × Nat) :=
  if (bi.multiplicity.constValue?).isSome then denseProbeCandsGo [] 0 bi.payload else []

/-- The per-interaction values the bound derivations would otherwise re-derive per payload
    variable. Nothing is derived when the multiplicity is not constant: every bound below then
    returns `none` regardless of the payload, and that is the common case in the first cleanup
    cycle. -/
structure DenseBiPrep (p : ℕ) where
  mval? : Option (ZMod p)
  pat : List (Option (ZMod p))
  cands : List (VarId × Nat)

def denseBiPrepOf (bi : BusInteraction (DenseExpr p)) : DenseBiPrep p :=
  match bi.multiplicity.constValue? with
  | none => ⟨none, [], []⟩
  | some mval =>
    ⟨some mval, bi.payload.map DenseExpr.constValue?, denseProbeCandsGo [] 0 bi.payload⟩

/-- `denseInteractionBound` with the per-interaction values and the variable's payload slot hoisted
    out of the caller's loop; `denseSlotBoundAt_eq` is the equality at the canonical arguments. -/
def denseSlotBoundAt (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (mval? : Option (ZMod p)) (pat : List (Option (ZMod p)))
    (slot? : Option Nat) : Option Nat :=
  match mval? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match slot? with
      | none => none
      | some slot => facts.slotBound bi.busId mval pat slot

def denseSlotBoundAtImpl (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (mval? : Option (ZMod p)) (pat : List (Option (ZMod p)))
    (slot? : Option Nat) : Option Nat :=
  match mval? with
  | none => none
  | some mval =>
    if zmodIsZero mval then none
    else
      match slot? with
      | none => none
      | some slot => facts.slotBound bi.busId mval pat slot

@[csimp] theorem denseSlotBoundAt_eq_impl : @denseSlotBoundAt = @denseSlotBoundAtImpl := by
  funext q bs facts bi m pat s
  simp [denseSlotBoundAt, denseSlotBoundAtImpl]

/-- `denseProbedSlotBoundAt` on the hoisted per-interaction values (the constant multiplicity and
    payload pattern) and the variable's payload slot; `denseProbedSlotBoundAtP_eq` is the equality
    at the canonical arguments. Everything past the two `facts` lookups is left as the original
    computes it: dropping the barren `.var`-at-first-slot candidates leaves almost no probe reaching
    that far (keccak cycle 1: 24 630 probe calls → 1), so hoisting there buys nothing. -/
def denseProbedSlotBoundAtP (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (pr : DenseBiPrep p) (i : VarId) (slot? : Option Nat)
    (j : Nat) : Option Nat :=
  if p = 0 then none
  else
  match pr.mval? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match slot? with
      | none => none
      | some s =>
        if s = j then none
        else
          match facts.slotBound bi.busId mval pr.pat s with
          | none => none
          | some B₀ =>
            if 256 < B₀ then none
            else
              match facts.slotFun bi.busId pr.pat j with
              | none => none
              | some f =>
                match bi.payload[j]? with
                | none => none
                | some e =>
                  match denseLinearize e with
                  | none => none
                  | some l =>
                    match l.terms with
                    | [(y, c)] =>
                      if y = i ∧ (List.range bi.payload.length).all (fun k =>
                          k == s || k == j ||
                            ((bi.payload[k]?.map
                              (fun e' => (DenseExpr.constValue? e').isSome)).getD false)) then
                        capBound (probeMax (fun v =>
                          f ((denseProbeBase bi.payload s ((v : ℕ) : ZMod p)).set j 0)
                            == l.const + c * ((v : ℕ) : ZMod p)) B₀) B₀
                      else none
                    | _ => none

/-- For candidate `(y, j)`s matching `i`, insert the probed bound. -/
def denseGoCands (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (pr : DenseBiPrep p) (i : VarId) (slot? : Option Nat) :
    List (VarId × Nat) → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | (y, j) :: cl, T =>
    if y = i then
      match denseProbedSlotBoundAtP bs facts bi pr i slot? j with
      | some b => denseGoCands bs facts bi pr i slot? cl (denseInsertEntry T i b)
      | none => denseGoCands bs facts bi pr i slot? cl T
    else denseGoCands bs facts bi pr i slot? cl T

/-- For each raw variable `i`, insert its interaction bound then its probed bounds. Its payload
    slot is resolved once and shared by both. -/
def denseAddVars (bs : BusSemantics p) (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (pr : DenseBiPrep p) :
    List VarId → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | i :: xs, T =>
    let slot? := denseVarSlot i bi.payload
    let T1 := match denseSlotBoundAt bs facts bi pr.mval? pr.pat slot? with
      | some b => denseInsertEntry T i b
      | none => T
    denseAddVars bs facts bi pr xs (denseGoCands bs facts bi pr i slot? pr.cands T1)

/-- The raw-variable payload entries a build is asked to bound; `none` asks for all of them. -/
def denseKeptRawVars (keep? : Option (Std.HashSet VarId)) (bi : BusInteraction (DenseExpr p)) :
    List VarId :=
  match keep? with
  | none => denseRawVarsOf bi
  | some keep => (denseRawVarsOf bi).filter (fun i => keep.contains i)

/-- Collect bounds from every interaction's fact-bounded raw payload slots, for the variables
    `keep?` asks for. An interaction contributing none pays no `denseBiPrepOf` (with its
    compound-slot linearizations) and no `facts` call.

    Restricting the keys does not change the bound stored for a key that is kept: every insertion
    for `i` happens on `i`'s own iteration, `denseInsertEntry` keeps the tightest of them, and the
    minimum for one key is independent of every other. -/
def denseAddAllWith (bs : BusSemantics p) (facts : BusFacts p bs)
    (keep? : Option (Std.HashSet VarId)) :
    List (BusInteraction (DenseExpr p)) → Std.HashMap VarId Nat → Std.HashMap VarId Nat
  | [], T => T
  | bi :: rest, T =>
    match denseKeptRawVars keep? bi with
    | [] => denseAddAllWith bs facts keep? rest T
    | vs => denseAddAllWith bs facts keep? rest (denseAddVars bs facts bi (denseBiPrepOf bi) vs T)

def denseAddAll (bs : BusSemantics p) (facts : BusFacts p bs)
    (dbis : List (BusInteraction (DenseExpr p))) (T : Std.HashMap VarId Nat) :
    Std.HashMap VarId Nat :=
  denseAddAllWith bs facts none dbis T

def denseBuildWith (bs : BusSemantics p) (facts : BusFacts p bs)
    (keep? : Option (Std.HashSet VarId)) (dbis : List (BusInteraction (DenseExpr p))) :
    Std.HashMap VarId Nat :=
  denseAddAllWith bs facts keep? dbis ∅

/-- Dense bounds-map build. -/
def denseBuild (bs : BusSemantics p) (facts : BusFacts p bs)
    (dbis : List (BusInteraction (DenseExpr p))) : Std.HashMap VarId Nat :=
  denseBuildWith bs facts none dbis

/-! ## Dense byte-pair recognizer -/

/-- Dense byte-pair-check recognizer: a `pairOp`/`result 0`/`mult 1` check on a `byteXorSpec` bus. -/
def densePairByteOps? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | some (op, o1, o2, _r) =>
      if spec.bound = 256 ∧ op = DenseExpr.const spec.pairOp ∧ _r = DenseExpr.const 0
          ∧ bi.multiplicity = DenseExpr.const 1
      then some (o1, o2) else none
    | none => none

/-- Dictionary-free twin: same structure, literals tested without the `ZMod.commRing` chain that
    `DenseExpr.const 0`/`1` put at this recognizer's entry. -/
def densePairByteOpsImpl? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (DenseExpr p × DenseExpr p) :=
  match facts.byteXorSpec bi.busId with
  | none => none
  | some spec =>
    match spec.decode bi.payload with
    | some (op, o1, o2, _r) =>
      if spec.bound = 256 ∧ op = DenseExpr.const spec.pairOp ∧ _r.isConstZero = true
          ∧ bi.multiplicity.isConstOne = true
      then some (o1, o2) else none
    | none => none

@[csimp] theorem densePairByteOps_eq_impl : @densePairByteOps? = @densePairByteOpsImpl? := by
  funext q bs facts bi
  simp only [densePairByteOps?, densePairByteOpsImpl?, DenseExpr.isConstOne_eq_decide,
    DenseExpr.isConstZero_eq_decide, decide_eq_true_eq]

/-! ## The fold plan: the ladder forms to solve and the keys they will query -/

/-- One operand's contribution: its ladder form (in reverse scan order) and its variables, when
    `denseSolveOperand` would attempt it — a successful linearization with at least two terms. -/
def denseFoldOperand (E : DenseExpr p) (acc : List (DenseLinExpr p) × Std.HashSet VarId) :
    List (DenseLinExpr p) × Std.HashSet VarId :=
  match denseLinearize E with
  | none => acc
  | some l =>
    if l.terms.length < 2 then acc
    else (l :: acc.1, l.terms.foldl (fun s t => s.insert t.1) acc.2)

def denseFoldPlanGo (bs : BusSemantics p) (facts : BusFacts p bs) :
    List (BusInteraction (DenseExpr p)) → List (DenseLinExpr p) × Std.HashSet VarId →
      List (DenseLinExpr p) × Std.HashSet VarId
  | [], acc => acc
  | bi :: rest, acc =>
    match densePairByteOps? bs facts bi with
    | none => denseFoldPlanGo bs facts rest acc
    | some (x, y) => denseFoldPlanGo bs facts rest (denseFoldOperand y (denseFoldOperand x acc))

/-- The ladder forms of every recognized byte-pair check's operands, in scan order (interaction
    order, first operand before second), paired with all their variables — which is exactly the set
    of keys the solve can look a bound up for. Recognition and linearization happen here only; the
    solve consumes the forms (`denseSolveLadders`) and the bounds map is built for the keys
    (`denseBuildWith`). -/
def denseFoldPlan (bs : BusSemantics p) (facts : BusFacts p bs)
    (dbis : List (BusInteraction (DenseExpr p))) : List (DenseLinExpr p) × Std.HashSet VarId :=
  let acc := denseFoldPlanGo bs facts dbis ([], ∅)
  (acc.1.reverse, acc.2)

/-! ## Dense ladder recognition and grid solving -/

/-- Dense ladder-shape check (coefficient-only, so `VarId`-agnostic). -/
def denseIsLadder (pos : Bool) : ℕ → List (VarId × ZMod p) → Bool
  | _, [] => true
  | n, (_, c) :: rest => coeffNat pos c == n && denseIsLadder pos (256 * n) rest

/-- Dense ladder recognition: sort by sign-interpreted coefficient, check the shape. -/
def denseTryLadder (pos : Bool) (terms : List (VarId × ZMod p)) :
    Option (ℕ × List (VarId × ZMod p)) :=
  match terms.mergeSort (fun a b => coeffNat pos a.2 ≤ coeffNat pos b.2) with
  | [] => none
  | t :: rest =>
    if 0 < coeffNat pos t.2 ∧ denseIsLadder pos (coeffNat pos t.2) (t :: rest) = true
    then some (coeffNat pos t.2, t :: rest) else none

/-- Dense fact-bound lookup for a ladder's variables, in order. -/
def denseLookupBounds (bounds : Std.HashMap VarId Nat) :
    List (VarId × ZMod p) → Option (List ℕ)
  | [] => some []
  | (v, _) :: rest =>
    match bounds[v]? with
    | some B => if B ≤ 256 then (denseLookupBounds bounds rest).map (B :: ·) else none
    | none => none

/-- Dense one-sign ladder attempt: recognise, bound, enumerate, force a singleton digit vector. -/
def denseAttemptLadder (pos : Bool) (bounds : Std.HashMap VarId Nat) (l : DenseLinExpr p) :
    Option (VarId × ℕ) :=
  match denseTryLadder pos l.terms with
  | none => none
  | some gs =>
    match denseLookupBounds bounds gs.2 with
    | none => none
    | some Bs =>
      match solutions p (tval pos l.const) gs.1 Bs (gs.1 * ladderVal (Bs.map (· - 1))) with
      | [_ds] =>
        match gs.2, _ds with
        | t :: _, d :: _ => some (t.1, d)
        | _, _ => none
      | _ => none

/-- Dense operand solver: linearize, require ≥2 ladder digits, try both sign interpretations. -/
def denseSolveOperand (bounds : Std.HashMap VarId Nat) (E : DenseExpr p) : Option (VarId × ℕ) :=
  match denseLinearize E with
  | none => none
  | some l =>
    if l.terms.length < 2 then none
    else
      match denseAttemptLadder true bounds l with
      | some r => some r
      | none => denseAttemptLadder false bounds l

/-! ## Dense scan for a forced digit and the pass -/

/-- Dense scan for the first byte-checked ladder operand with a forced digit. -/
def denseFindFold (bs : BusSemantics p) (facts : BusFacts p bs) (denseBM : Std.HashMap VarId Nat) :
    List (BusInteraction (DenseExpr p)) → Option (VarId × ℕ)
  | [] => none
  | bi :: rest =>
    match densePairByteOps? bs facts bi with
    | none => denseFindFold bs facts denseBM rest
    | some (x, y) =>
      match denseSolveOperand denseBM x with
      | some r => some r
      | none =>
        match denseSolveOperand denseBM y with
        | some r => some r
        | none => denseFindFold bs facts denseBM rest

/-- First planned ladder form with a forced digit, both sign interpretations in
    `denseSolveOperand`'s order. Reads nothing but `bounds` and the form. -/
def denseSolveLadders (bounds : Std.HashMap VarId Nat) :
    List (DenseLinExpr p) → Option (VarId × ℕ)
  | [] => none
  | l :: rest =>
    match denseAttemptLadder true bounds l with
    | some r => some r
    | none =>
      match denseAttemptLadder false bounds l with
      | some r => some r
      | none => denseSolveLadders bounds rest

/-- The planned scan: recognize and linearize the byte-pair operands once, bound only the keys those
    forms can query, then solve the forms in scan order. `denseSolveLadders_eq_findFold` in
    `Proofs/DigitFold.lean` is the equality with the interaction scan `denseFindFold`.

    No ladder form means no lookup, so the bounds map is not built at all — the common case. -/
def denseDigitFoldFind (bs : BusSemantics p) (facts : BusFacts p bs)
    (dbis : List (BusInteraction (DenseExpr p))) : Option (VarId × ℕ) :=
  let plan := denseFoldPlan bs facts dbis
  if plan.1.isEmpty then none
  else denseSolveLadders (denseBuildWith bs facts (some plan.2) dbis) plan.1

/-- Digit-fold transform: when a witness limb is forced to a compile-time constant by a byte check
    over a base-256 ladder (e.g. a limb pinned to `7`), substitute it away. One forced digit per
    invocation; identity if none found. -/
def denseDigitFoldF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if 256 < p then
    match denseDigitFoldFind bs facts d.busInteractions with
    | some (i, dd) => d.subst i (DenseExpr.const (dd : ZMod p))
    | none => d
  else d

def denseDigitFoldHints (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    RecoveryMap p :=
  if 256 < p then
    match denseDigitFoldFind bs facts d.busInteractions with
    | some (i, dd) => ⟨substitutionHints (fun j => if j = i then some (.const (dd : ZMod p)) else none)⟩
    | none => ⟨WitnessExpr.var⟩
  else ⟨WitnessExpr.var⟩

end ApcOptimizer.Dense
