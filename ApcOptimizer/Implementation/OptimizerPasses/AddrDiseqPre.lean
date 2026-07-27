import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Prepared address-disequality certificates

The disequality certificates (`AddrDiseq.lean`) re-derive the same per-interaction data — the
address slot's constant value, linear form, and two-root reductions — once per *compared pair*,
which made the region scans of `busPairCancel` and the mid re-verification of `busUnify`'s
`denseCheckPair` quadratic in interaction count. `DenseAddrPre` prepares that data once per
interaction (each field a memoizing `Thunk`, so untouched certificate arms stay unpaid); the `*P`
twins below read the prepared records, and their `*_eq` lemmas let call sites rewrite scan
hypotheses back to the original certificate forms. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Prepared per-address-slot data: the raw slot expression plus its lazily-computed constant
    value, linear form, and two-root reductions. -/
structure DenseSlotPre (p : ℕ) where
  expr : DenseExpr p
  cval : Thunk (Option (ZMod p))
  lin : Thunk (Option (DenseLinExpr p))
  reds : Thunk (List (DenseLinExpr p × DenseLinExpr p))

def denseSlotPrep (T : DenseTwoRootMap p) (e : DenseExpr p) : DenseSlotPre p :=
  ⟨e, Thunk.mk fun _ => e.constValue?, Thunk.mk fun _ => denseLinearize e,
   Thunk.mk fun _ => densePtrReductions T e⟩

/-- Prepared per-interaction address data relative to one memory-bus shape: the bus id, the
    multiplicity constant, and the prepared slot record at each of the shape's address fields. -/
structure DenseAddrPre (p : ℕ) where
  busId : Nat
  mult : Thunk (Option (ZMod p))
  slots : List (Option (DenseSlotPre p))

def denseAddrPrep (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bi : BusInteraction (DenseExpr p)) : DenseAddrPre p :=
  ⟨bi.busId, Thunk.mk fun _ => denseMultConst bi,
   shape.addressFields.map (fun slot => (bi.payload[slot]?).map (denseSlotPrep T))⟩

/-- The zipped prepared slot lists are the pairwise map over the shape's address fields. -/
theorem denseAddrPrep_slots_zip (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    ((denseAddrPrep shape T S).slots).zip ((denseAddrPrep shape T m).slots)
      = shape.addressFields.map (fun slot =>
          ((S.payload[slot]?).map (denseSlotPrep T), (m.payload[slot]?).map (denseSlotPrep T))) := by
  simp [denseAddrPrep, List.zip_map']

/-! ## The prepared certificate twins -/

def denseAddrConstsNeqP (a b : DenseAddrPre p) : Bool :=
  (a.slots.zip b.slots).any (fun s =>
    match s with
    | (some sa, some sb) =>
        (match sa.cval.get, sb.cval.get with
         | some c, some c' => decide (c ≠ c')
         | _, _ => false)
    | _ => false)

theorem denseAddrConstsNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrConstsNeqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrConstsNeq shape S m := by
  unfold denseAddrConstsNeqP denseAddrConstsNeq
  rw [denseAddrPrep_slots_zip, List.any_map]
  refine congrArg _ (funext fun slot => ?_)
  simp only [Function.comp_apply]
  cases S.payload[slot]? <;> cases m.payload[slot]? <;> rfl

def denseAddrConstsEqP (a b : DenseAddrPre p) : Bool :=
  (a.slots.zip b.slots).all (fun s =>
    match s with
    | (some sa, some sb) =>
        decide (sa.expr = sb.expr) ||
        (match sa.cval.get, sb.cval.get with
         | some c, some c' => c = c'
         | _, _ => false)
    | _ => false)

theorem denseAddrConstsEqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrConstsEqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrConstsEq shape S m := by
  unfold denseAddrConstsEqP denseAddrConstsEq
  rw [denseAddrPrep_slots_zip, List.all_map]
  refine congrArg _ (funext fun slot => ?_)
  simp only [Function.comp_apply]
  cases S.payload[slot]? <;> cases m.payload[slot]? <;> rfl

def denseAddrAffineNeqP (a b : DenseAddrPre p) : Bool :=
  (a.slots.zip b.slots).any (fun s =>
    match s with
    | (some sa, some sb) =>
        (match sa.lin.get, sb.lin.get with
         | some L, some L' => denseConstDiffNZ L L'
         | _, _ => false)
    | _ => false)

theorem denseAddrAffineNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrAffineNeqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrAffineNeq shape S m := by
  unfold denseAddrAffineNeqP denseAddrAffineNeq
  rw [denseAddrPrep_slots_zip, List.any_map]
  refine congrArg _ (funext fun slot => ?_)
  simp only [Function.comp_apply]
  cases S.payload[slot]? <;> cases m.payload[slot]? <;> rfl

def denseAddrTwoRootNeqP (a b : DenseAddrPre p) : Bool :=
  (a.slots.zip b.slots).any (fun s =>
    match s with
    | (some sa, some sb) =>
        sa.reds.get.any (fun red => sb.reds.get.any (fun red' =>
          denseConstDiffNZ red.1 red'.1 && denseConstDiffNZ red.1 red'.2 &&
          denseConstDiffNZ red.2 red'.1 && denseConstDiffNZ red.2 red'.2))
    | _ => false)

theorem denseAddrTwoRootNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseAddrTwoRootNeqP (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrTwoRootNeq shape T S m := by
  unfold denseAddrTwoRootNeqP denseAddrTwoRootNeq
  rw [denseAddrPrep_slots_zip, List.any_map]
  refine congrArg _ (funext fun slot => ?_)
  simp only [Function.comp_apply]
  cases S.payload[slot]? <;> cases m.payload[slot]? <;> rfl

/-- `denseDiffSumOver` over prepared slot pairs (same fold, linearizations read from the prep). -/
def denseDiffSumP : List (Option (DenseSlotPre p) × Option (DenseSlotPre p)) →
    Option (DenseLinExpr p)
  | [] => some ⟨0, []⟩
  | s :: fs =>
    match denseDiffSumP fs with
    | none => none
    | some acc =>
      match s with
      | (some sa, some sb) =>
        match sa.lin.get, sb.lin.get with
        | some lS, some lM => some ((lM.add (lS.scale (-1))).add acc)
        | _, _ => none
      | _ => none

theorem denseDiffSumP_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p)) :
    ∀ fs : List Nat,
      denseDiffSumP (fs.map (fun slot =>
          ((S.payload[slot]?).map (denseSlotPrep T), (m.payload[slot]?).map (denseSlotPrep T))))
        = denseDiffSumOver S m fs := by
  intro fs
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [List.map_cons, denseDiffSumP, ih, denseDiffSumOver]
      cases denseDiffSumOver S m fs
      · rfl
      · cases S.payload[f]? <;> cases m.payload[f]? <;> rfl

def denseAddrNonzeroNeqP (nw : DenseNonzeroWits p) (a b : DenseAddrPre p) : Bool :=
  (a.slots.zip b.slots).sublists.any (fun sub =>
    match denseDiffSumP sub with
    | some D => nw.wits.any (fun g =>
        denseIsZeroLin (D.add (g.scale (-1))) || denseIsZeroLin (D.add g))
    | none => false)

theorem denseAddrNonzeroNeqP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (S m : BusInteraction (DenseExpr p)) :
    denseAddrNonzeroNeqP nw (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = denseAddrNonzeroNeq shape nw S m := by
  unfold denseAddrNonzeroNeqP denseAddrNonzeroNeq
  rw [denseAddrPrep_slots_zip, List.sublists_map, List.any_map]
  refine congrArg _ (funext fun fs => ?_)
  simp only [Function.comp_apply]
  rw [denseDiffSumP_eq]
  rfl

/-! ## `busUnify`'s verifier on prepared records

`denseCheckPair` re-verifies each candidate's whole mid region; the compiled twin prepares the
candidate side once and each mid message once, so a mid message costs one preparation instead of
one certificate derivation per arm. -/

/-- `denseCheckPair`'s per-mid-message exclusion disjunction, on prepared records. -/
def denseMidExcludedP (nw : DenseNonzeroWits p) (preS prem : DenseAddrPre p) : Bool :=
  denseAddrConstsNeqP preS prem || denseAddrAffineNeqP preS prem
    || denseAddrTwoRootNeqP preS prem || denseAddrNonzeroNeqP nw preS prem
    || decide (prem.mult.get = some 0)

theorem denseMidExcludedP_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (S m : BusInteraction (DenseExpr p)) :
    denseMidExcludedP nw (denseAddrPrep shape T S) (denseAddrPrep shape T m)
      = (denseAddrConstsNeq shape S m || denseAddrAffineNeq shape S m
        || denseAddrTwoRootNeq shape T S m || denseAddrNonzeroNeq shape nw S m
        || decide (denseMultConst m = some 0)) := by
  unfold denseMidExcludedP
  rw [denseAddrConstsNeqP_eq, denseAddrAffineNeqP_eq, denseAddrTwoRootNeqP_eq,
    denseAddrNonzeroNeqP_eq]
  rfl

def denseCheckPairFast (shape : MemoryBusShape) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (S : BusInteraction (DenseExpr p))
    (mid : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p)) : Bool :=
  decide (denseMultConst S = some shape.setNewMult) &&
    decide (denseMultConst R = some (-shape.setNewMult)) &&
  denseAddrConstsEq shape S R &&
  (let preS := denseAddrPrep shape T S
   mid.all (fun m => denseMidExcludedP nw preS (denseAddrPrep shape T m)))

@[csimp] theorem denseCheckPair_eq_fast : @denseCheckPair = @denseCheckPairFast := by
  funext q shape T nw S mid R
  unfold denseCheckPair denseCheckPairFast
  congr 1
  exact (congrArg mid.all (funext fun m => denseMidExcludedP_eq shape T nw S m)).symm

end ApcOptimizer.Dense
