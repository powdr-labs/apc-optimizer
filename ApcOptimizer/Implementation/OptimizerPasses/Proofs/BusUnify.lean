import ApcOptimizer.Implementation.OptimizerPasses.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.AddrDiseq
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.MemoryBusDrop
import ApcOptimizer.Implementation.MemoryBusMultiset

set_option autoImplicit false

/-! # Soundness for the dense `busUnify` pass

`DensePassCorrect` for `denseBusUnifyF` (`BusUnify.lean`), lifted through `DenseVerifiedPassW.of`.
`busUnify` only adds constraints, so soundness is a constraint superset
(`DensePassCorrect.denseAddConstraints`); the substance is real-trace completeness — every
admissible satisfying assignment already fulfils the added slot equalities. The justification is
*order-free*: `denseBUGroupPairs?_sound` assembles the verifier's certificates into the
hypotheses of `admissibleMemoryBusM_copies_of_ts` (`Implementation/MemoryBusMultiset.lean`) —
fiber presentations from the classification split, send-timestamp structure from the shared
linear base, and the per-access LessThan bound from the solved gadget plus the TS_BOUND rely
(`facts.memTsField_sound`).

The constant-address (dis)equality certificates near the top are also consumed by other pass
proofs (`Proofs/XorEqExtract.lean`, `Proofs/BusPairCancelIndex.lean`,
`Proofs/BusPairCancelCheck.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Small value-level helpers -/

/-- A dense constant-folded expression evaluates to its recognized constant. -/
theorem denseConstValueEval (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  grind [DenseExpr.constValue?, DenseExpr.eval]

/-- `denseEqExpr e₂ e₁` evaluates to `e₂ − e₁`. -/
theorem denseEqExpr_eval (e2 e1 : DenseExpr p) (denv : VarId → ZMod p) :
    (denseEqExpr e2 e1).eval denv = e2.eval denv - e1.eval denv := by
  show e2.eval denv + (-1) * e1.eval denv = _
  ring

/-- Both entries of equal-under-`denv` payloads evaluate equally. -/
theorem densePayloadSlot_eval_eq (P Q : List (DenseExpr p)) (denv : VarId → ZMod p)
    (h : P.map (fun e => e.eval denv) = Q.map (fun e => e.eval denv)) (i : Nat) :
    ((P[i]?).getD (.const 0)).eval denv = ((Q[i]?).getD (.const 0)).eval denv := by
  have hi := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map] at hi
  cases hP : P[i]? <;> cases hQ : Q[i]? <;> rw [hP, hQ] at hi <;> simp_all

/-! ## The constant-address (dis)equality certificates -/

theorem denseAddrConstsEq_sound (shape : MemoryBusShape) (S S' : BusInteraction (DenseExpr p))
    (h : denseAddrConstsEq shape S S' = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) = shape.address (denseBIEval S' denv) := by
  unfold MemoryBusShape.address
  apply List.map_congr_left
  intro slot hslot
  have hs := List.all_eq_true.mp h slot hslot
  show (S.payload.map (fun e => e.eval denv))[slot]?
    = (S'.payload.map (fun e => e.eval denv))[slot]?
  grind [denseConstValueEval]

theorem denseAddrConstsNeq_sound (shape : MemoryBusShape) (S bi : BusInteraction (DenseExpr p))
    (h : denseAddrConstsNeq shape S bi = true) (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval bi denv) := by
  grind [denseAddrConstsNeq, denseConstValueEval, denseAddr_slot_neq]

/-! ## The load-bearing fact plumbing -/

/-- Filtering evaluated dense messages by bus id equals evaluating the bus-filtered interactions
    (`denseBIEval` preserves `busId`). -/
theorem dense_map_eval_filter_busId (l : List (BusInteraction (DenseExpr p))) (busId : Nat)
    (denv : VarId → ZMod p) :
    (l.map (fun bi => denseBIEval bi denv)).filter (fun m => m.busId = busId)
    = (l.filter (fun bi => bi.busId = busId)).map (fun bi => denseBIEval bi denv) := by
  induction l with
  | nil => rfl
  | cons bi rest ih =>
    have hbid : (denseBIEval bi denv).busId = bi.busId := rfl
    simp only [List.map_cons, List.filter_cons, hbid]
    by_cases h : bi.busId = busId
    · simp [h, ih]
    · simp [h, ih]

/-- Every var of an entailed slot equality comes from the send's or receive's payload. -/
theorem denseMemEqConstraints_vars (shape : MemoryBusShape) (S Rt : BusInteraction (DenseExpr p))
    {c : DenseExpr p} (hc : c ∈ denseMemEqConstraints shape S Rt) {z : VarId} (hz : z ∈ c.vars) :
    (∃ e ∈ Rt.payload, z ∈ e.vars) ∨ (∃ e ∈ S.payload, z ∈ e.vars) := by
  grind [denseMemEqConstraints, denseEqExpr, DenseExpr.vars, List.mem_of_getElem?]

/-- A var of a bus interaction's payload occurs in `d`. -/
theorem DenseConstraintSystem.mem_occ_of_payload {d : DenseConstraintSystem p}
    {bi : BusInteraction (DenseExpr p)} {e : DenseExpr p} {z : VarId}
    (hbi : bi ∈ d.busInteractions) (he : e ∈ bi.payload) (hz : z ∈ e.vars) : z ∈ d.occ :=
  DenseConstraintSystem.mem_occ_of_bi hbi (by
    simp only [denseBIVars, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨e, he, hz⟩)

/-! ## Prepared records: the slot-wise bridges

`denseBUPrep` stores, per address slot, exactly what the certificates of `AddrDiseq.lean` read
(`cval = constValue?`, `lin = denseLinearize`, `reds = densePtrReductions`), so the arms that keep
the original test are equal to it slot for slot. The affine and two-root arms are *not* — they
compare canonical term keys — and get their own semantic lemmas below. -/

theorem denseBUSlotsAny_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p))
    (f : DenseBUSlot p → DenseBUSlot p → Bool) (g : DenseExpr p → DenseExpr p → Bool)
    (hfg : ∀ e e', f (denseBUSlotPrep T e) (denseBUSlotPrep T e') = g e e') :
    ∀ fields : List Nat,
      denseBUSlotsAny f (fields.map (fun slot => (S.payload[slot]?).map (denseBUSlotPrep T)))
          (fields.map (fun slot => (m.payload[slot]?).map (denseBUSlotPrep T)))
        = fields.any (fun slot =>
            match S.payload[slot]?, m.payload[slot]? with
            | some e, some e' => g e e'
            | _, _ => false)
  | [] => rfl
  | slot :: rest => by
      simp only [List.map_cons, List.any_cons]
      rw [← denseBUSlotsAny_eq T S m f g hfg rest]
      cases S.payload[slot]? with
      | none => cases m.payload[slot]? <;> rfl
      | some e =>
          cases m.payload[slot]? with
          | none => rfl
          | some e' =>
              show (f (denseBUSlotPrep T e) (denseBUSlotPrep T e') || _) = (g e e' || _)
              rw [hfg]

theorem denseBUSlotsAll_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p))
    (f : DenseBUSlot p → DenseBUSlot p → Bool) (g : DenseExpr p → DenseExpr p → Bool)
    (hfg : ∀ e e', f (denseBUSlotPrep T e) (denseBUSlotPrep T e') = g e e') :
    ∀ fields : List Nat,
      denseBUSlotsAll f (fields.map (fun slot => (S.payload[slot]?).map (denseBUSlotPrep T)))
          (fields.map (fun slot => (m.payload[slot]?).map (denseBUSlotPrep T)))
        = fields.all (fun slot =>
            match S.payload[slot]?, m.payload[slot]? with
            | some e, some e' => g e e'
            | _, _ => false)
  | [] => rfl
  | slot :: rest => by
      simp only [List.map_cons, List.all_cons]
      rw [← denseBUSlotsAll_eq T S m f g hfg rest]
      cases S.payload[slot]? with
      | none => cases m.payload[slot]? <;> rfl
      | some e =>
          cases m.payload[slot]? with
          | none => rfl
          | some e' =>
              show (f (denseBUSlotPrep T e) (denseBUSlotPrep T e') && _) = (g e e' && _)
              rw [hfg]

/-- The hash gate on the structural compare is transparent: equal expressions hash equally. -/
private theorem denseBU_bHash_gate (e e' : DenseExpr p) :
    (e.bHash == e'.bHash && decide (e = e')) = decide (e = e') := by
  by_cases h : e = e'
  · subst h; simp
  · simp [h]

theorem denseBUConstsEq_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseBUConstsEq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = denseAddrConstsEq shape S m :=
  denseBUSlotsAll_eq T S m _ _ (fun e e' => by
    show ((e.bHash == e'.bHash && decide (e = e')) || _) = (decide (e = e') || _)
    rw [denseBU_bHash_gate]; rfl) shape.addressFields

theorem denseBUConstsNeq_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    denseBUConstsNeq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = denseAddrConstsNeq shape S m :=
  denseBUSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields

theorem denseBUPrep_slots_zip (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p)) :
    ((denseBUPrep shape T S).slots).zip ((denseBUPrep shape T m).slots)
      = shape.addressFields.map (fun slot =>
          ((S.payload[slot]?).map (denseBUSlotPrep T), (m.payload[slot]?).map (denseBUSlotPrep T))) := by
  simp [denseBUPrep, denseBUOfSlots, List.zip_map']

theorem denseBUDiffSum_eq (T : DenseTwoRootMap p) (S m : BusInteraction (DenseExpr p)) :
    ∀ fs : List Nat,
      denseBUDiffSum (fs.map (fun slot =>
          ((S.payload[slot]?).map (denseBUSlotPrep T), (m.payload[slot]?).map (denseBUSlotPrep T))))
        = denseDiffSumOver S m fs := by
  intro fs
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [List.map_cons, denseBUDiffSum, ih, denseDiffSumOver]
      cases denseDiffSumOver S m fs
      · rfl
      · cases S.payload[f]? <;> cases m.payload[f]? <;> rfl

theorem denseBUNonzeroNeq_eq (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (S m : BusInteraction (DenseExpr p)) :
    denseBUNonzeroNeq nw (denseBUPrep shape T S) (denseBUPrep shape T m)
      = denseAddrNonzeroNeq shape nw S m := by
  unfold denseBUNonzeroNeq denseAddrNonzeroNeq
  rw [denseBUPrep_slots_zip, List.sublists_map, List.any_map]
  refine congrArg _ (funext fun fs => ?_)
  simp only [Function.comp_apply]
  rw [denseBUDiffSum_eq]
  rfl

/-! ## The affine and two-root arms -/

theorem denseBUAffineNeq_sound (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (S m : BusInteraction (DenseExpr p))
    (h : denseBUAffineNeq (denseBUPrep shape T S) (denseBUPrep shape T m) = true)
    (denv : VarId → ZMod p) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval m denv) := by
  rw [show denseBUAffineNeq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = shape.addressFields.any (fun slot =>
          match S.payload[slot]?, m.payload[slot]? with
          | some e, some e' =>
            denseBUAffineNeqSlot (denseBUSlotPrep T e) (denseBUSlotPrep T e')
          | _, _ => false) from
    denseBUSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields] at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : m.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond
      unfold denseBUAffineNeqSlot denseBUSlotPrep at hcond
      cases hL : denseLinearize e with
      | none => simp [hL] at hcond
      | some L =>
        cases hL' : denseLinearize e' with
        | none => simp [hL, hL'] at hcond
        | some L' =>
          simp only [hL, hL', Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨_, hkey⟩, hconst⟩ := hcond
          refine denseAddr_slot_neq shape S m denv hslot hSp hbp ?_
          rw [denseLinearize_eval e L hL denv, denseLinearize_eval e' L' hL' denv]
          exact denseKeyNeq_sound L L' hkey hconst denv

/-- A stored reduction entry comes from an actual `densePtrReductions` pair, with the stored key
    the canonical key of both its branches and the stored constants their constants. -/
theorem denseBUSlot_reds_mem {T : DenseTwoRootMap p} {e : DenseExpr p}
    {r : UInt64 × List (VarId × ZMod p) × ZMod p × ZMod p} (h : r ∈ (denseBUSlotPrep T e).reds) :
    ∃ b1 b2, (b1, b2) ∈ densePtrReductions T e ∧ r.2.1 = denseTermKey b1 ∧
      r.2.2.1 = b1.const ∧ r.2.2.2 = b2.const := by
  simp only [denseBUSlotPrep, List.mem_map] at h
  obtain ⟨⟨b1, b2⟩, hmem, rfl⟩ := h
  exact ⟨b1, b2, hmem, rfl, rfl, rfl⟩

theorem denseBUTwoRootNeq_sound {dcs : List (DenseExpr p)} (shape : MemoryBusShape)
    (T : DenseTwoRootMap p) (hT : T.Sound dcs) (S m : BusInteraction (DenseExpr p))
    (h : denseBUTwoRootNeq (denseBUPrep shape T S) (denseBUPrep shape T m) = true)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ dcs, c.eval denv = 0) :
    shape.address (denseBIEval S denv) ≠ shape.address (denseBIEval m denv) := by
  rw [show denseBUTwoRootNeq (denseBUPrep shape T S) (denseBUPrep shape T m)
      = shape.addressFields.any (fun slot =>
          match S.payload[slot]?, m.payload[slot]? with
          | some e, some e' =>
            denseBUTwoRootNeqSlot (denseBUSlotPrep T e) (denseBUSlotPrep T e')
          | _, _ => false) from
    denseBUSlotsAny_eq T S m _ _ (fun _ _ => rfl) shape.addressFields] at h
  obtain ⟨slot, hslot, hcond⟩ := List.any_eq_true.1 h
  cases hSp : S.payload[slot]? with
  | none => rw [hSp] at hcond; simp at hcond
  | some e =>
    cases hbp : m.payload[slot]? with
    | none => rw [hSp, hbp] at hcond; simp at hcond
    | some e' =>
      rw [hSp, hbp] at hcond
      unfold denseBUTwoRootNeqSlot at hcond
      obtain ⟨ra, hra, hinner⟩ := List.any_eq_true.1 hcond
      obtain ⟨rb, hrb, hchk⟩ := List.any_eq_true.1 hinner
      obtain ⟨a1, a2, hared, hakey, hac1, hac2⟩ := denseBUSlot_reds_mem hra
      obtain ⟨b1, b2, hbred, hbkey, hbc1, hbc2⟩ := denseBUSlot_reds_mem hrb
      simp only [denseRedKeysNeq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
      obtain ⟨⟨⟨_, hkeq⟩, h11, h12⟩, h21, h22⟩ := hchk
      have hka : denseTermKey a2 = denseTermKey a1 := densePtrReductions_key hared
      have hkb : denseTermKey b2 = denseTermKey b1 := densePtrReductions_key hbred
      have hkab : denseTermKey a1 = denseTermKey b1 := by rw [← hakey, ← hbkey]; exact hkeq
      have hev := densePtrReductions_sound T hT e a1 a2 hared denv hcon
      have hev' := densePtrReductions_sound T hT e' b1 b2 hbred denv hcon
      refine denseAddr_slot_neq shape S m denv hslot hSp hbp ?_
      rcases hev with ha | ha <;> rcases hev' with hb | hb <;> rw [ha, hb]
      · exact denseKeyNeq_sound a1 b1 hkab (by rw [← hac1, ← hbc1]; exact h11) denv
      · exact denseKeyNeq_sound a1 b2 (by rw [hkab, ← hkb]) (by rw [← hac1, ← hbc2]; exact h12) denv
      · exact denseKeyNeq_sound a2 b1 (by rw [hka, hkab]) (by rw [← hac2, ← hbc1]; exact h21) denv
      · exact denseKeyNeq_sound a2 b2 (by rw [hka, hkab, ← hkb])
          (by rw [← hac2, ← hbc2]; exact h22) denv

/-! ## The two-root table is sound

Every entry the build inserts is a `denseTwoRootOf?` decomposition of an actual constraint, which
is all `DenseTwoRootMap.Sound` asserts — scoping the build to fewer variables and fewer constraints
only removes entries. -/

theorem denseBUWits_eq (d : DenseConstraintSystem p) :
    denseBUWits d = DenseNonzeroWits.build d.algebraicConstraints := rfl

theorem denseBUPrep_mult (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bi : BusInteraction (DenseExpr p)) :
    (denseBUPrep shape T bi).mult = denseMultConst bi := rfl

theorem denseBUAddTwoRoot_sound {dcs : List (DenseExpr p)} (hp : Nat.Prime p)
    (avars : Std.HashSet VarId) {c : DenseExpr p} (hc : c ∈ dcs) (T : DenseTwoRootMap p)
    (hT : T.Sound dcs) : (denseBUAddTwoRoot avars T c).Sound dcs := by
  unfold denseBUAddTwoRoot
  split
  · rename_i f1 f2
    split
    · rename_i l1 l2 hl1 hl2
      refine List.foldlRecOn _ _ hT ?_
      intro T' hT' v _
      split
      · split
        · rename_i k A δ htr
          split
          · exact hT'.insertEntry ⟨hp, by assumption, _, hc, by
              simp only [denseTwoRootOf?, hl1, hl2] ; exact htr⟩
          · exact hT'
        · exact hT'
      · exact hT'
    · exact hT
  · exact hT

theorem denseBUTwoRootMap_sound (avars : Std.HashSet VarId) (cs dcs : List (DenseExpr p))
    (hsub : ∀ c ∈ cs, c ∈ dcs) : (denseBUTwoRootMap avars cs).Sound dcs := by
  unfold denseBUTwoRootMap
  split
  · rename_i hp
    refine List.foldlRecOn _ _ (DenseTwoRootMap.empty_sound dcs) ?_
    intro T hT c hc
    exact denseBUAddTwoRoot_sound hp avars (hsub c hc) T hT
  · exact DenseTwoRootMap.empty_sound dcs

theorem denseBUTable_sound
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) :
    (denseBUTable busLists d).Sound d.algebraicConstraints :=
  denseBUTwoRootMap_sound _ _ _ (fun _ h => List.mem_of_mem_filter h)

/-! ## The classification verdicts -/

theorem denseBUClassify_send {nw : DenseNonzeroWits p} {setMult prevMult : ZMod p}
    {a m : DenseBUPre p} (h : denseBUClassify nw setMult prevMult a m = some .send) :
    m.mult = some setMult ∧ denseBUConstsEq a m = true := by
  unfold denseBUClassify at h
  split_ifs at h with h1 h2 h3
  · exact ⟨of_decide_eq_true (Bool.and_eq_true .. ▸ h1).1, (Bool.and_eq_true .. ▸ h1).2⟩
  all_goals simp at h

theorem denseBUClassify_recv {nw : DenseNonzeroWits p} {setMult prevMult : ZMod p}
    {a m : DenseBUPre p} (h : denseBUClassify nw setMult prevMult a m = some .recv) :
    m.mult = some prevMult ∧ denseBUConstsEq a m = true := by
  unfold denseBUClassify at h
  split_ifs at h with h1 h2 h3
  · simp at h
  · exact ⟨of_decide_eq_true (Bool.and_eq_true .. ▸ h2).1, (Bool.and_eq_true .. ▸ h2).2⟩
  · simp at h

theorem denseBUClassify_out {nw : DenseNonzeroWits p} {setMult prevMult : ZMod p}
    {a m : DenseBUPre p} (h : denseBUClassify nw setMult prevMult a m = some .out) :
    (denseBUConstsNeq a m || denseBUAffineNeq a m || denseBUTwoRootNeq a m
      || denseBUNonzeroNeq nw a m) = true
    ∨ ∃ c, m.mult = some c ∧ c ≠ setMult ∧ c ≠ prevMult := by
  unfold denseBUClassify at h
  split_ifs at h with h1 h2 h3
  · simp at h
  · simp at h
  · rcases (Bool.or_eq_true _ _).mp h3 with h4 | h5
    · exact Or.inl h4
    · right
      cases hm : m.mult with
      | none => rw [hm] at h5; simp at h5
      | some c =>
          rw [hm] at h5
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h5
          exact ⟨c, rfl, h5.1, h5.2⟩

/-! ## Semantic reading of a verdict -/

/-- A member send: constant multiplicity `setNewMult` and the leader's evaluated address. -/
theorem denseBUVerdict_send_sound (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    {nw : DenseNonzeroWits p} (lbi bi : BusInteraction (DenseExpr p))
    (h : denseBUClassify nw shape.setNewMult (-shape.setNewMult)
      (denseBUPrep shape T lbi) (denseBUPrep shape T bi) = some .send)
    (denv : VarId → ZMod p) :
    (denseBIEval bi denv).multiplicity = shape.setNewMult ∧
      shape.address (denseBIEval bi denv) = shape.address (denseBIEval lbi denv) := by
  obtain ⟨hm, heq⟩ := denseBUClassify_send h
  rw [denseBUPrep_mult] at hm
  refine ⟨denseConstValueEval bi.multiplicity _ hm denv, ?_⟩
  exact (denseAddrConstsEq_sound shape lbi bi
    (by rw [← denseBUConstsEq_eq shape T lbi bi]; exact heq) denv).symm

/-- A member receive: constant multiplicity `-setNewMult` and the leader's evaluated address. -/
theorem denseBUVerdict_recv_sound (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    {nw : DenseNonzeroWits p} (lbi bi : BusInteraction (DenseExpr p))
    (h : denseBUClassify nw shape.setNewMult (-shape.setNewMult)
      (denseBUPrep shape T lbi) (denseBUPrep shape T bi) = some .recv)
    (denv : VarId → ZMod p) :
    (denseBIEval bi denv).multiplicity = -shape.setNewMult ∧
      shape.address (denseBIEval bi denv) = shape.address (denseBIEval lbi denv) := by
  obtain ⟨hm, heq⟩ := denseBUClassify_recv h
  rw [denseBUPrep_mult] at hm
  refine ⟨denseConstValueEval bi.multiplicity _ hm denv, ?_⟩
  exact (denseAddrConstsEq_sound shape lbi bi
    (by rw [← denseBUConstsEq_eq shape T lbi bi]; exact heq) denv).symm

/-- Certified outside the group: different evaluated address, or a multiplicity in neither
    fiber. -/
theorem denseBUVerdict_out_sound (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (hT : T.Sound d.algebraicConstraints) (lbi bi : BusInteraction (DenseExpr p))
    (hlbi : lbi ∈ d.busInteractions) (hbi : bi ∈ d.busInteractions)
    (h : denseBUClassify (denseBUWits d) shape.setNewMult (-shape.setNewMult)
      (denseBUPrep shape T lbi) (denseBUPrep shape T bi) = some .out)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0) :
    shape.address (denseBIEval bi denv) ≠ shape.address (denseBIEval lbi denv) ∨
      ((denseBIEval bi denv).multiplicity ≠ shape.setNewMult ∧
       (denseBIEval bi denv).multiplicity ≠ -shape.setNewMult) := by
  rcases denseBUClassify_out h with harm | ⟨c, hm, hc1, hc2⟩
  · left
    intro haddr
    rcases (Bool.or_eq_true _ _).mp harm with h3 | hnz
    · rcases (Bool.or_eq_true _ _).mp h3 with h2 | h2r
      · rcases (Bool.or_eq_true _ _).mp h2 with hneq | haff
        · exact denseAddrConstsNeq_sound shape lbi bi
            (by rw [← denseBUConstsNeq_eq shape T lbi bi]; exact hneq) denv haddr.symm
        · exact denseBUAffineNeq_sound shape T lbi bi haff denv haddr.symm
      · exact denseBUTwoRootNeq_sound shape T hT lbi bi h2r denv hcon haddr.symm
    · refine denseAddrNonzeroNeq_sound reg shape d.algebraicConstraints hcov.1 lbi bi
        (hcov.2 lbi hlbi) (hcov.2 bi hbi) ?_ denv hcon haddr.symm
      rw [← denseBUNonzeroNeq_eq shape T (DenseNonzeroWits.build d.algebraicConstraints) lbi bi,
        ← denseBUWits_eq d]
      exact hnz
  · right
    rw [denseBUPrep_mult] at hm
    have := denseConstValueEval bi.multiplicity c hm denv
    show bi.multiplicity.eval denv ≠ _ ∧ bi.multiplicity.eval denv ≠ _
    rw [this]
    exact ⟨hc1, hc2⟩

/-! ## The split: membership and fiber presentations -/

theorem denseBUSplit_sends {nw : DenseNonzeroWits p} {sm pm : ZMod p} {a : DenseBUPre p} :
    ∀ {zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)}
      {s r : List (BusInteraction (DenseExpr p))},
      denseBUSplit nw sm pm a zipped = some (s, r) →
      ∀ S ∈ s, ∃ pre, (S, pre) ∈ zipped ∧ denseBUClassify nw sm pm a pre = some .send
  | [], s, r, h => by
      simp only [denseBUSplit, Option.some.injEq, Prod.mk.injEq] at h
      intro S hS
      rw [← h.1] at hS
      simp at hS
  | (bi, pre) :: rest, s, r, h => by
      rw [denseBUSplit] at h
      intro S hS
      cases hc : denseBUClassify nw sm pm a pre with
      | none => rw [hc] at h; simp at h
      | some v =>
          rw [hc] at h
          cases hrec : denseBUSplit nw sm pm a rest with
          | none => rw [hrec] at h; cases v <;> simp at h
          | some sr =>
              obtain ⟨s', r'⟩ := sr
              rw [hrec] at h
              cases v with
              | send =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.1] at hS
                  rcases List.mem_cons.mp hS with rfl | hS'
                  · exact ⟨pre, List.mem_cons_self .., hc⟩
                  · obtain ⟨pre', hmem, hcl⟩ := denseBUSplit_sends hrec S hS'
                    exact ⟨pre', List.mem_cons_of_mem _ hmem, hcl⟩
              | recv =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.1] at hS
                  obtain ⟨pre', hmem, hcl⟩ := denseBUSplit_sends hrec S hS
                  exact ⟨pre', List.mem_cons_of_mem _ hmem, hcl⟩
              | out =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.1] at hS
                  obtain ⟨pre', hmem, hcl⟩ := denseBUSplit_sends hrec S hS
                  exact ⟨pre', List.mem_cons_of_mem _ hmem, hcl⟩

theorem denseBUSplit_recvs {nw : DenseNonzeroWits p} {sm pm : ZMod p} {a : DenseBUPre p} :
    ∀ {zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)}
      {s r : List (BusInteraction (DenseExpr p))},
      denseBUSplit nw sm pm a zipped = some (s, r) →
      ∀ R ∈ r, ∃ pre, (R, pre) ∈ zipped ∧ denseBUClassify nw sm pm a pre = some .recv
  | [], s, r, h => by
      simp only [denseBUSplit, Option.some.injEq, Prod.mk.injEq] at h
      intro R hR
      rw [← h.2] at hR
      simp at hR
  | (bi, pre) :: rest, s, r, h => by
      rw [denseBUSplit] at h
      intro R hR
      cases hc : denseBUClassify nw sm pm a pre with
      | none => rw [hc] at h; simp at h
      | some v =>
          rw [hc] at h
          cases hrec : denseBUSplit nw sm pm a rest with
          | none => rw [hrec] at h; cases v <;> simp at h
          | some sr =>
              obtain ⟨s', r'⟩ := sr
              rw [hrec] at h
              cases v with
              | recv =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.2] at hR
                  rcases List.mem_cons.mp hR with rfl | hR'
                  · exact ⟨pre, List.mem_cons_self .., hc⟩
                  · obtain ⟨pre', hmem, hcl⟩ := denseBUSplit_recvs hrec R hR'
                    exact ⟨pre', List.mem_cons_of_mem _ hmem, hcl⟩
              | send =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.2] at hR
                  obtain ⟨pre', hmem, hcl⟩ := denseBUSplit_recvs hrec R hR
                  exact ⟨pre', List.mem_cons_of_mem _ hmem, hcl⟩
              | out =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.2] at hR
                  obtain ⟨pre', hmem, hcl⟩ := denseBUSplit_recvs hrec R hR
                  exact ⟨pre', List.mem_cons_of_mem _ hmem, hcl⟩

/-! Per-element step lemmas for the fiber filters, at the multiset level. `q` is the
activity filter, `P` the fiber predicate. -/

private theorem denseBU_fiber_cons_keep {P : BusInteraction (ZMod p) → Prop} [DecidablePred P]
    (x : BusInteraction (ZMod p)) (l : List (BusInteraction (ZMod p)))
    (hx : x.multiplicity ≠ 0) (hP : P x) :
    Multiset.filter P ↑((x :: l).filter (fun m => decide (m.multiplicity ≠ 0)))
      = x ::ₘ Multiset.filter P ↑(l.filter (fun m => decide (m.multiplicity ≠ 0))) := by
  rw [List.filter_cons, if_pos (decide_eq_true hx), ← Multiset.cons_coe,
    Multiset.filter_cons_of_pos _ hP]

private theorem denseBU_fiber_cons_drop {P : BusInteraction (ZMod p) → Prop} [DecidablePred P]
    (x : BusInteraction (ZMod p)) (l : List (BusInteraction (ZMod p)))
    (hP : ¬P x) :
    Multiset.filter P ↑((x :: l).filter (fun m => decide (m.multiplicity ≠ 0)))
      = Multiset.filter P ↑(l.filter (fun m => decide (m.multiplicity ≠ 0))) := by
  rw [List.filter_cons]
  by_cases hx : x.multiplicity ≠ 0
  · rw [if_pos (decide_eq_true hx), ← Multiset.cons_coe, Multiset.filter_cons_of_neg _ hP]
  · rw [if_neg (by simpa using hx)]

/-- The fiber presentations: at the leader's evaluated address, the active send/receive fibers of
    the evaluated bus list are exactly the members' evaluations, in source order. -/
theorem denseBUSplit_fibers (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (hT : T.Sound d.algebraicConstraints)
    (lbi : BusInteraction (DenseExpr p)) (hlbi : lbi ∈ d.busInteractions)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0)
    (hp1 : (1 : ZMod p) ≠ 0) (hpm : -shape.setNewMult ≠ (shape.setNewMult : ZMod p)) :
    ∀ (bisL : List (BusInteraction (DenseExpr p))), (∀ bi ∈ bisL, bi ∈ d.busInteractions) →
    ∀ (sends recvs : List (BusInteraction (DenseExpr p))),
      denseBUSplit (denseBUWits d) shape.setNewMult (-shape.setNewMult)
          (denseBUPrep shape T lbi)
          (bisL.map (fun bi => (bi, denseBUPrep shape T bi))) = some (sends, recvs) →
      sendsAt shape (shape.address (denseBIEval lbi denv))
          (↑((bisL.map (fun bi => denseBIEval bi denv)).filter
            (fun m => decide (m.multiplicity ≠ 0))) : Multiset (BusInteraction (ZMod p)))
        = ↑(sends.map (fun bi => denseBIEval bi denv))
      ∧ recvsAt shape (shape.address (denseBIEval lbi denv))
          (↑((bisL.map (fun bi => denseBIEval bi denv)).filter
            (fun m => decide (m.multiplicity ≠ 0))) : Multiset (BusInteraction (ZMod p)))
        = ↑(recvs.map (fun bi => denseBIEval bi denv))
  | [], _, sends, recvs, h => by
      simp only [List.map_nil, denseBUSplit, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact ⟨rfl, rfl⟩
  | bi :: rest, hmem, sends, recvs, h => by
      have hbid : bi ∈ d.busInteractions := hmem bi (List.mem_cons_self ..)
      have hmr : ∀ b ∈ rest, b ∈ d.busInteractions :=
        fun b hb => hmem b (List.mem_cons_of_mem _ hb)
      rw [List.map_cons, denseBUSplit] at h
      cases hc : denseBUClassify (denseBUWits d) shape.setNewMult (-shape.setNewMult)
          (denseBUPrep shape T lbi) (denseBUPrep shape T bi) with
      | none => rw [hc] at h; simp at h
      | some v =>
          rw [hc] at h
          cases hrec : denseBUSplit (denseBUWits d) shape.setNewMult (-shape.setNewMult)
              (denseBUPrep shape T lbi)
              (rest.map (fun bi => (bi, denseBUPrep shape T bi))) with
          | none => rw [hrec] at h; cases v <;> simp at h
          | some sr =>
              obtain ⟨s', r'⟩ := sr
              rw [hrec] at h
              obtain ⟨ihs, ihr⟩ := denseBUSplit_fibers reg d hcov shape T hT lbi hlbi denv hcon
                hp1 hpm rest hmr s' r' hrec
              cases v with
              | send =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hmul, haddr⟩ := denseBUVerdict_send_sound shape T lbi bi hc denv
                  have hne0 : (denseBIEval bi denv).multiplicity ≠ 0 := by
                    rw [hmul]; exact shape.setNewMult_ne_zero hp1
                  rw [← h.1, ← h.2, List.map_cons]
                  constructor
                  · show Multiset.filter _ _ = _
                    rw [List.map_cons, denseBU_fiber_cons_keep _ _ hne0 ⟨hmul, haddr⟩,
                      ← Multiset.cons_coe]
                    exact congrArg _ ihs
                  · show Multiset.filter _ _ = _
                    rw [denseBU_fiber_cons_drop _ _ (by
                        rintro ⟨hm, -⟩
                        rw [hmul] at hm
                        exact hpm hm.symm)]
                    exact ihr
              | recv =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hmul, haddr⟩ := denseBUVerdict_recv_sound shape T lbi bi hc denv
                  have hne0 : (denseBIEval bi denv).multiplicity ≠ 0 := by
                    rw [hmul]
                    exact neg_ne_zero.mpr (shape.setNewMult_ne_zero hp1)
                  rw [← h.1, ← h.2, List.map_cons]
                  constructor
                  · show Multiset.filter _ _ = _
                    rw [denseBU_fiber_cons_drop _ _ (by
                        rintro ⟨hm, -⟩
                        rw [hmul] at hm
                        exact hpm hm)]
                    exact ihs
                  · show Multiset.filter _ _ = _
                    rw [List.map_cons, denseBU_fiber_cons_keep _ _ hne0 ⟨hmul, haddr⟩,
                      ← Multiset.cons_coe]
                    exact congrArg _ ihr
              | out =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  have hout := denseBUVerdict_out_sound reg d hcov shape T hT lbi bi hlbi hbid
                    hc denv hcon
                  rw [← h.1, ← h.2, List.map_cons]
                  have hpredS : ¬((denseBIEval bi denv).multiplicity = shape.setNewMult ∧
                      shape.address (denseBIEval bi denv)
                        = shape.address (denseBIEval lbi denv)) := by
                    rintro ⟨hm, ha⟩
                    rcases hout with hne | ⟨hm1, -⟩
                    · exact hne ha
                    · exact hm1 hm
                  have hpredR : ¬((denseBIEval bi denv).multiplicity = -shape.setNewMult ∧
                      shape.address (denseBIEval bi denv)
                        = shape.address (denseBIEval lbi denv)) := by
                    rintro ⟨hm, ha⟩
                    rcases hout with hne | ⟨-, hm2⟩
                    · exact hne ha
                    · exact hm2 hm
                  constructor
                  · show Multiset.filter _ _ = _
                    rw [denseBU_fiber_cons_drop _ _ hpredS]
                    exact ihs
                  · show Multiset.filter _ _ = _
                    rw [denseBU_fiber_cons_drop _ _ hpredR]
                    exact ihr

/-! ## Timestamp structure: offsets, bounds, gadgets -/

/-- A linear form's value is its constant plus the sum over its *normalized* terms. -/
private theorem denseLin_eval_norm (a : DenseLinExpr p) (denv : VarId → ZMod p) :
    a.eval denv = a.const + (a.norm.terms.map (fun t => t.2 * denv t.1)).sum := by
  rw [← DenseLinExpr.norm_eval a denv]; rfl

/-- Forms with equal canonical keys share their variable part. -/
theorem denseKey_eval_base_eq (L L' : DenseLinExpr p)
    (h : denseTermKey L = denseTermKey L') (denv : VarId → ZMod p) :
    L.eval denv - L.const = L'.eval denv - L'.const := by
  have hsum : (L.norm.terms.map (fun t => t.2 * denv t.1)).sum
      = (L'.norm.terms.map (fun t => t.2 * denv t.1)).sum :=
    ((denseTermKey_perm L L' h).map _).sum_eq
  rw [denseLin_eval_norm L denv, denseLin_eval_norm L' denv, hsum]
  ring

theorem denseBUOffs_length {tsField : Nat} {key0 : List (VarId × ZMod p)} :
    ∀ {sends : List (BusInteraction (DenseExpr p))} {offs : List (ZMod p)},
      denseBUOffs tsField key0 sends = some offs → offs.length = sends.length
  | [], offs, h => by
      simp only [denseBUOffs, Option.some.injEq] at h
      rw [← h]
      rfl
  | S :: rest, offs, h => by
      cases hL : denseBUTsLin tsField S with
      | none => simp [denseBUOffs, hL] at h
      | some L =>
          cases hrec : denseBUOffs tsField key0 rest with
          | none => simp [denseBUOffs, hL, hrec] at h
          | some offs' =>
              simp only [denseBUOffs, hL, hrec] at h
              split at h
              · simp only [Option.some.injEq] at h
                rw [← h]
                simp [denseBUOffs_length hrec]
              · simp at h

theorem denseBUOffs_spec {tsField : Nat} {key0 : List (VarId × ZMod p)} :
    ∀ {sends : List (BusInteraction (DenseExpr p))} {offs : List (ZMod p)},
      denseBUOffs tsField key0 sends = some offs →
      ∀ (i : Nat) (S : BusInteraction (DenseExpr p)) (o : ZMod p),
        sends[i]? = some S → offs[i]? = some o →
        ∃ e L, S.payload[tsField]? = some e ∧ denseLinearize e = some L ∧
          denseTermKey L = key0 ∧ o = L.const
  | [], offs, h => by
      intro i S o hS
      simp at hS
  | S0 :: rest, offs, h => by
      cases hL : denseBUTsLin tsField S0 with
      | none => simp [denseBUOffs, hL] at h
      | some L =>
          cases hrec : denseBUOffs tsField key0 rest with
          | none => simp [denseBUOffs, hL, hrec] at h
          | some offs' =>
              simp only [denseBUOffs, hL, hrec] at h
              split at h
              · rename_i hkey
                simp only [Option.some.injEq] at h
                intro i S o hS ho
                rw [← h] at ho
                cases i with
                | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at hS ho
                    unfold denseBUTsLin at hL
                    cases hpay : S0.payload[tsField]? with
                    | none => rw [hpay] at hL; simp at hL
                    | some e =>
                        rw [hpay] at hL
                        exact ⟨e, L, by rw [← hS]; exact hpay, hL, hkey, ho.symm⟩
                | succ j =>
                    simp only [List.getElem?_cons_succ] at hS ho
                    exact denseBUOffs_spec hrec j S o hS ho
              · simp at h

/-- The step check read index-wise: consecutive offsets differ by a value in `[1, B)`. -/
theorem denseBUStepsOk_spec {B : Nat} :
    ∀ {offs : List (ZMod p)}, denseBUStepsOk B offs = true →
      ∀ (i : Nat) (hi : i + 1 < offs.length),
        1 ≤ ((offs[i + 1]'hi) - (offs[i]'(by omega))).val ∧
          ((offs[i + 1]'hi) - (offs[i]'(by omega))).val < B
  | [], _, i, hi => by simp at hi
  | [_], _, i, hi => by simp at hi
  | c :: c' :: rest, h, i, hi => by
      simp only [denseBUStepsOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, hrec⟩ := h
      cases i with
      | zero => exact ⟨h1, h2⟩
      | succ j =>
          have hj : j + 1 < (c' :: rest).length := by
            simp only [List.length_cons] at hi ⊢
            omega
          exact denseBUStepsOk_spec hrec j hj

/-- The range-check witness scan is sound: a hit bounds the variable's value under any
    satisfying assignment. -/
theorem denseBUVarBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (allBis : List (BusInteraction (DenseExpr p)))
    (hall : ∀ bi ∈ allBis, bi ∈ d.busInteractions)
    (v : VarId) (w : Nat) (h : denseBUVarBound bs facts allBis v = some w)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) : (denv v).val < w := by
  induction allBis with
  | nil => simp [denseBUVarBound] at h
  | cons bi rest ih =>
      have hrest : ∀ b ∈ rest, b ∈ d.busInteractions :=
        fun b hb => hall b (List.mem_cons_of_mem _ hb)
      rw [denseBUVarBound] at h
      split at h
      · rename_i v' b c hpay hmc
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          obtain ⟨⟨hvr, hv'⟩, hcne⟩ := hcond
          simp only [Option.some.injEq] at h
          have hbmem : bi ∈ d.busInteractions := hall bi (List.mem_cons_self ..)
          have hmev : (denseBIEval bi denv).multiplicity = c :=
            denseConstValueEval bi.multiplicity c hmc denv
          have hacc : bs.accepts (denseBIEval bi denv) :=
            hsat.2 bi hbmem (by rw [hmev]; exact hcne)
          have hbieq : denseBIEval bi denv
              = { busId := bi.busId, multiplicity := bi.multiplicity.eval denv,
                  payload := [denv v', b] } := by
            unfold denseBIEval
            rw [hpay]
            rfl
          have hiff := (facts.varRangeBus_sound bi.busId hvr).2 (denv v') b
            (bi.multiplicity.eval denv)
          rw [← hbieq] at hiff
          have hbound := (hiff.mp hacc).2
          rw [← h, ← hv']
          exact hbound
        · exact ih hrest h
      · exact ih hrest h

/-- The per-interaction slot scan is sound: a hit bounds the variable's value under any
    satisfying assignment, via `facts.slotBound_sound` on the evaluated message. -/
theorem denseBUSlotScanAt_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (bi : BusInteraction (DenseExpr p))
    (hbi : bi ∈ d.busInteractions) (c : ZMod p) (hmc : denseMultConst bi = some c)
    (hcne : c ≠ 0) (pat : List (Option (ZMod p)))
    (hpat : pat = bi.payload.map DenseExpr.constValue?) (v : VarId)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) :
    ∀ (slots : List Nat) (w : Nat),
      denseBUSlotScanAt bs facts bi c pat v slots = some w → (denv v).val < w
  | [], w, h => by simp [denseBUSlotScanAt] at h
  | slot :: rest, w, h => by
      rw [denseBUSlotScanAt] at h
      split at h
      · rename_i v' hslot
        split at h
        · rename_i hv'
          split at h
          · rename_i w' hsb
            obtain rfl : w' = w := Option.some.inj h
            subst hv'
            have hmev : (denseBIEval bi denv).multiplicity = c :=
              denseConstValueEval bi.multiplicity c hmc denv
            have hacc : bs.accepts (denseBIEval bi denv) :=
              hsat.2 bi hbi (by rw [hmev]; exact hcne)
            have hmatch : Matches (denseBIEval bi denv).payload pat := by
              rw [hpat]
              exact denseMatches_evalPattern bi.payload denv
            have hsb' : facts.slotBound (denseBIEval bi denv).busId
                (denseBIEval bi denv).multiplicity pat slot = some w' := by
              rw [hmev]; exact hsb
            have hget : (denseBIEval bi denv).payload[slot]? = some (denv v') := by
              show (bi.payload.map (fun e => e.eval denv))[slot]? = some (denv v')
              rw [List.getElem?_map, hslot]
              rfl
            exact facts.slotBound_sound (denseBIEval bi denv) pat slot w' (denv v')
              hsb' hmatch hacc hget
          · exact denseBUSlotScanAt_sound bs facts d bi hbi c hmc hcne pat hpat v denv hsat
              rest w h
        · exact denseBUSlotScanAt_sound bs facts d bi hbi c hmc hcne pat hpat v denv hsat
            rest w h
      · exact denseBUSlotScanAt_sound bs facts d bi hbi c hmc hcne pat hpat v denv hsat
          rest w h

/-- The `facts.slotBound` scan is sound: a hit bounds the variable's value under any
    satisfying assignment. -/
theorem denseBUSlotScan_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (allBis : List (BusInteraction (DenseExpr p)))
    (hall : ∀ bi ∈ allBis, bi ∈ d.busInteractions)
    (v : VarId) (w : Nat) (h : denseBUSlotScan bs facts allBis v = some w)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) : (denv v).val < w := by
  induction allBis with
  | nil => simp [denseBUSlotScan] at h
  | cons bi rest ih =>
      have hrest : ∀ b ∈ rest, b ∈ d.busInteractions :=
        fun b hb => hall b (List.mem_cons_of_mem _ hb)
      rw [denseBUSlotScan] at h
      split at h
      · rename_i c hmc
        split at h
        · rename_i hcne
          split at h
          · rename_i w' hscan
            obtain rfl : w' = w := Option.some.inj h
            exact denseBUSlotScanAt_sound bs facts d bi (hall bi (List.mem_cons_self ..)) c hmc
              (by simpa using hcne) _ rfl v denv hsat _ w' hscan
          · exact ih hrest h
        · exact ih hrest h
      · exact ih hrest h

/-- Either range-check scan bounds the variable soundly. -/
theorem denseBUAnyBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (allBis : List (BusInteraction (DenseExpr p)))
    (hall : ∀ bi ∈ allBis, bi ∈ d.busInteractions)
    (v : VarId) (w : Nat) (h : denseBUAnyBound bs facts allBis v = some w)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) : (denv v).val < w := by
  rw [denseBUAnyBound] at h
  split at h
  · rename_i w' hvb
    obtain rfl : w' = w := Option.some.inj h
    exact denseBUVarBound_sound bs facts d allBis hall v w' hvb denv hsat
  · exact denseBUSlotScan_sound bs facts d allBis hall v w h denv hsat

/-- The indexed scan is sound: each consulted position is re-verified on its own singleton, so a
    hit bounds the variable under any satisfying assignment regardless of the index's content. -/
theorem denseBUIdxScan_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (allBis : List (BusInteraction (DenseExpr p)))
    (hall : ∀ bi ∈ allBis, bi ∈ d.busInteractions) (v : VarId)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv) :
    ∀ (positions : List Nat) (w : Nat),
      denseBUIdxScan bs facts allBis v positions = some w → (denv v).val < w
  | [], w, h => by simp [denseBUIdxScan] at h
  | i :: rest, w, h => by
      rw [denseBUIdxScan] at h
      split at h
      · rename_i bi hbi
        split at h
        · rename_i w' hw
          obtain rfl : w' = w := Option.some.inj h
          have hmem : bi ∈ d.busInteractions :=
            hall bi (List.mem_of_getElem? hbi)
          exact denseBUAnyBound_sound bs facts d [bi]
            (fun b hb => by rwa [List.mem_singleton.mp hb]) v w' hw denv hsat
        · exact denseBUIdxScan_sound bs facts d allBis hall v denv hsat rest w h
      · exact denseBUIdxScan_sound bs facts d allBis hall v denv hsat rest w h

/-- The per-term certificates: the certified pairs are the terms, each with a sound bound. -/
theorem denseBUTermCerts_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (allBis : List (BusInteraction (DenseExpr p)))
    (hall : ∀ bi ∈ allBis, bi ∈ d.busInteractions) (idx : DenseBUIdx) :
    ∀ (terms : List (VarId × ZMod p)) (certs : List (VarId × ZMod p × Nat)),
      denseBUTermCerts bs facts allBis idx terms = some certs →
      certs.map (fun c => (c.1, c.2.1)) = terms ∧
      ∀ (denv : VarId → ZMod p), d.satisfies bs denv →
        ∀ c ∈ certs, (denv c.1).val < c.2.2
  | [], certs, h => by
      simp only [denseBUTermCerts, Option.some.injEq] at h
      rw [← h]
      exact ⟨rfl, by intro denv _ c hc; simp at hc⟩
  | (v, coeff) :: rest, certs, h => by
      cases hw : denseBUIdxScan bs facts allBis v (idx.bounds.getD v []) with
      | none => simp [denseBUTermCerts, hw] at h
      | some w =>
          cases hrec : denseBUTermCerts bs facts allBis idx rest with
          | none => simp [denseBUTermCerts, hw, hrec] at h
          | some cs =>
              simp only [denseBUTermCerts, hw, hrec, Option.some.injEq] at h
              obtain ⟨hcorr, hbnd⟩ :=
                denseBUTermCerts_sound bs facts d allBis hall idx rest cs hrec
              rw [← h]
              refine ⟨by simp [hcorr], ?_⟩
              intro denv hsat c hc
              rcases List.mem_cons.mp hc with rfl | hc'
              · exact denseBUIdxScan_sound bs facts d allBis hall v denv hsat _ w hw
              · exact hbnd denv hsat c hc'

/-- The variable-limb certificate is sound: with `N` evaluating to `a − x` and `x` bounded
    (TS_BOUND), `x.val < a.val`. -/
theorem denseBUGadgetCore_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (idx : DenseBUIdx) (B : Nat)
    (N : DenseLinExpr p)
    (h : denseBUGadgetCore bs facts d.busInteractions idx B N = true)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv)
    (a x : ZMod p) (hax : N.eval denv = a - x) (hx : x.val < B) : x.val < a.val := by
  cases hcerts : denseBUTermCerts bs facts d.busInteractions idx N.terms with
  | none => simp [denseBUGadgetCore, hcerts] at h
  | some certs =>
  simp only [denseBUGadgetCore, hcerts, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc0, htot⟩ := h
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨hcorr, hbnd⟩ := denseBUTermCerts_sound bs facts d d.busInteractions
    (fun _ hb => hb) idx N.terms certs hcerts
  set triples : List (ℕ × ℕ × ZMod p) :=
    certs.map (fun c => (c.2.1.val, c.2.2, denv c.1)) with htriples
  have hterm_sum : (triples.map fun t => (t.1 : ZMod p) * t.2.2).sum
      = (N.terms.map (fun t => t.2 * denv t.1)).sum := by
    rw [htriples, List.map_map, ← hcorr, List.map_map]
    refine congrArg _ (List.map_congr_left fun c _ => ?_)
    simp only [Function.comp_apply]
    rw [ZMod.natCast_val, ZMod.cast_id]
  have heq : a = ((N.const.val : ℕ) : ZMod p) + x
      + (triples.map fun t => (t.1 : ZMod p) * t.2.2).sum := by
    have hNv : N.eval denv = N.const + (N.terms.map (fun t => t.2 * denv t.1)).sum := rfl
    rw [hterm_sum, ZMod.natCast_val, ZMod.cast_id]
    have hcomb := hax.symm.trans hNv
    linear_combination hcomb
  have hbnd' : ∀ t ∈ triples, t.2.2.val < t.2.1 := by
    intro t ht
    rw [htriples] at ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hbnd denv hsat c hc
  have htot' : N.const.val + B + (triples.map fun t => t.1 * (t.2.1 - 1)).sum ≤ p := by
    rw [htriples, List.map_map]
    exact htot
  exact val_lt_of_lessThan_gadget a x N.const.val B hc0 triples heq hbnd' hx htot'

/-- The remainder check is sound: with a synthetic limb value `X < bX` for `LX` and `N`
    evaluating to `a − x`, `x.val < a.val`. -/
theorem denseBUGadgetXRem_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (idx : DenseBUIdx) (B : Nat)
    (N LX : DenseLinExpr p) (k : ZMod p) (bX : Nat)
    (h : denseBUGadgetXRem bs facts d.busInteractions idx B N LX k bX = true)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv)
    (X : ZMod p) (hX : LX.eval denv = X) (hXb : X.val < bX)
    (a x : ZMod p) (hax : N.eval denv = a - x) (hx : x.val < B) : x.val < a.val := by
  cases hcerts : denseBUTermCerts bs facts d.busInteractions idx
      ((N.add (LX.scale (-k))).norm).terms with
  | none => simp [denseBUGadgetXRem, hcerts] at h
  | some certs =>
  simp only [denseBUGadgetXRem, hcerts, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc0, htot⟩ := h
  set Rem := (N.add (LX.scale (-k))).norm with hRem
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨hcorr, hbnd⟩ := denseBUTermCerts_sound bs facts d d.busInteractions
    (fun _ hb => hb) idx Rem.terms certs hcerts
  set triples : List (ℕ × ℕ × ZMod p) :=
    (k.val, bX, X) :: certs.map (fun c => (c.2.1.val, c.2.2, denv c.1)) with htriples
  have hterm_sum : ((certs.map (fun c => (c.2.1.val, c.2.2, denv c.1))).map
        fun t => ((t.1 : ℕ) : ZMod p) * t.2.2).sum
      = (Rem.terms.map (fun t => t.2 * denv t.1)).sum := by
    rw [List.map_map, ← hcorr, List.map_map]
    refine congrArg _ (List.map_congr_left fun c _ => ?_)
    simp only [Function.comp_apply]
    rw [ZMod.natCast_val, ZMod.cast_id]
  have heq : a = ((Rem.const.val : ℕ) : ZMod p) + x
      + (triples.map fun t => (t.1 : ZMod p) * t.2.2).sum := by
    have hRe : Rem.eval denv = N.eval denv - k * LX.eval denv := by
      rw [hRem, DenseLinExpr.norm_eval, DenseLinExpr.add_eval, DenseLinExpr.scale_eval]
      ring
    have hRv : Rem.eval denv = Rem.const + (Rem.terms.map (fun t => t.2 * denv t.1)).sum := rfl
    rw [htriples]
    simp only [List.map_cons, List.sum_cons]
    rw [hterm_sum, ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
    have hcomb := hRe.symm.trans hRv
    rw [hax, hX] at hcomb
    linear_combination hcomb
  have hbnd' : ∀ t ∈ triples, t.2.2.val < t.2.1 := by
    intro t ht
    rw [htriples] at ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact hXb
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht'
      exact hbnd denv hsat c hc
  have htot' : Rem.const.val + B + (triples.map fun t => t.1 * (t.2.1 - 1)).sum ≤ p := by
    rw [htriples]
    simp only [List.map_cons, List.sum_cons, List.map_map]
    rw [← Nat.add_assoc]
    exact htot
  exact val_lt_of_lessThan_gadget a x Rem.const.val B hc0 triples heq hbnd' hx htot'

/-- One synthetic-limb candidate is sound: the slot's declared bound applies to its evaluated
    expression (`facts.slotBound_sound`), and the remainder check finishes the gadget. -/
theorem denseBUGadgetXSlot_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (idx : DenseBUIdx) (B : Nat)
    (N : DenseLinExpr p)
    (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ d.busInteractions)
    (c : ZMod p) (hmc : denseMultConst bi = some c) (hcne : c ≠ 0) (slot : Nat)
    (h : denseBUGadgetXSlot bs facts d.busInteractions idx B N bi c slot = true)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv)
    (a x : ZMod p) (hax : N.eval denv = a - x) (hx : x.val < B) : x.val < a.val := by
  rw [denseBUGadgetXSlot] at h
  split at h
  case _ bX hsb =>
    split at h
    case _ eX hpx =>
      split at h
      case _ LX hlin =>
        split at h
        case _ t0 hfind =>
          have hmev : (denseBIEval bi denv).multiplicity = c :=
            denseConstValueEval bi.multiplicity c hmc denv
          have hacc : bs.accepts (denseBIEval bi denv) :=
            hsat.2 bi hbi (by rw [hmev]; exact hcne)
          have hmatch : Matches (denseBIEval bi denv).payload
              (bi.payload.map DenseExpr.constValue?) :=
            denseMatches_evalPattern bi.payload denv
          have hsb' : facts.slotBound (denseBIEval bi denv).busId
              (denseBIEval bi denv).multiplicity (bi.payload.map DenseExpr.constValue?) slot
              = some bX := by
            rw [hmev]; exact hsb
          have hget : (denseBIEval bi denv).payload[slot]? = some (eX.eval denv) := by
            show (bi.payload.map (fun e => e.eval denv))[slot]? = some (eX.eval denv)
            rw [List.getElem?_map, hpx]
            rfl
          have hXb : (eX.eval denv).val < bX :=
            facts.slotBound_sound (denseBIEval bi denv) (bi.payload.map DenseExpr.constValue?)
              slot bX (eX.eval denv) hsb' hmatch hacc hget
          exact denseBUGadgetXRem_sound bs facts d idx B N LX (t0.2 * (LX.coeff t0.1)⁻¹) bX h
            denv hsat (eX.eval denv) (denseLinearize_eval eX LX hlin denv).symm hXb a x hax hx
        case _ => exact absurd h (by simp)
      case _ => exact absurd h (by simp)
    case _ => exact absurd h (by simp)
  case _ => exact absurd h (by simp)

/-- The expression-limb fallback is sound. -/
theorem denseBUGadgetX_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (idx : DenseBUIdx) (B : Nat)
    (N : DenseLinExpr p)
    (h : denseBUGadgetX bs facts d.busInteractions idx B N = true)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv)
    (a x : ZMod p) (hax : N.eval denv = a - x) (hx : x.val < B) : x.val < a.val := by
  rw [denseBUGadgetX, List.any_eq_true] at h
  obtain ⟨is, _, hb⟩ := h
  revert hb
  split
  case _ bi hbi =>
    split
    case _ c hmc =>
      intro hb
      rw [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨hcne, hslot⟩ := hb
      exact denseBUGadgetXSlot_sound bs facts d idx B N bi (List.mem_of_getElem? hbi)
        c hmc hcne is.2 hslot denv hsat a x hax hx
    case _ => intro hb; exact absurd hb (by simp)
  case _ => intro hb; exact absurd hb (by simp)

/-- The solved LessThan gadget forces the receive's ts-slot value below its own send's,
    given the receive-side TS_BOUND (`hx`). -/
theorem denseBUGadgetOk_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (idx : DenseBUIdx) (tsField B : Nat)
    (S R : BusInteraction (DenseExpr p))
    (h : denseBUGadgetOk bs facts d.busInteractions idx tsField B S R = true)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv)
    (hx : tsSlotVal tsField (denseBIEval R denv) < B) :
    tsSlotVal tsField (denseBIEval R denv) < tsSlotVal tsField (denseBIEval S denv) := by
  cases hLS : denseBUTsLin tsField S with
  | none => simp [denseBUGadgetOk, hLS] at h
  | some LS =>
  cases hLR : denseBUTsLin tsField R with
  | none => simp [denseBUGadgetOk, hLS, hLR] at h
  | some LR =>
  simp only [denseBUGadgetOk, hLS, hLR, Bool.or_eq_true] at h
  set N := (LS.add (LR.scale (-1))).norm with hN
  -- payload slots
  unfold denseBUTsLin at hLS hLR
  cases hpS : S.payload[tsField]? with
  | none => rw [hpS] at hLS; simp at hLS
  | some eS =>
  cases hpR : R.payload[tsField]? with
  | none => rw [hpR] at hLR; simp at hLR
  | some eR =>
  rw [hpS] at hLS
  rw [hpR] at hLR
  -- evaluated ts values
  have hvS : tsSlotVal tsField (denseBIEval S denv) = (eS.eval denv).val := by
    show (((S.payload.map (fun e : DenseExpr p => e.eval denv))[tsField]?).getD 0).val = _
    rw [List.getElem?_map, hpS]
    rfl
  have hvR : tsSlotVal tsField (denseBIEval R denv) = (eR.eval denv).val := by
    show (((R.payload.map (fun e : DenseExpr p => e.eval denv))[tsField]?).getD 0).val = _
    rw [List.getElem?_map, hpR]
    rfl
  rw [hvS, hvR]
  rw [hvR] at hx
  have hax : N.eval denv = eS.eval denv - eR.eval denv := by
    rw [hN, DenseLinExpr.norm_eval, DenseLinExpr.add_eval, DenseLinExpr.scale_eval,
      denseLinearize_eval eS LS hLS denv, denseLinearize_eval eR LR hLR denv]
    ring
  rcases h with h | h
  · exact denseBUGadgetCore_sound bs facts d idx B N h denv hsat
      (eS.eval denv) (eR.eval denv) hax hx
  · exact denseBUGadgetX_sound bs facts d idx B N h denv hsat
      (eS.eval denv) (eR.eval denv) hax hx
/-! ## Assembling the group -/

theorem denseBU_one_ne_zero (hp : 2 ^ 30 < p) : (1 : ZMod p) ≠ 0 := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  exact one_ne_zero

theorem denseBU_negSet_ne (hp : 2 ^ 30 < p) (shape : MemoryBusShape) :
    -shape.setNewMult ≠ (shape.setNewMult : ZMod p) := by
  haveI : NeZero p := ⟨by omega⟩
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast (n := p) 2
    rw [h, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  intro h
  apply h2
  have hcast : ((2 : ℕ) : ZMod p) = 1 + 1 := by push_cast; ring
  rw [hcast]
  unfold MemoryBusShape.setNewMult at h
  cases hd : shape.direction <;> rw [hd] at h <;> simp only [] at h
  · have h0 : (-1 : ZMod p) + 1 = 1 + 1 := by rw [h]
    rw [← h0]
    ring
  · calc (1 : ZMod p) + 1 = - -1 + 1 := by ring
      _ = -1 + 1 := by rw [h]
      _ = 0 := by ring

/-- The list-to-`Fin`-presentation bridge. -/
theorem denseBU_coe_map_fin {α β : Type _} {n : ℕ} (l : List α) (hn : l.length = n)
    (f : α → β) :
    (↑(l.map f) : Multiset β)
      = Multiset.map (fun i : Fin n => f (l[i.val]'(hn ▸ i.isLt))) ↑(List.finRange n) := by
  subst hn
  rw [show Multiset.map (fun i : Fin l.length => f (l[i.val]'i.isLt)) ↑(List.finRange l.length)
    = ↑((List.finRange l.length).map (fun i : Fin l.length => f (l[i.val]'i.isLt))) from rfl]
  congr 1
  rw [show (List.finRange l.length).map (fun i : Fin l.length => f (l[i.val]'i.isLt))
    = ((List.finRange l.length).map (fun i : Fin l.length => l[i.val]'i.isLt)).map f from by
      rw [List.map_map]; rfl]
  rw [List.map_getElem_finRange]

/-- The verified group forces every interior receive to copy the previous send's payload. -/
theorem denseBUGroupPairs?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (tsField B : Nat) (htsf : facts.memTsField busId = some (tsField, B))
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (pos : Nat) (sends recvs : List (BusInteraction (DenseExpr p)))
    (idx : DenseBUIdx)
    (hgrp : denseBUGroupPairs? bs facts (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B d.busInteractions idx
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape T bi))) pos = some (sends, recvs))
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBUGroupEqs shape sends recvs, c.eval denv = 0 := by
  set bisL := d.busInteractions.filter (fun bi => bi.busId = busId) with hbisL
  have hbmem : ∀ bi ∈ bisL, bi ∈ d.busInteractions := fun bi hb => List.mem_of_mem_filter hb
  -- invert the verifier
  rw [denseSetNewMult_eq, denseGetPreviousMult_eq] at hgrp
  cases hlp : (bisL.map (fun bi => (bi, denseBUPrep shape T bi)))[pos]? with
  | none => simp [denseBUGroupPairs?, hlp] at hgrp
  | some lp =>
  cases hsplit : denseBUSplit (denseBUWits d) shape.setNewMult (-shape.setNewMult) lp.2
      (bisL.map (fun bi => (bi, denseBUPrep shape T bi))) with
  | none => simp [denseBUGroupPairs?, hlp, hsplit] at hgrp
  | some sr =>
  obtain ⟨sends', recvs'⟩ := sr
  simp only [denseBUGroupPairs?, hlp, hsplit] at hgrp
  split at hgrp
  case isFalse => simp at hgrp
  rename_i hgate
  split at hgrp
  case isFalse => simp at hgrp
  rename_i hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgate
  obtain ⟨hp30, hB29⟩ := hgate
  simp only [Option.some.injEq, Prod.mk.injEq] at hgrp
  obtain ⟨rfl, rfl⟩ : sends = sends' ∧ recvs = recvs' := ⟨hgrp.1.symm, hgrp.2.symm⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hk2, hklen⟩, htsok⟩, hgad⟩ := hchk
  -- the leader
  obtain ⟨lbi, hlbi_get, hlp_eq⟩ : ∃ lbi, bisL[pos]? = some lbi ∧
      lp = (lbi, denseBUPrep shape T lbi) := by
    rw [List.getElem?_map] at hlp
    cases hb : bisL[pos]? with
    | none => rw [hb] at hlp; simp at hlp
    | some b =>
        rw [hb] at hlp
        simp only [Option.map_some, Option.some.injEq] at hlp
        exact ⟨b, rfl, hlp.symm⟩
  have hlbi_mem : lbi ∈ bisL := List.mem_of_getElem? hlbi_get
  have hlbi : lbi ∈ d.busInteractions := hbmem lbi hlbi_mem
  rw [hlp_eq] at hsplit
  -- the p-facts
  haveI : NeZero p := ⟨by omega⟩
  have hp1 : (1 : ZMod p) ≠ 0 := denseBU_one_ne_zero hp30
  have hpm : -shape.setNewMult ≠ (shape.setNewMult : ZMod p) := denseBU_negSet_ne hp30 shape
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  -- the fibers
  obtain ⟨hsends, hrecvs⟩ := denseBUSplit_fibers reg d hcov shape T hT lbi hlbi denv hcon hp1
    hpm bisL hbmem sends recvs hsplit
  -- the order-free rely on this bus
  have hadm' : bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hM := facts.admissible_sound (d.busInteractions.map (fun bi => denseBIEval bi denv))
    hadm' busId shape hshape
  rw [dense_map_eval_filter_busId, ← hbisL] at hM
  -- the TS_BOUND rely on this bus
  have hbnds := facts.memTsField_sound (d.busInteractions.map (fun bi => denseBIEval bi denv))
    hadm' busId tsField B htsf
  rw [dense_map_eval_filter_busId, ← hbisL] at hbnds
  -- member facts
  have hsend_mult : ∀ S ∈ sends, (denseBIEval S denv).multiplicity = shape.setNewMult := by
    intro S hS
    obtain ⟨pre, hmem, hcl⟩ := denseBUSplit_sends hsplit S hS
    obtain ⟨S', hS', heq⟩ := List.mem_map.mp hmem
    cases heq
    exact (denseBUVerdict_send_sound shape T lbi S hcl denv).1
  have hrecv_mult : ∀ R ∈ recvs, (denseBIEval R denv).multiplicity = -shape.setNewMult := by
    intro R hR
    obtain ⟨pre, hmem, hcl⟩ := denseBUSplit_recvs hsplit R hR
    obtain ⟨R', hR', heq⟩ := List.mem_map.mp hmem
    cases heq
    exact (denseBUVerdict_recv_sound shape T lbi R hcl denv).1
  have hsend_bisL : ∀ S ∈ sends, S ∈ bisL := by
    intro S hS
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_sends hsplit S hS
    obtain ⟨S', hS', heq⟩ := List.mem_map.mp hmem
    rw [show S' = S from congrArg Prod.fst heq] at hS'
    exact hS'
  have hrecv_bisL : ∀ R ∈ recvs, R ∈ bisL := by
    intro R hR
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_recvs hsplit R hR
    obtain ⟨R', hR', heq⟩ := List.mem_map.mp hmem
    rw [show R' = R from congrArg Prod.fst heq] at hR'
    exact hR'
  -- TS bounds on members
  have hsend_ts : ∀ S ∈ sends, tsSlotVal tsField (denseBIEval S denv) < B := by
    intro S hS
    refine hbnds (denseBIEval S denv)
      (List.mem_map.mpr ⟨S, hsend_bisL S hS, rfl⟩) ?_
    rw [hsend_mult S hS]
    exact shape.setNewMult_ne_zero hp1
  have hrecv_ts : ∀ R ∈ recvs, tsSlotVal tsField (denseBIEval R denv) < B := by
    intro R hR
    refine hbnds (denseBIEval R denv)
      (List.mem_map.mpr ⟨R, hrecv_bisL R hR, rfl⟩) ?_
    rw [hrecv_mult R hR]
    exact neg_ne_zero.mpr (shape.setNewMult_ne_zero hp1)
  -- the send ts structure
  cases hS0 : sends.head? with
  | none => simp [denseBUSendTsOk, hS0] at htsok
  | some S0 =>
  cases hL0 : denseBUTsLin tsField S0 with
  | none => simp [denseBUSendTsOk, hS0, hL0] at htsok
  | some L0 =>
  cases hoffs : denseBUOffs tsField (denseTermKey L0) sends with
  | none => simp [denseBUSendTsOk, hS0, hL0, hoffs] at htsok
  | some offs =>
  simp only [denseBUSendTsOk, hS0, hL0, hoffs] at htsok
  have hstepspec := denseBUStepsOk_spec htsok
  have hofflen : offs.length = sends.length := denseBUOffs_length hoffs
  have hoffb0 : ∀ i : Nat, i < sends.length → i < offs.length :=
    fun i hi => Nat.lt_of_lt_of_eq hi hofflen.symm
  -- indexing
  set k := sends.length with hk
  have hklen' : recvs.length = k := hklen.symm
  have hrecb : ∀ i : Fin k, i.val < recvs.length :=
    fun i => Nat.lt_of_lt_of_eq i.isLt hklen'.symm
  set A := shape.address (denseBIEval lbi denv) with hA
  set M : Multiset (BusInteraction (ZMod p)) :=
    ↑((bisL.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0))) with hMdef
  set send : Fin k → BusInteraction (ZMod p) :=
    fun i => denseBIEval (sends[i.val]'i.isLt) denv with hsendf
  set recv : Fin k → BusInteraction (ZMod p) :=
    fun i => denseBIEval (recvs[i.val]'(hrecb i)) denv with hrecvf
  have hsendP : sendsAt shape A M = Multiset.map send ↑(List.finRange k) := by
    rw [hsends, denseBU_coe_map_fin sends rfl (fun bi => denseBIEval bi denv)]
  have hrecvP : recvsAt shape A M = Multiset.map recv ↑(List.finRange k) := by
    rw [hrecvs, denseBU_coe_map_fin recvs hklen' (fun bi => denseBIEval bi denv)]
  set off : Fin k → ZMod p := fun i => offs[i.val]'(hoffb0 i.val i.isLt) with hofff
  have hstep : ∀ (i : ℕ) (hi : i + 1 < k),
      1 ≤ (off ⟨i + 1, hi⟩ - off ⟨i, Nat.lt_of_succ_lt hi⟩).val ∧
        (off ⟨i + 1, hi⟩ - off ⟨i, Nat.lt_of_succ_lt hi⟩).val < B := by
    intro i hi
    exact hstepspec i (by omega)
  -- offsets certificate per send
  have hoffspec := denseBUOffs_spec hoffs
  set b : ZMod p := L0.eval denv - L0.const with hb
  have hts : ∀ i : Fin k, (send i).payload[tsField]? = some (b + off i) := by
    intro i
    obtain ⟨e, L, hpay, hlin, hkey, ho⟩ := hoffspec i.val (sends[i.val]'i.isLt)
      (offs[i.val]'(hoffb0 i.val i.isLt))
      (List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩)
      (List.getElem?_eq_some_iff.mpr ⟨hoffb0 i.val i.isLt, rfl⟩)
    have hslot : (send i).payload[tsField]? = some (e.eval denv) := by
      show ((sends[i.val]'i.isLt).payload.map (fun e => e.eval denv))[tsField]? = _
      rw [List.getElem?_map, hpay]
      rfl
    rw [hslot]
    congr 1
    rw [denseLinearize_eval e L hlin denv]
    have hbase : L.eval denv - L.const = b := by
      rw [hb]
      exact denseKey_eval_base_eq L L0 hkey denv
    have hcast : off i = L.const := by
      simp only [hofff, ho]
    rw [hcast]
    linear_combination hbase
  have hbs : ∀ i : Fin k, tsSlotVal tsField (send i) < B :=
    fun i => hsend_ts (sends[i.val]'i.isLt) (List.getElem_mem _)
  -- gadget: recv i < send i
  have hlt : ∀ i : Fin k, tsSlotVal tsField (recv i) < tsSlotVal tsField (send i) := by
    intro i
    have hzip : (sends.zip recvs)[i.val]? = some (sends[i.val]'i.isLt,
        recvs[i.val]'(hrecb i)) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩,
        List.getElem?_eq_some_iff.mpr ⟨hrecb i, rfl⟩⟩
    have hmemz := List.mem_of_getElem? hzip
    have hok := List.all_eq_true.mp hgad _ hmemz
    exact denseBUGadgetOk_sound bs facts d idx tsField B _ _ hok denv hsat
      (hrecv_ts (recvs[i.val]'(hrecb i)) (List.getElem_mem _))
  -- the copies
  have hcopies := admissibleMemoryBusM_copies_of_steps shape M A hp30 hM send recv hsendP hrecvP
    tsField B hB29 b off hts hbs hstep hlt
  -- read off the emitted equalities
  intro c hc
  unfold denseBUGroupEqs at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨sr, hsr, hcm⟩ := hc
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hsr
  have hizip : i < sends.length ∧ i < recvs.tail.length := by
    rw [List.length_zip] at hilt
    omega
  have hgetS : (sends.zip recvs.tail)[i] = (sends[i]'hizip.1, recvs.tail[i]'hizip.2) :=
    List.getElem_zip ..
  have htail : recvs.tail[i]'hizip.2 = recvs[i + 1]'(by
      have := hizip.2
      rw [List.length_tail] at this
      omega) := by
    rw [List.getElem_tail]
  have hi1k : i + 1 < k := by
    have := hizip.2
    rw [List.length_tail] at this
    omega
  have hpay : (recv ⟨i + 1, hi1k⟩).payload
      = (send ⟨(i + 1) - 1, Nat.lt_of_le_of_lt (Nat.sub_le (i + 1) 1) hi1k⟩).payload :=
    hcopies ⟨i + 1, hi1k⟩ (by simp)
  have hidx : ((⟨(i + 1) - 1, Nat.lt_of_le_of_lt (Nat.sub_le (i + 1) 1) hi1k⟩ : Fin k))
      = (⟨i, by omega⟩ : Fin k) := by
    ext
    simp
  rw [hidx] at hpay
  -- sr = (sends[i], recvs[i+1])
  rw [← hget, hgetS] at hcm
  simp only at hcm
  rw [htail] at hcm
  -- evaluate the constraint
  unfold denseMemEqConstraints at hcm
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hcm
  rw [denseEqExpr_eval]
  have hPQ : (recvs[i + 1]'(by omega)).payload.map (fun e => e.eval denv)
      = (sends[i]'hizip.1).payload.map (fun e => e.eval denv) := hpay
  rw [densePayloadSlot_eval_eq _ _ denv hPQ t, sub_self]

/-! ## From the emitted equalities back to a verified group -/

/-- Each entry of the bus split is a declared memory bus with exactly its interactions. -/
theorem denseBUBusLists_mem {memShape : Nat → Option MemoryBusShape}
    {bis : List (BusInteraction (DenseExpr p))} {e : Nat × MemoryBusShape ×
      List (BusInteraction (DenseExpr p))} (h : e ∈ denseBUBusLists memShape bis) :
    memShape e.1 = some e.2.1 ∧ e.2.2 = bis.filter (fun bi => bi.busId = e.1) := by
  unfold denseBUBusLists at h
  obtain ⟨busId, _, hmap⟩ := List.mem_filterMap.1 h
  cases hms : memShape busId with
  | none => rw [hms] at hmap; exact absurd hmap (by simp)
  | some shape =>
    rw [hms] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    subst hmap
    exact ⟨hms, rfl⟩

/-- The structure of an emitted equality: a declared bus with a declared ts slot, and a verified
    group on it containing the equality. -/
theorem denseBUEqs_mem (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    {c : DenseExpr p} (hc : c ∈ denseBUEqs bs facts d) :
    ∃ busId shape tsField B pos sends recvs,
      facts.memShape busId = some shape ∧
      facts.memTsField busId = some (tsField, B) ∧
      denseBUGroupPairs? bs facts
        (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B d.busInteractions
        (denseBUBuildIdx bs facts d.busInteractions)
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape
            (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d) bi))) pos
        = some (sends, recvs) ∧
      c ∈ denseBUGroupEqs shape sends recvs := by
  rw [show denseBUEqs bs facts d
      = (if (denseBUBusLists facts.memShape d.busInteractions).isEmpty then []
         else denseBUEqsOf bs facts (denseBUBusLists facts.memShape d.busInteractions) d)
    from rfl] at hc
  split at hc
  · simp at hc
  · rw [show denseBUEqsOf bs facts (denseBUBusLists facts.memShape d.busInteractions) d
        = ((denseBUBusLists facts.memShape d.busInteractions).map (fun sl =>
            match facts.memTsField sl.1 with
            | some (tsField, B) =>
              denseBUForBus bs facts denseZModOps
                (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
                (denseBUWits d) sl.2.1 tsField B d.busInteractions
                (denseBUBuildIdx bs facts d.busInteractions) sl.2.2
            | none => [])).flatten from rfl,
      List.mem_flatten] at hc
    obtain ⟨l, hl, hcl⟩ := hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hms, hfilter⟩ := denseBUBusLists_mem he
    cases htf : facts.memTsField e.1 with
    | none => rw [htf] at hcl; simp at hcl
    | some tB =>
        obtain ⟨tsField, B⟩ := tB
        rw [htf] at hcl
        unfold denseBUForBus at hcl
        rw [List.mem_flatMap] at hcl
        obtain ⟨pos, -, hcp⟩ := hcl
        cases hgp : denseBUGroupPairs? bs facts (denseBUWits d)
            (denseSetNewMult denseZModOps e.2.1) (denseGetPreviousMult denseZModOps e.2.1)
            tsField B d.busInteractions (denseBUBuildIdx bs facts d.busInteractions)
            (e.2.2.map (fun bi => (bi, denseBUPrep e.2.1
              (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d) bi))) pos with
        | none => rw [hgp] at hcp; simp at hcp
        | some sr =>
            obtain ⟨sends, recvs⟩ := sr
            rw [hgp] at hcp
            rw [hfilter] at hgp
            exact ⟨e.1, e.2.1, tsField, B, pos, sends, recvs, hms, htf, hgp, hcp⟩

/-! ## The appended constraints -/

theorem denseBUFilterNew_subset (d : DenseConstraintSystem p) (eqs : List (DenseExpr p))
    {c : DenseExpr p} (h : c ∈ denseBUFilterNew d eqs) : c ∈ eqs :=
  List.mem_of_mem_filter h

theorem denseBusUnifyNewCs_subset (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) {c : DenseExpr p} (h : c ∈ denseBusUnifyNewCs bs facts d) :
    c ∈ denseBUEqs bs facts d := by
  rw [show denseBusUnifyNewCs bs facts d
      = (if (denseBUEqs bs facts d).isEmpty then []
         else denseBUFilterNew d (denseBUEqs bs facts d)) from rfl] at h
  split at h
  · simp at h
  · exact denseBUFilterNew_subset d _ h

/-- The members of a verified group are interactions of `d`. -/
private theorem denseBUGroupPairs?_mem_bis {bs : BusSemantics p} {facts : BusFacts p bs}
    {d : DenseConstraintSystem p} {shape : MemoryBusShape} {T : DenseTwoRootMap p}
    {busId tsField B pos : Nat} {sends recvs : List (BusInteraction (DenseExpr p))}
    (idx : DenseBUIdx)
    (hgrp : denseBUGroupPairs? bs facts (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B d.busInteractions idx
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape T bi))) pos = some (sends, recvs)) :
    (∀ S ∈ sends, S ∈ d.busInteractions) ∧ (∀ R ∈ recvs, R ∈ d.busInteractions) := by
  cases hlp : ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => (bi, denseBUPrep shape T bi)))[pos]? with
  | none => simp [denseBUGroupPairs?, hlp] at hgrp
  | some lp =>
  cases hsplit : denseBUSplit (denseBUWits d) (denseSetNewMult denseZModOps shape)
      (denseGetPreviousMult denseZModOps shape) lp.2
      ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
        (fun bi => (bi, denseBUPrep shape T bi))) with
  | none => simp [denseBUGroupPairs?, hlp, hsplit] at hgrp
  | some sr =>
  obtain ⟨s', r'⟩ := sr
  simp only [denseBUGroupPairs?, hlp, hsplit] at hgrp
  split at hgrp
  case isFalse => simp at hgrp
  split at hgrp
  case isFalse => simp at hgrp
  simp only [Option.some.injEq, Prod.mk.injEq] at hgrp
  obtain ⟨rfl, rfl⟩ : sends = s' ∧ recvs = r' := ⟨hgrp.1.symm, hgrp.2.symm⟩
  constructor
  · intro S hS
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_sends hsplit S hS
    obtain ⟨S', hS', heq⟩ := List.mem_map.mp hmem
    rw [show S' = S from congrArg Prod.fst heq] at hS'
    exact List.mem_of_mem_filter hS'
  · intro R hR
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_recvs hsplit R hR
    obtain ⟨R', hR', heq⟩ := List.mem_map.mp hmem
    rw [show R' = R from congrArg Prod.fst heq] at hR'
    exact List.mem_of_mem_filter hR'

/-- The variables of an emitted equality occur in `d`. -/
theorem denseBusUnifyNewCs_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseBusUnifyNewCs bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨busId, shape, tsField, B, pos, sends, recvs, -, -, hgrp, hmem⟩ :=
    denseBUEqs_mem bs facts d (denseBusUnifyNewCs_subset bs facts d hc)
  obtain ⟨hsend_mem, hrecv_mem⟩ := denseBUGroupPairs?_mem_bis _ hgrp
  unfold denseBUGroupEqs at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨sr, hsr, hcm⟩ := hmem
  have hS : sr.1 ∈ sends := (List.of_mem_zip hsr).1
  have hR : sr.2 ∈ recvs.tail := (List.of_mem_zip hsr).2
  rcases denseMemEqConstraints_vars shape sr.1 sr.2 hcm hz with ⟨e, he, hze⟩ | ⟨e, he, hze⟩
  · exact DenseConstraintSystem.mem_occ_of_payload
      (hrecv_mem sr.2 (List.mem_of_mem_tail hR)) he hze
  · exact DenseConstraintSystem.mem_occ_of_payload (hsend_mem sr.1 hS) he hze

theorem denseBusUnifyNewCs_sound (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusUnifyNewCs bs facts d, c.eval denv = 0 := by
  intro c hc
  obtain ⟨busId, shape, tsField, B, pos, sends, recvs, hms, htf, hgrp, hmem⟩ :=
    denseBUEqs_mem bs facts d (denseBusUnifyNewCs_subset bs facts d hc)
  exact denseBUGroupPairs?_sound bs facts reg d hcov busId shape hms tsField B htf
    _ (denseBUTable_sound (denseBUBusLists facts.memShape d.busInteractions) d)
    pos sends recvs (denseBUBuildIdx bs facts d.busInteractions) hgrp denv hadm hsat c hmem

/-! ## The pass transform: correctness and coverage -/

/-- The `let`-bound body, unfolded (definitionally). -/
theorem denseBusUnifyF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseBusUnifyF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseBusUnifyNewCs bs facts d).isEmpty then d
         else { d with algebraicConstraints :=
                  d.algebraicConstraints ++ denseBusUnifyNewCs bs facts d })
       else d) := rfl

theorem denseBusUnifyF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBusUnifyF bs facts d).CoveredBy reg := by
  rw [denseBusUnifyF_eq]
  split_ifs with hp1 _hempty
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h | h
    · exact hcov.1 e h
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseBusUnifyNewCs_vars bs facts d e h i hi)
  · exact hcov

theorem denseBusUnifyF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBusUnifyF bs facts d) [] bs := by
  rw [denseBusUnifyF_eq]
  split_ifs with hp1 _hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseBusUnifyNewCs bs facts d)
      (denseBusUnifyNewCs_vars bs facts d)
      (fun denv hadm hsat => denseBusUnifyNewCs_sound bs facts reg d hcov denv hadm hsat)
  · exact DensePassCorrect.refl reg.isInput d bs

/-! ## The dense `busUnify` pass -/

/-- The dense `busUnify` pass (see `denseBusUnifyF`). -/
def denseBusUnifyPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseBusUnifyF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseBusUnifyF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseBusUnifyF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
