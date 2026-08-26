import ApcOptimizer.VmSpec.Audit.PlaceCheck
import ApcOptimizer.VmSpec.Audit.OpenVmLegalAudit

set_option autoImplicit false

/-! **A static check for `StepLayout.sendsOk`, OpenVM's byte invariant.**

    `sendsOk` asks that what a chip sends on a stateful bus be `payloadOk` — for OpenVM, that a
    memory record's four data limbs are bytes — given that everything the chip already touched is.

    Real chips justify a send in a small number of ways, and this file decides four of them:

    * the interaction is not a send at all, so there is nothing to ask;
    * it is not on the memory bus, where `openVmPayloadOk` asks nothing;
    * its data limbs are literal bytes (a fresh write of zeros);
    * its data limbs are those of an *earlier* interaction, so `sendsOk`'s own hypothesis supplies
      them — a memory send echoing the read it just did.

    A fifth is left to the caller (`external`): a limb that is a byte because a lookup table says
    so, which is where a VM's own arithmetic enters and a decidable check stops. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

--------- The memory-record shape ---------

/-- A normalized payload in OpenVM's memory shape `(addr_space, ptr, d₀…d₃, t)`, with the address
    space pinned to `1`. -/
def memShape : List (LinForm p) → Bool
  | [f0, _, _, _, _, _, _] => f0.isConst 1
  | _ => false

/-- Its four data limbs. -/
def dataLimbs : List (LinForm p) → List (LinForm p)
  | [_, _, f2, f3, f4, f5, _] => [f2, f3, f4, f5]
  | _ => []

/-- Whether a form is a literal byte. -/
def isByteConst (f : LinForm p) : Bool :=
  f.coefs.all (· == 0) && decide (f.const.val < 256)

theorem isByte_of_isByteConst {vs : List Variable} {asg : Variable → ZMod p} {f : LinForm p}
    (h : isByteConst f = true) : isByte (f.eval vs asg) := by
  simp only [isByteConst, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [LinForm.eval_of_coefs_zero vs f asg h.1]
  exact h.2

/-- What a payload in memory shape evaluates to. -/
theorem memShape_eval {vs : List Variable} {rules : List (PinRule p)} {asg : ChipAssignment p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {es : List (Expression p)} {pl : List (LinForm p)}
    (hpl : payloadLin vs rules es = some pl) (hshape : memShape pl = true) :
    ∃ (ptr ts : ZMod p) (d0 d1 d2 d3 : LinForm p),
      dataLimbs pl = [d0, d1, d2, d3] ∧
      es.map (fun e => e.eval asg)
        = [1, ptr, d0.eval vs asg, d1.eval vs asg, d2.eval vs asg, d3.eval vs asg, ts] := by
  match pl, hshape with
  | [f0, f1, f2, f3, f4, f5, f6], hshape =>
    refine ⟨f1.eval vs asg, f6.eval vs asg, f2, f3, f4, f5, rfl, ?_⟩
    rw [payloadLin_eval hrules hpl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    simp only [memShape, LinForm.isConst, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hshape
    rw [LinForm.eval_of_coefs_zero vs f0 asg (by simpa using hshape.2), hshape.1]

--------- Witnesses ---------

/-- Why one interaction's payload is Ok. -/
inductive ByteWitness where
  /-- It is not a stateful send — its bus is a lookup, or its multiplicity is not `1` — so
      `sendsOk` asks nothing of it. -/
  | notSend
  /-- It is not on the memory bus, where `openVmPayloadOk` asks nothing. -/
  | notMemory
  /-- Its four data limbs are literal bytes. -/
  | limbs
  /-- Its data limbs are those of interaction `j`, which precedes it and is active — so
      `sendsOk`'s own hypothesis already vouches for them. -/
  | echo (j : ℕ)
  /-- The caller proves it. -/
  | external
  deriving DecidableEq, Repr

/-- Whether a multiplicity expression folds to something other than `1`. -/
def multNotOne (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => !(v == 1)
  | none => false

/-- Whether it folds to something other than `0`. -/
def multNotZero (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => !(v == 0)
  | none => false

/-- Check one interaction against its witness. -/
def byteCheckOne (vs : List Variable) (rules : List (PinRule p))
    (L : List (BusInteraction (Expression p))) (i : ℕ)
    (bi : BusInteraction (Expression p)) (w : ByteWitness) : Bool :=
  match w with
  | .notSend => multNotOne rules bi || !openVmIsStateful defaultBusMap bi.busId
  | .notMemory => !(bi.busId == openVmMemBusId)
  | .limbs =>
    (bi.busId == openVmMemBusId) &&
      (match payloadLin vs rules bi.payload with
       | some pl => memShape pl && (dataLimbs pl).all isByteConst
       | none => false)
  | .echo j =>
    (bi.busId == openVmMemBusId) && decide (j < i) &&
      (match L[j]? with
       | none => false
       | some bj =>
         (bj.busId == openVmMemBusId) && multNotZero rules bj &&
           (match payloadLin vs rules bi.payload, payloadLin vs rules bj.payload with
            | some pli, some plj =>
              memShape pli && memShape plj && (dataLimbs pli == dataLimbs plj)
            | _, _ => false))
  | .external => true

/-- Check every interaction against its witness, walking both lists together (as `placeCheckAll`
    does) rather than re-indexing `L`/`W` from scratch at every position. -/
def byteCheckAllFrom (vs : List Variable) (rules : List (PinRule p))
    (full : List (BusInteraction (Expression p))) (i : ℕ) :
    List (BusInteraction (Expression p)) → List ByteWitness → Bool
  | [], _ => true
  | _ :: _, [] => false
  | bi :: lt, w :: wt =>
    byteCheckOne vs rules full i bi w && byteCheckAllFrom vs rules full (i + 1) lt wt

def byteCheckAll (vs : List Variable) (rules : List (PinRule p))
    (L : List (BusInteraction (Expression p))) (W : List ByteWitness) : Bool :=
  byteCheckAllFrom vs rules L 0 L W

theorem byteCheckAllFrom_get {vs : List Variable} {rules : List (PinRule p)}
    {full : List (BusInteraction (Expression p))} :
    ∀ {i : ℕ} {L : List (BusInteraction (Expression p))} {W : List ByteWitness},
      byteCheckAllFrom vs rules full i L W = true →
      ∀ k : Fin L.length,
        byteCheckOne vs rules full (i + k.val) (L.get k) (W.getD k.val .notSend) = true := by
  intro i L
  induction L generalizing i with
  | nil => intro W _ k; exact absurd k.isLt (by simp)
  | cons bi bt ih =>
    intro W h k
    match W with
    | [] => simp only [byteCheckAllFrom] at h; cases h
    | w :: wt =>
      simp only [byteCheckAllFrom, Bool.and_eq_true] at h
      match k with
      | ⟨0, _⟩ => exact h.1
      | ⟨j + 1, hj⟩ =>
        have hk := ih h.2 ⟨j, by simpa using hj⟩
        have heq : i + (j + 1) = i + 1 + j := by omega
        rwa [heq]

theorem byteCheckAll_get {vs : List Variable} {rules : List (PinRule p)}
    {L : List (BusInteraction (Expression p))} {W : List ByteWitness}
    (h : byteCheckAll vs rules L W = true) (i : Fin L.length) :
    byteCheckOne vs rules L i.val (L.get i) (W.getD i.val .notSend) = true := by
  simpa using byteCheckAllFrom_get h i

--------- Soundness ---------

/-- **Soundness of the byte check.** A `true` witness turns `sendsOk`'s hypothesis into its
    conclusion, for every justification except `external`, which the caller supplies. -/
theorem byteCheckOne_sound [Fact (1 < p)] {vs : List Variable} {rules : List (PinRule p)}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {c : Circuit p} {i : Fin c.busInteractions.length} {w : ByteWitness}
    (h : byteCheckOne vs rules c.busInteractions i.val (c.busInteractions.get i) w = true)
    (hsend : c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i)
    (hlow : ∀ j : Fin c.busInteractions.length, j < i →
      c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
      openVmPayloadOk defaultBusMap (c.msgAt asg j))
    (hext : w = .external → openVmPayloadOk defaultBusMap (c.msgAt asg i)) :
    openVmPayloadOk defaultBusMap (c.msgAt asg i) := by
  have hbus : (c.msgAt asg i).1 = (c.busInteractions.get i).busId := rfl
  cases hw : w with
  | external => exact hext hw
  | notSend =>
    exfalso
    rw [hw] at h
    simp only [byteCheckOne, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · simp only [multNotOne] at h
      cases hm : (c.busInteractions.get i).multiplicity.foldConstWith rules with
      | none => rw [hm] at h; cases h
      | some v =>
        rw [hm] at h
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
        exact h ((Expression.foldConstWith_eq hrules hm).symm.trans hsend.2)
    · exact absurd hsend.1 (by simp only [openVmGuestRules]; rw [h]; simp)
  | notMemory =>
    rw [hw] at h
    simp only [byteCheckOne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
    rcases openVmIsStateful_default hsend.1 with hmem | hexec
    · exact absurd hmem h
    · have : (c.msgAt asg i).1 = openVmExecBusId := hbus.trans hexec
      simp only [openVmPayloadOk, this, openVmExecBusId, defaultBusMap]
  | limbs =>
    rw [hw] at h
    simp only [byteCheckOne, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hmem, h⟩ := h
    cases hpl : payloadLin vs rules (c.busInteractions.get i).payload with
    | none => rw [hpl] at h; cases h
    | some pl =>
      rw [hpl] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨ptr, ts, d0, d1, d2, d3, hdl, hev⟩ := memShape_eval hrules hpl h.1
      rw [hdl] at h
      simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at h
      have hmsg : c.msgAt asg i
          = ((1 : ℕ), [(1 : ZMod p), ptr, d0.eval vs asg, d1.eval vs asg, d2.eval vs asg,
              d3.eval vs asg, ts]) := by
        rw [Circuit.msgAt]
        exact Prod.ext hmem hev
      rw [hmsg]
      exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
        ⟨isByte_of_isByteConst h.2.1, isByte_of_isByteConst h.2.2.1,
         isByte_of_isByteConst h.2.2.2.1, isByte_of_isByteConst h.2.2.2.2.1⟩
  | echo j =>
    rw [hw] at h
    simp only [byteCheckOne, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hmem, hji⟩, h⟩ := h
    cases hbj : c.busInteractions[j]? with
    | none => rw [hbj] at h; cases h
    | some bj =>
      rw [hbj] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hbjmem, hbjmult⟩, h⟩ := h
      cases hpli : payloadLin vs rules (c.busInteractions.get i).payload with
      | none => rw [hpli] at h; cases h
      | some pli =>
        cases hplj : payloadLin vs rules bj.payload with
        | none => rw [hpli, hplj] at h; cases h
        | some plj =>
          rw [hpli, hplj] at h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hshi, hshj⟩, hdeq⟩ := h
          have hjlt : j < c.busInteractions.length := by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at hbj; cases hbj
          have hget : c.busInteractions.get ⟨j, hjlt⟩ = bj := by
            rw [List.get_eq_getElem, ← Option.some_inj, ← List.getElem?_eq_getElem hjlt, hbj]
          -- The earlier interaction is active, so `sendsOk`'s hypothesis vouches for it.
          have hmultj : c.multAt asg ⟨j, hjlt⟩ ≠ 0 := by
            cases hm : bj.multiplicity.foldConstWith rules with
            | none => simp only [multNotZero, hm] at hbjmult; cases hbjmult
            | some v =>
              simp only [multNotZero, hm, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hbjmult
              rw [Circuit.multAt, hget]
              exact fun hc => hbjmult ((Expression.foldConstWith_eq hrules hm).symm.trans hc)
          have hactj : c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg
              ⟨j, hjlt⟩ := ⟨by rw [hget, hbjmem]; rfl, hmultj⟩
          have hlowj := hlow ⟨j, hjlt⟩ (Fin.lt_def.mpr hji) hactj
          obtain ⟨ptri, tsi, a0, a1, a2, a3, hdli, hevi⟩ := memShape_eval hrules hpli hshi
          obtain ⟨ptrj, tsj, b0, b1, b2, b3, hdlj, hevj⟩ := memShape_eval hrules hplj hshj
          rw [hdli, hdlj] at hdeq
          simp only [List.cons.injEq, and_true] at hdeq
          obtain ⟨e0, e1, e2, e3⟩ := hdeq
          have hmsgj : c.msgAt asg ⟨j, hjlt⟩
              = ((1 : ℕ), [(1 : ZMod p), ptrj, b0.eval vs asg, b1.eval vs asg, b2.eval vs asg,
                  b3.eval vs asg, tsj]) := by
            rw [Circuit.msgAt, hget]
            exact Prod.ext hbjmem hevj
          have hmsgi : c.msgAt asg i
              = ((1 : ℕ), [(1 : ZMod p), ptri, a0.eval vs asg, a1.eval vs asg, a2.eval vs asg,
                  a3.eval vs asg, tsi]) := by
            rw [Circuit.msgAt]
            exact Prod.ext hmem hevi
          rw [hmsgj] at hlowj
          rw [hmsgi, e0, e1, e2, e3]
          exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
            ((openVmPayloadOk_mem_iff _ _ _ _ _ _).mp hlowj)

/-- **`StepLayout.sendsOk`, from the witnesses.** Everything the check decides is discharged; the
    `external` indices are left to the caller, and for every other index that hypothesis is
    decidably vacuous. -/
theorem byteCheck_sendsOk [Fact (1 < p)] {vs : List Variable} {rules : List (PinRule p)}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {c : Circuit p} {W : List ByteWitness}
    (h : byteCheckAll vs rules c.busInteractions W = true)
    (hext : ∀ i : Fin c.busInteractions.length, W.getD i.val .notSend = .external →
      c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i →
      (∀ j : Fin c.busInteractions.length, j < i →
        c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
        openVmPayloadOk defaultBusMap (c.msgAt asg j)) →
      openVmPayloadOk defaultBusMap (c.msgAt asg i)) :
    ∀ i : Fin c.busInteractions.length,
      c.statefulSend (openVmGuestRules defaultBusMap openVmMemBusId) asg i →
      (∀ j : Fin c.busInteractions.length, j < i →
        c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg j →
        openVmPayloadOk defaultBusMap (c.msgAt asg j)) →
      openVmPayloadOk defaultBusMap (c.msgAt asg i) := fun i hsend hlow =>
  byteCheckOne_sound hrules (byteCheckAll_get h i) hsend hlow (fun hw => hext i hw hsend hlow)

end ApcOptimizer.OpenVM
