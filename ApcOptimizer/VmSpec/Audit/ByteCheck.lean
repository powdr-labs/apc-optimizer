import ApcOptimizer.VmSpec.Audit.PlaceCheck
import ApcOptimizer.VmSpec.Audit.OpenVmShapes

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

/-- Whether a form is a literal address space whose words OpenVM byte-range-checks: registers
    (`1`) or main memory (`2`), the two `MemoryPayload.isByteChecked` names. -/
def isByteCheckedConst (f : LinForm p) : Bool :=
  f.coefs.all (· == 0) && (f.const.val == 1 || f.const.val == 2)

/-- A payload in OpenVM's memory shape `(addr_space, ptr, d₀…d₃, t)`, normalized *only where this
    file reads it* — the address space and the four data limbs — and returning the two.

    The pointer and the timestamp are deliberately left as raw expressions. Normalizing a field no
    clause here inspects would reject records for no reason: a byte load's pointer is quadratic in
    its own selector flags (`Apcs/TwoLoads/`), so a whole-payload normalization fails on it while
    every field this check actually uses is linear. -/
def memShapeLin (vs : List Variable) (rules : List (PinRule p)) :
    List (Expression p) → Option (LinForm p × List (LinForm p))
  | [e0, _, e2, e3, e4, e5, _] =>
    match payloadLin vs rules [e0, e2, e3, e4, e5] with
    | some [f0, f2, f3, f4, f5] => some (f0, [f2, f3, f4, f5])
    | _ => none
  | _ => none

/-- Whether a form is a literal byte. -/
def isByteConst (f : LinForm p) : Bool :=
  f.coefs.all (· == 0) && decide (f.const.val < 256)

theorem isByte_of_isByteConst {vs : List Variable} {asg : Variable → ZMod p} {f : LinForm p}
    (h : isByteConst f = true) : isByte (f.eval vs asg) := by
  simp only [isByteConst, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [LinForm.eval_of_coefs_zero vs f asg h.1]
  exact h.2

/-- What a payload in memory shape evaluates to, and that its address space is one
    `openVmPayloadOk` asks about. -/
theorem memShapeLin_eval {vs : List Variable} {rules : List (PinRule p)} {asg : ChipAssignment p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {es : List (Expression p)} {f0 : LinForm p}
    {ds : List (LinForm p)}
    (hpl : memShapeLin vs rules es = some (f0, ds)) (hshape : isByteCheckedConst f0 = true) :
    ∃ (ptr ts : ZMod p) (d0 d1 d2 d3 : LinForm p),
      ds = [d0, d1, d2, d3] ∧ (f0.const.val = 1 ∨ f0.const.val = 2) ∧
      es.map (fun e => e.eval asg)
        = [f0.const, ptr, d0.eval vs asg, d1.eval vs asg, d2.eval vs asg, d3.eval vs asg, ts] := by
  simp only [isByteCheckedConst, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hshape
  match es, hpl with
  | [e0, e1, e2, e3, e4, e5, e6], hpl =>
    simp only [memShapeLin] at hpl
    cases hp : payloadLin vs rules [e0, e2, e3, e4, e5] with
    | none => rw [hp] at hpl; cases hpl
    | some l =>
      rw [hp] at hpl
      match l, hpl with
      | [g0, g2, g3, g4, g5], hpl =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hpl
        obtain ⟨rfl, rfl⟩ := hpl
        have hev := payloadLin_eval hrules hp
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hev
        obtain ⟨h0, h2, h3, h4, h5⟩ := hev
        refine ⟨e1.eval asg, e6.eval asg, g2, g3, g4, g5, rfl, hshape.2, ?_⟩
        simp only [List.map_cons, List.map_nil]
        rw [h0, h2, h3, h4, h5, LinForm.eval_of_coefs_zero vs g0 asg hshape.1]

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

/-- Check one interaction against its witness. -/
def byteCheckOne (vs : List Variable) (rules : List (PinRule p))
    (L : List (BusInteraction (Expression p))) (i : ℕ)
    (bi : BusInteraction (Expression p)) (w : ByteWitness) : Bool :=
  match w with
  | .notSend => multNotOne rules bi || !openVmIsStateful defaultBusMap bi.busId
  | .notMemory => !(bi.busId == openVmMemBusId)
  | .limbs =>
    (bi.busId == openVmMemBusId) &&
      (match memShapeLin vs rules bi.payload with
       | some (f0, ds) => isByteCheckedConst f0 && ds.all isByteConst
       | none => false)
  | .echo j =>
    (bi.busId == openVmMemBusId) && decide (j < i) &&
      (match L[j]? with
       | none => false
       | some bj =>
         (bj.busId == openVmMemBusId) && multNotZero rules bj &&
           (match memShapeLin vs rules bi.payload, memShapeLin vs rules bj.payload with
            | some (f0i, dsi), some (f0j, dsj) =>
              isByteCheckedConst f0i && isByteCheckedConst f0j && (dsi == dsj)
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
    cases hpl : memShapeLin vs rules (c.busInteractions.get i).payload with
    | none => rw [hpl] at h; cases h
    | some fd =>
      obtain ⟨f0, ds⟩ := fd
      rw [hpl] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨ptr, ts, d0, d1, d2, d3, hdl, hasp, hev⟩ := memShapeLin_eval hrules hpl h.1
      rw [hdl] at h
      simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at h
      have hmsg : c.msgAt asg i
          = ((1 : ℕ), [f0.const, ptr, d0.eval vs asg, d1.eval vs asg, d2.eval vs asg,
              d3.eval vs asg, ts]) := by
        rw [Circuit.msgAt]
        exact Prod.ext hmem hev
      rw [hmsg]
      exact (openVmPayloadOk_mem_iff_of_byteChecked hasp _ _ _ _ _ _).mpr
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
      cases hpli : memShapeLin vs rules (c.busInteractions.get i).payload with
      | none => rw [hpli] at h; cases h
      | some fdi =>
        obtain ⟨f0i, dsi⟩ := fdi
        cases hplj : memShapeLin vs rules bj.payload with
        | none => rw [hpli, hplj] at h; cases h
        | some fdj =>
          obtain ⟨f0j, dsj⟩ := fdj
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
          obtain ⟨ptri, tsi, a0, a1, a2, a3, hdli, haspi, hevi⟩ :=
            memShapeLin_eval hrules hpli hshi
          obtain ⟨ptrj, tsj, b0, b1, b2, b3, hdlj, haspj, hevj⟩ :=
            memShapeLin_eval hrules hplj hshj
          rw [hdli, hdlj] at hdeq
          simp only [List.cons.injEq, and_true] at hdeq
          obtain ⟨e0, e1, e2, e3⟩ := hdeq
          have hmsgj : c.msgAt asg ⟨j, hjlt⟩
              = ((1 : ℕ), [f0j.const, ptrj, b0.eval vs asg, b1.eval vs asg, b2.eval vs asg,
                  b3.eval vs asg, tsj]) := by
            rw [Circuit.msgAt, hget]
            exact Prod.ext hbjmem hevj
          have hmsgi : c.msgAt asg i
              = ((1 : ℕ), [f0i.const, ptri, a0.eval vs asg, a1.eval vs asg, a2.eval vs asg,
                  a3.eval vs asg, tsi]) := by
            rw [Circuit.msgAt]
            exact Prod.ext hmem hevi
          rw [hmsgj] at hlowj
          rw [hmsgi, e0, e1, e2, e3]
          exact (openVmPayloadOk_mem_iff_of_byteChecked haspi _ _ _ _ _ _).mpr
            ((openVmPayloadOk_mem_iff_of_byteChecked haspj _ _ _ _ _ _).mp hlowj)

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
