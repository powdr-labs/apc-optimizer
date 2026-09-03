import ApcOptimizer.VmSpec.OpenVm
import ApcOptimizer.VmSpec.Implementation.Connection
import ApcOptimizer.VmSpec.OrderFree

set_option autoImplicit false
set_option maxRecDepth 8000

/-! # Is `Host.forcesAdmissible` true of `openVmHost`?

    Scratch file: a candidate counterexample. -/

namespace ApcOptimizer.OpenVM.AdmissibleGap

open ApcOptimizer.OpenVM

/-- A constant bus interaction. -/
def kc (bid : Nat) (mult : ZMod babyBear) (pl : List (ZMod babyBear)) :
    BusInteraction (Expression babyBear) :=
  { busId := bid, multiplicity := .const mult, payload := pl.map Expression.const }

/-- A guest chip with **no variables and no constraints**: it receives `(pc 0, t 1)` on the
    execution bridge, hands on `(pc 1, t 4)`, and makes two accesses to main-memory cell
    `(2, 7)` — reading the record `(1,0,0,0)` stamped `0` and writing it back at `2`, then
    reading the record `(2,0,0,0)` *also* stamped `0` and writing it back at `3`.

    The second read is stale: it reaches past the write this very instance made at `2`. -/
def badChip : Circuit babyBear where
  algebraicConstraints := []
  busInteractions :=
    [ kc 0 (-1) [0, 1]
    , kc 0 1 [1, 4]
    , kc 1 (-1) [2, 7, 1, 0, 0, 0, 0]
    , kc 1 1 [2, 7, 1, 0, 0, 0, 2]
    , kc 1 (-1) [2, 7, 2, 0, 0, 0, 0]
    , kc 1 1 [2, 7, 2, 0, 0, 0, 3] ]

abbrev bs : BusSemantics babyBear := openVmBusSemantics babyBear defaultBusMap

/-- The memory shape `defaultBusMap` gives bus `1`. -/
theorem memShape_one :
    memShapeOf defaultBusMap 1 = some { addressFields := [0, 1], direction := .receiveThenSend } :=
  rfl

/-- The bus-1 messages `badChip` writes, in order. -/
theorem badChip_memMsgs (asg : ChipAssignment babyBear) :
    ((badChip.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)).filter
      (fun m => m.busId = 1)
    = [ { busId := 1, multiplicity := -1, payload := [2, 7, 1, 0, 0, 0, 0] },
        { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] },
        { busId := 1, multiplicity := -1, payload := [2, 7, 2, 0, 0, 0, 0] },
        { busId := 1, multiplicity := 1, payload := [2, 7, 2, 0, 0, 0, 3] } ] := by
  rfl

/-- **`badChip` has no admissible assignment.** Its second memory read reaches back past its own
    first write to the same cell, which is exactly what `admissibleMemoryBus` forbids. -/
theorem badChip_not_admissible (asg : ChipAssignment babyBear) :
    ¬ badChip.admissible bs asg := by
  rintro ⟨h1, -⟩
  have hmem := h1 1 _ memShape_one
  rw [badChip_memMsgs asg] at hmem
  have := hmem [{ busId := 1, multiplicity := -1, payload := [2, 7, 1, 0, 0, 0, 0] }] []
    [{ busId := 1, multiplicity := 1, payload := [2, 7, 2, 0, 0, 0, 3] }]
    { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] }
    { busId := 1, multiplicity := -1, payload := [2, 7, 2, 0, 0, 0, 0] }
    rfl rfl rfl rfl (by simp)
  exact absurd this (by decide)

--------- Legality ---------

abbrev rr : GuestBusRules babyBear := openVmGuestRules defaultBusMap openVmMemBusId

/-- Where each interaction sits, as an integer offset from `tStart = 1`. -/
def offs : List ℤ := [0, 3, -1, 1, -1, 2]

theorem negOne_ne_one : ¬((-1 : ZMod babyBear) = 1) := by decide
theorem oneNeNegOne : ¬((1 : ZMod babyBear) = -1) := by decide
theorem negOne_ne_zero : ¬((-1 : ZMod babyBear) = 0) := by decide

/-- Every payload `badChip` writes is `payloadOk`: the two memory sends carry byte data. -/
theorem badChip_payloadOk (asg : ChipAssignment babyBear)
    (i : Fin badChip.busInteractions.length) : rr.payloadOk (badChip.msgAt asg i) := by
  fin_cases i
  · exact trivial
  · exact trivial
  all_goals
    show (2 : ZMod babyBear).val = 1 ∨ (2 : ZMod babyBear).val = 2 → _
    intro _ d hd
    simp [Expression.eval] at hd
    rcases hd with rfl | rfl <;> · simp only [isByte]; decide

/-- The (irrelevant) assignment the run gives its single `badChip` instance. -/
def asg0 : ChipAssignment babyBear := fun _ => 0

/-! `badChip` and `badChip2` are variable-free, so their messages do not depend on the assignment.
    Stating that lets the layout proofs `decide` closed terms — `rfl` on a `ZMod babyBear` equation
    makes the kernel unfold the modulus into successor form and blow the stack. -/

theorem badChip_mult_eq (asg : ChipAssignment babyBear)
    (i : Fin badChip.busInteractions.length) : badChip.multAt asg i = badChip.multAt asg0 i := by fin_cases i <;> rfl

theorem badChip_msg_eq (asg : ChipAssignment babyBear)
    (i : Fin badChip.busInteractions.length) : badChip.msgAt asg i = badChip.msgAt asg0 i := by fin_cases i <;> rfl

/-- **`badChip` lays out as one instruction step.** -/
def badChipLayout (P : OpenVmParams babyBear) (asg : ChipAssignment babyBear) :
    StepLayout badChip rr asg openVmMemAddress P.maxWindow openVmTimestampBound where
  pcFrom := 0
  pcTo := 1
  tStart := 1
  tWindow := 3
  tWindowPos := by decide
  tWindowLt := P.inputWindowOk
  bridgeRecv := by rfl
  bridgeSend := by rfl
  bridgeNoOther := by
    rintro ⟨b, pl⟩ hb h1 h2
    simp only at hb
    subst hb
    simp only [Prod.mk.injEq, true_and, ne_eq] at h1 h2
    have h2' : ¬ pl = [(1 : ZMod babyBear), 4] := fun h => h2 (by rw [h]; decide)
    have e1 : ¬ (([0, 1] : List (ZMod babyBear)) = pl) := fun h => h1 h.symm
    have e2 : ¬ (([1, 4] : List (ZMod babyBear)) = pl) := fun h => h2' h.symm
    simp [Circuit.allEffects, badChip, kc, BusInteraction.eval, Expression.eval,
      show rr.execBusId = 0 from rfl, e1, e2]
  tOffset := fun i => offs.getD i.val 0
  tOffsetMatch := by
    intro i _
    fin_cases i
    · exact ⟨by decide, by decide, by show (1 : ZMod babyBear) = 1 + ((0 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (4 : ZMod babyBear) = 1 + ((3 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (0 : ZMod babyBear) = 1 + ((-1 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (2 : ZMod babyBear) = 1 + ((1 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (0 : ZMod babyBear) = 1 + ((-1 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (3 : ZMod babyBear) = 1 + ((2 : ℤ) : ZMod babyBear); decide⟩
  memSendsOk := fun i _ _ => badChip_payloadOk asg i
  sendTimesDistinct := by
    intro i j hi hj _ hts
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hi.2 (by decide)
        | exact absurd hj.2 (by decide)
        | exact absurd hi.1.2 negOne_ne_one
        | exact absurd hj.1.2 negOne_ne_one
        | exact absurd hts (by decide)
  negOffsetOnlyMemRecv := by
    intro i _ hlt
    fin_cases i <;> first | exact ⟨rfl, rfl⟩ | exact absurd hlt (by decide)
  sendInWindow := by
    intro i hi
    fin_cases i <;>
      first
        | decide
        | exact absurd hi.2 (by decide)
        | exact absurd hi.1.2 negOne_ne_one
  memPartner := fun i =>
    if i.val = 2 then ⟨3, by decide⟩
    else if i.val = 3 then ⟨2, by decide⟩
    else if i.val = 4 then ⟨5, by decide⟩ else ⟨4, by decide⟩
  memPartner_invol := by
    intro i hi
    fin_cases i <;> first | exact absurd hi (by decide) | exact ⟨rfl, by decide, rfl⟩
  memPartner_mult := by
    intro i hi
    simp only [badChip_mult_eq, badChip_msg_eq]
    fin_cases i <;> first | exact absurd hi (by decide) | exact ⟨by decide, by decide⟩
  memPartner_time := by
    intro i hi hr
    fin_cases i <;>
      first
        | decide
        | exact absurd hi (by decide)
        | exact absurd hr oneNeNegOne

/-- **`badChip` is a legal guest of `openVmHost PP`.** -/
theorem badChip_legalGuest (P : OpenVmParams babyBear) (hI : 6 ≤ P.maxInteractions) :
    (openVmHost P).legalGuest badChip where
  sendOnly := by
    intro asg _ bi hbi hst
    fin_cases hbi <;> exact absurd hst (by decide)
  polarity := by
    intro asg _ bi hbi _
    fin_cases hbi <;> simp [kc, BusInteraction.eval, Expression.eval]
  stepLayout := fun asg _ _ => ⟨badChipLayout P asg⟩
  size := hI
  x0Zero := by
    intro asg _ _ i hs h1
    have hspace : ¬((some 2 : Option (ZMod babyBear)) = some 1) := by decide
    fin_cases i
    · exact absurd hs.2 (by decide)
    · exact absurd hs.2 (by decide)
    all_goals exact absurd h1 hspace

--------- The six messages `badChip` writes ---------

def k0 : BusMessage babyBear := (0, [0, 1])
def k1 : BusMessage babyBear := (0, [1, 4])
def k2 : BusMessage babyBear := (1, [2, 7, 1, 0, 0, 0, 0])
def k3 : BusMessage babyBear := (1, [2, 7, 1, 0, 0, 0, 2])
def k4 : BusMessage babyBear := (1, [2, 7, 2, 0, 0, 0, 0])
def k5 : BusMessage babyBear := (1, [2, 7, 2, 0, 0, 0, 3])

theorem eff_k0 : badChip.allEffects asg0 k0 = -1 := by decide
theorem eff_k1 : badChip.allEffects asg0 k1 = 1 := by decide
theorem eff_k2 : badChip.allEffects asg0 k2 = -1 := by decide
theorem eff_k3 : badChip.allEffects asg0 k3 = 1 := by decide
theorem eff_k4 : badChip.allEffects asg0 k4 = -1 := by decide
theorem eff_k5 : badChip.allEffects asg0 k5 = 1 := by decide

/-- Away from those six messages `badChip` contributes nothing. -/
theorem eff_other (m : BusMessage babyBear)
    (h0 : k0 ≠ m) (h1 : k1 ≠ m) (h2 : k2 ≠ m) (h3 : k3 ≠ m) (h4 : k4 ≠ m) (h5 : k5 ≠ m) :
    badChip.allEffects asg0 m = 0 := by
  simp only [k0, k1, k2, k3, k4, k5] at h0 h1 h2 h3 h4 h5
  simp [Circuit.allEffects, badChip, kc, BusInteraction.eval, Expression.eval,
    h0, h1, h2, h3, h4, h5]

--------- The host side of the run ---------

/-- The connector: seeds `(pc 0, t 1)` and consumes `(pc 1, t 4)`. -/
def theBoundary : ConnectorBoundary babyBear where
  initialPc := 0
  finalPc := 1
  finalTimestamp := 4
  finalTimestampBounded := by decide

def connEffect : BusState babyBear := fun m => if k0 = m then 1 else if k1 = m then -1 else 0

/-- The initial memory image: **two different records at the same cell** `(2, 7)`, both stamped
    `0`. `memoryInitHostChip.canProduce` asks only that each record be a byte-valued memory payload
    stamped `0`; nothing makes the image a *function* of the address. -/
def initEffect : BusState babyBear := fun m => if k2 = m then 1 else if k4 = m then 1 else 0

def finEffect : BusState babyBear := fun m => if k3 = m then -1 else if k5 = m then -1 else 0

theorem connEffect_eq : connEffect = busStateOf (theBoundary.interactions openVmExecBusId) := by
  funext m
  simp only [connEffect, busStateOf, theBoundary, ConnectorBoundary.interactions, k0, k1,
    List.filter_cons, List.filter_nil, decide_eq_true_eq]
  by_cases h0 : ((0 : Nat), ([0, 1] : List (ZMod babyBear))) = m
  · simp only [h0]
    by_cases h1 : ((0 : Nat), ([1, 4] : List (ZMod babyBear))) = m
    · exact absurd (h0.trans h1.symm) (by decide)
    · simp [h1]
  · by_cases h1 : ((0 : Nat), ([1, 4] : List (ZMod babyBear))) = m
    · simp [h0, h1]
    · simp [h0, h1]

--------- The run ---------

noncomputable def theVm (P : OpenVmParams babyBear) : Vm babyBear :=
  ⟨openVmHost P, [badChip]⟩

noncomputable def theAsg (P : OpenVmParams babyBear) : VmAssignment babyBear (theVm P) where
  guestAssignments := fun _ => [asg0]
  hostAssignment := fun t =>
    if t.val = 4 then [initEffect]
    else if t.val = 5 then [finEffect]
    else if t.val = 7 then [connEffect]
    else []

/-- The record the first access reads and writes back. -/
def fA : MemoryPayload babyBear := { addressSpace := 2, pointer := 7, data := #v[1, 0, 0, 0] }

/-- The record the second access reads and writes back — same cell, different value. -/
def fB : MemoryPayload babyBear := { addressSpace := 2, pointer := 7, data := #v[2, 0, 0, 0] }

theorem fA_bytes : ∀ d ∈ fA.data, isByte d := by
  intro d hd
  simp [fA] at hd
  rcases hd with rfl | rfl <;> · simp only [isByte]; decide

theorem fB_bytes : ∀ d ∈ fB.data, isByte d := by
  intro d hd
  simp [fB] at hd
  rcases hd with rfl | rfl <;> · simp only [isByte]; decide

theorem initEffect_canProduce : (memoryInitHostChip (p := babyBear)).canProduce initEffect := by
  intro m hm
  by_cases h2 : k2 = m
  · subst h2
    exact ⟨rfl, by simp [initEffect], fA, rfl, fA_bytes, rfl, Or.inr (Or.inl (by decide))⟩
  · by_cases h4 : k4 = m
    · subst h4
      exact ⟨rfl, by simp [initEffect, h2], fB, rfl, fB_bytes, rfl, Or.inr (Or.inl (by decide))⟩
    · exact absurd (by simp [initEffect, h2, h4] : initEffect m = 0) hm

theorem finEffect_canProduce :
    (memoryFinalizeHostChip (p := babyBear)).canProduce finEffect := by
  intro m hm
  by_cases h3 : k3 = m
  · subst h3
    exact ⟨rfl, by simp [finEffect], fA, rfl, Or.inr (Or.inl (by decide))⟩
  · by_cases h5 : k5 = m
    · subst h5
      exact ⟨rfl, by simp [finEffect, h3], fB, rfl, Or.inr (Or.inl (by decide))⟩
    · exact absurd (by simp [finEffect, h3, h5] : finEffect m = 0) hm

/-- The three non-empty host contributions cancel exactly what the guest instance writes. -/
theorem host_eff (m : BusMessage babyBear) :
    initEffect m + finEffect m + connEffect m = - badChip.allEffects asg0 m := by
  by_cases h0 : k0 = m
  · subst h0; rw [eff_k0]; decide
  by_cases h1 : k1 = m
  · subst h1; rw [eff_k1]; decide
  by_cases h2 : k2 = m
  · subst h2; rw [eff_k2]; decide
  by_cases h3 : k3 = m
  · subst h3; rw [eff_k3]; decide
  by_cases h4 : k4 = m
  · subst h4; rw [eff_k4]; decide
  by_cases h5 : k5 = m
  · subst h5; rw [eff_k5]; decide
  · rw [eff_other m h0 h1 h2 h3 h4 h5]
    simp [initEffect, finEffect, connEffect, h0, h1, h2, h3, h4, h5]

theorem theAsg_balances (P : OpenVmParams babyBear) (m : BusMessage babyBear) :
    (theAsg P).busEffect m = 0 := by
  have hg : (theAsg P).guestAssignments.busEffect m = badChip.allEffects asg0 m := by
    simp [GuestAssignment.busEffect, theAsg, theVm]
  have hh : (theAsg P).hostAssignment.busEffect m
      = initEffect m + finEffect m + connEffect m := by
    show ∑ x : Fin 8, (List.map (fun effect => effect m)
        (if (x : ℕ) = 4 then [initEffect] else if (x : ℕ) = 5 then [finEffect]
          else if (x : ℕ) = 7 then [connEffect] else [])).sum = _
    simp [Fin.sum_univ_eight]
  rw [VmAssignment.busEffect, hg, hh, host_eff m, add_neg_cancel]

/-- **`memoryInitHostChip` closes `badChip`.** Its run needed the initial image to hold two
    different records for cell `(2,7)`; §4.6.2's correspondence with a single initial memory state
    forbids that. -/
theorem initEffect_not_producible :
    ¬ (memoryInitHostChip (p := babyBear)).canProduce initEffect := by
  rintro ⟨-, hinj, -⟩
  exact absurd (hinj k2 k4 (by decide) (by decide) (by decide) (by decide)) (by decide)

/-! `theAsg_satisfiesHost`, `theAsg_vmSat` and `not_forcesAdmissibleOF` stood here. They are
    retracted: `initEffect_not_producible` shows the run's host side is no longer legal, so
    `badChip` — though still a legal guest, and still inadmissible — no longer sits in any
    satisfying run. `theAsg_balances` is kept: the run does still balance, which is why nothing
    short of the initial-image clause could have ruled it out. -/

--------- A second counterexample, surviving both candidate repairs ---------

/-! `badChip` is killed by requiring the initial memory image to be a *function* of the address,
    and by requiring a chip's memory sends to carry distinct timestamps. `badChip2` survives both:
    it makes **one** memory send, and the run's initial image holds **one** record.

    What it does instead is put the send *before* the receive in list order while putting it
    *after* in time — `MemoryBus.lean`'s "this assumes that bus interactions are ordered by time!",
    unbridged. -/

def badChip2 : Circuit babyBear where
  algebraicConstraints := []
  busInteractions :=
    [ kc 0 (-1) [0, 1]
    , kc 0 1 [1, 4]
    , kc 1 1 [2, 7, 1, 0, 0, 0, 2]
    , kc 1 (-1) [2, 7, 5, 0, 0, 0, 0] ]

def j0 : BusMessage babyBear := (0, [0, 1])
def j1 : BusMessage babyBear := (0, [1, 4])
def j2 : BusMessage babyBear := (1, [2, 7, 1, 0, 0, 0, 2])
def j3 : BusMessage babyBear := (1, [2, 7, 5, 0, 0, 0, 0])

theorem badChip2_memMsgs (asg : ChipAssignment babyBear) :
    ((badChip2.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)).filter
      (fun m => m.busId = 1)
    = [ { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] },
        { busId := 1, multiplicity := -1, payload := [2, 7, 5, 0, 0, 0, 0] } ] := by
  rfl

theorem badChip2_not_admissible (asg : ChipAssignment babyBear) :
    ¬ badChip2.admissible bs asg := by
  rintro ⟨h1, -⟩
  have hmem := h1 1 _ memShape_one
  rw [badChip2_memMsgs asg] at hmem
  have := hmem [] [] []
    { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] }
    { busId := 1, multiplicity := -1, payload := [2, 7, 5, 0, 0, 0, 0] }
    rfl rfl rfl rfl (by simp)
  exact absurd this (by decide)

/-- **`badChip2` makes exactly one memory send**, so its sends trivially carry distinct
    timestamps — the discipline that kills `badChip`. -/
theorem badChip2_sends_distinct (asg : ChipAssignment babyBear)
    (i j : Fin badChip2.busInteractions.length)
    (hi : badChip2.memSend rr asg i) (hj : badChip2.memSend rr asg j) : i = j := by
  have key : ∀ k : Fin badChip2.busInteractions.length, badChip2.memSend rr asg k →
      k = ⟨2, by decide⟩ := by
    intro k hk
    fin_cases k
    · exact absurd hk.2 (by decide)
    · exact absurd hk.2 (by decide)
    · rfl
    · exact absurd hk.1.2 (show ¬((-1 : ZMod babyBear) = 1) by decide)
  rw [key i hi, key j hj]

theorem badChip2_payloadOk (asg : ChipAssignment babyBear)
    (i : Fin badChip2.busInteractions.length) : rr.payloadOk (badChip2.msgAt asg i) := by
  fin_cases i
  · exact trivial
  · exact trivial
  all_goals
    show (2 : ZMod babyBear).val = 1 ∨ (2 : ZMod babyBear).val = 2 → _
    intro _ d hd
    simp [Expression.eval] at hd
    rcases hd with rfl | rfl <;> · simp only [isByte]; decide

def offs2 : List ℤ := [0, 3, 1, -1]

theorem badChip2_mult_eq (asg : ChipAssignment babyBear)
    (i : Fin badChip2.busInteractions.length) :
    badChip2.multAt asg i = badChip2.multAt asg0 i := by fin_cases i <;> rfl

theorem badChip2_msg_eq (asg : ChipAssignment babyBear)
    (i : Fin badChip2.busInteractions.length) :
    badChip2.msgAt asg i = badChip2.msgAt asg0 i := by fin_cases i <;> rfl

def badChip2Layout (P : OpenVmParams babyBear) (asg : ChipAssignment babyBear) :
    StepLayout badChip2 rr asg openVmMemAddress P.maxWindow openVmTimestampBound where
  pcFrom := 0
  pcTo := 1
  tStart := 1
  tWindow := 3
  tWindowPos := by decide
  tWindowLt := P.inputWindowOk
  bridgeRecv := by rfl
  bridgeSend := by rfl
  bridgeNoOther := by
    rintro ⟨b, pl⟩ hb h1 h2
    simp only at hb
    subst hb
    simp only [Prod.mk.injEq, true_and, ne_eq] at h1 h2
    have h2' : ¬ pl = [(1 : ZMod babyBear), 4] := fun h => h2 (by rw [h]; decide)
    have e1 : ¬ (([0, 1] : List (ZMod babyBear)) = pl) := fun h => h1 h.symm
    have e2 : ¬ (([1, 4] : List (ZMod babyBear)) = pl) := fun h => h2' h.symm
    simp [Circuit.allEffects, badChip2, kc, BusInteraction.eval, Expression.eval,
      show rr.execBusId = 0 from rfl, e1, e2]
  tOffset := fun i => offs2.getD i.val 0
  tOffsetMatch := by
    intro i _
    fin_cases i
    · exact ⟨by decide, by decide, by show (1 : ZMod babyBear) = 1 + ((0 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (4 : ZMod babyBear) = 1 + ((3 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (2 : ZMod babyBear) = 1 + ((1 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (0 : ZMod babyBear) = 1 + ((-1 : ℤ) : ZMod babyBear); decide⟩
  memSendsOk := fun i _ _ => badChip2_payloadOk asg i
  sendTimesDistinct := fun i j hi hj _ _ => badChip2_sends_distinct asg i j hi hj
  negOffsetOnlyMemRecv := by
    intro i _ hlt
    fin_cases i <;> first | exact ⟨rfl, rfl⟩ | exact absurd hlt (by decide)
  sendInWindow := by
    intro i hi
    fin_cases i <;>
      first
        | decide
        | exact absurd hi.2 (by decide)
        | exact absurd hi.1.2 negOne_ne_one
  memPartner := fun i => if i.val = 2 then ⟨3, by decide⟩ else ⟨2, by decide⟩
  memPartner_invol := by
    intro i hi
    fin_cases i <;> first | exact absurd hi (by decide) | exact ⟨rfl, by decide, rfl⟩
  memPartner_mult := by
    intro i hi
    simp only [badChip2_mult_eq, badChip2_msg_eq]
    fin_cases i <;> first | exact absurd hi (by decide) | exact ⟨by decide, by decide⟩
  memPartner_time := by
    intro i hi hr
    fin_cases i <;>
      first
        | decide
        | exact absurd hi (by decide)
        | exact absurd hr oneNeNegOne

theorem badChip2_legalGuest (P : OpenVmParams babyBear) (hI : 4 ≤ P.maxInteractions) :
    (openVmHost P).legalGuest badChip2 where
  sendOnly := by
    intro asg _ bi hbi hst
    fin_cases hbi <;> exact absurd hst (by decide)
  polarity := by
    intro asg _ bi hbi _
    fin_cases hbi <;> simp [kc, BusInteraction.eval, Expression.eval]
  stepLayout := fun asg _ _ => ⟨badChip2Layout P asg⟩
  size := hI
  x0Zero := by
    intro asg _ _ i hs h1
    have hspace : ¬((some 2 : Option (ZMod babyBear)) = some 1) := by decide
    fin_cases i
    · exact absurd hs.2 (by decide)
    · exact absurd hs.2 (by decide)
    all_goals exact absurd h1 hspace

theorem eff2_j0 : badChip2.allEffects asg0 j0 = -1 := by decide
theorem eff2_j1 : badChip2.allEffects asg0 j1 = 1 := by decide
theorem eff2_j2 : badChip2.allEffects asg0 j2 = 1 := by decide
theorem eff2_j3 : badChip2.allEffects asg0 j3 = -1 := by decide

theorem eff2_other (m : BusMessage babyBear)
    (h0 : j0 ≠ m) (h1 : j1 ≠ m) (h2 : j2 ≠ m) (h3 : j3 ≠ m) :
    badChip2.allEffects asg0 m = 0 := by
  simp only [j0, j1, j2, j3] at h0 h1 h2 h3
  simp [Circuit.allEffects, badChip2, kc, BusInteraction.eval, Expression.eval, h0, h1, h2, h3]

/-- The initial memory image for this run: **one** record, so it is a function of the address. -/
def initEffect2 : BusState babyBear := fun m => if j3 = m then 1 else 0

def finEffect2 : BusState babyBear := fun m => if j2 = m then -1 else 0

/-- The repair that kills `badChip`: this image assigns at most one record per address. -/
theorem initEffect2_functional (m m' : BusMessage babyBear)
    (h : initEffect2 m ≠ 0) (h' : initEffect2 m' ≠ 0) : m = m' := by
  by_cases hm : j3 = m
  · by_cases hm' : j3 = m'
    · exact hm ▸ hm' ▸ rfl
    · exact absurd (by simp [initEffect2, hm'] : initEffect2 m' = 0) h'
  · exact absurd (by simp [initEffect2, hm] : initEffect2 m = 0) h

/-- The one record this run's initial image holds. -/
def fC : MemoryPayload babyBear := { addressSpace := 2, pointer := 7, data := #v[5, 0, 0, 0] }

theorem fC_bytes : ∀ d ∈ fC.data, isByte d := by
  intro d hd
  simp [fC] at hd
  rcases hd with rfl | rfl <;> · simp only [isByte]; decide

theorem initEffect2_canProduce :
    (memoryInitHostChip (p := babyBear)).canProduce initEffect2 := by
  refine ⟨?_, fun m m' h h' _ _ => initEffect2_functional m m' h h', ?_⟩
  case refine_2 =>
    intro m hm h1
    by_cases h3 : j3 = m
    · exact absurd (h3 ▸ h1) (by decide)
    · exact absurd (by simp [initEffect2, h3] : initEffect2 m = 0) hm
  intro m hm
  by_cases h3 : j3 = m
  · subst h3
    exact ⟨rfl, by simp [initEffect2], fC, rfl, fC_bytes, rfl, Or.inr (Or.inl (by decide))⟩
  · exact absurd (by simp [initEffect2, h3] : initEffect2 m = 0) hm

theorem finEffect2_canProduce :
    (memoryFinalizeHostChip (p := babyBear)).canProduce finEffect2 := by
  intro m hm
  by_cases h2 : j2 = m
  · subst h2
    exact ⟨rfl, by simp [finEffect2], fA, rfl, Or.inr (Or.inl (by decide))⟩
  · exact absurd (by simp [finEffect2, h2] : finEffect2 m = 0) hm

theorem host_eff2 (m : BusMessage babyBear) :
    initEffect2 m + finEffect2 m + connEffect m = - badChip2.allEffects asg0 m := by
  by_cases h0 : j0 = m
  · subst h0; rw [eff2_j0]; decide
  by_cases h1 : j1 = m
  · subst h1; rw [eff2_j1]; decide
  by_cases h2 : j2 = m
  · subst h2; rw [eff2_j2]; decide
  by_cases h3 : j3 = m
  · subst h3; rw [eff2_j3]; decide
  · rw [eff2_other m h0 h1 h2 h3]
    simp [initEffect2, finEffect2, connEffect, h0, h1, h2, h3,
      show k0 = j0 from rfl, show k1 = j1 from rfl]

noncomputable def theVm2 (P : OpenVmParams babyBear) : Vm babyBear :=
  ⟨openVmHost P, [badChip2]⟩

noncomputable def theAsg2 (P : OpenVmParams babyBear) : VmAssignment babyBear (theVm2 P) where
  guestAssignments := fun _ => [asg0]
  hostAssignment := fun t =>
    if t.val = 4 then [initEffect2]
    else if t.val = 5 then [finEffect2]
    else if t.val = 7 then [connEffect]
    else []

theorem theAsg2_balances (P : OpenVmParams babyBear) (m : BusMessage babyBear) :
    (theAsg2 P).busEffect m = 0 := by
  have hg : (theAsg2 P).guestAssignments.busEffect m = badChip2.allEffects asg0 m := by
    simp [GuestAssignment.busEffect, theAsg2, theVm2]
  have hh : (theAsg2 P).hostAssignment.busEffect m
      = initEffect2 m + finEffect2 m + connEffect m := by
    show ∑ x : Fin 8, (List.map (fun effect => effect m)
        (if (x : ℕ) = 4 then [initEffect2] else if (x : ℕ) = 5 then [finEffect2]
          else if (x : ℕ) = 7 then [connEffect] else [])).sum = _
    simp [Fin.sum_univ_eight]
  rw [VmAssignment.busEffect, hg, hh, host_eff2 m, add_neg_cancel]

theorem theAsg2_satisfiesHost (P : OpenVmParams babyBear) :
    (theAsg2 P).hostAssignment.satisfies where
  producible := by
    intro t effect he
    fin_cases t <;> simp [theAsg2, theVm2, openVmHost] at he ⊢
    · subst he; exact initEffect2_canProduce
    · subst he; exact finEffect2_canProduce
    · subst he; exact ⟨theBoundary, connEffect_eq⟩
  withinBound := by
    intro t
    fin_cases t <;>
      simp [theAsg2, theVm2, openVmHost, memoryInitHostChip, memoryFinalizeHostChip,
        connectorHostChip, singletonWitnessChip]

theorem theAsg2_vmSat (P : OpenVmParams babyBear) (hN : 1 ≤ P.maxInstances) :
    VmSat (theVm2 P) (theAsg2 P) where
  satisfiesGuest := by intro t asg _ c hc; simp [theVm2, badChip2] at hc
  satisfiesHost := theAsg2_satisfiesHost P
  balances := theAsg2_balances P
  withinBudget := by
    simpa [GuestAssignment.instanceCount, theAsg2, theVm2, openVmHost] using hN

/-- **`forcesAdmissible` still fails once the initial image is a function of the address and a
    chip's memory sends carry distinct timestamps.** `badChip2` satisfies both
    (`initEffect2_functional`, `badChip2_sends_distinct`) and is still legal, satisfying and
    inadmissible. -/
theorem not_forcesAdmissible' (P : OpenVmParams babyBear) (hI : 4 ≤ P.maxInteractions)
    (hN : 1 ≤ P.maxInstances) :
    ¬ (openVmHost P).forcesAdmissible (openVmBusSemantics babyBear defaultBusMap) := by
  intro h
  refine badChip2_not_admissible asg0
    (h [badChip2] ?_ (theAsg2 P) (theAsg2_vmSat P hN) 0 asg0 ?_)
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact badChip2_legalGuest P hI
  · simp [theAsg2]

--------- Against the order-free rely (`VmSpec/OrderFree.lean`) ---------

open ApcOptimizer.OpenVM.OrderFree

abbrev bsOF : BusSemantics babyBear := openVmBusSemanticsOF babyBear defaultBusMap none

/-- `defaultBusMap` declares a memory shape on exactly two bus ids. -/
theorem memShapeOf_default {busId : Nat} {shape : MemoryBusShape}
    (h : memShapeOf defaultBusMap busId = some shape) :
    (busId = 0 ∧ shape = { addressFields := [], direction := .receiveThenSend }) ∨
    (busId = 1 ∧ shape = { addressFields := [0, 1], direction := .receiveThenSend }) := by
  match busId with
  | 0 => exact Or.inl ⟨rfl, by simpa [memShapeOf, defaultBusMap] using h.symm⟩
  | 1 => exact Or.inr ⟨rfl, by simpa [memShapeOf, defaultBusMap] using h.symm⟩
  | 2 => simp [memShapeOf, defaultBusMap] at h
  | 3 => simp [memShapeOf, defaultBusMap] at h
  | 4 => simp [memShapeOf, defaultBusMap] at h
  | 5 => simp [memShapeOf, defaultBusMap] at h
  | 6 => simp [memShapeOf, defaultBusMap] at h
  | 7 => simp [memShapeOf, defaultBusMap] at h
  | (n + 8) => simp [memShapeOf, defaultBusMap] at h

/-- Likewise for the declared timestamp slot. -/
theorem memTsFieldOf_default {busId tsField : Nat}
    (h : memTsFieldOf defaultBusMap busId = some tsField) :
    (busId = 0 ∧ tsField = 1) ∨ (busId = 1 ∧ tsField = 6) := by
  match busId with
  | 0 => exact Or.inl ⟨rfl, by simpa [memTsFieldOf, defaultBusMap] using h.symm⟩
  | 1 => exact Or.inr ⟨rfl, by simpa [memTsFieldOf, defaultBusMap] using h.symm⟩
  | 2 => simp [memTsFieldOf, defaultBusMap] at h
  | 3 => simp [memTsFieldOf, defaultBusMap] at h
  | 4 => simp [memTsFieldOf, defaultBusMap] at h
  | 5 => simp [memTsFieldOf, defaultBusMap] at h
  | 6 => simp [memTsFieldOf, defaultBusMap] at h
  | 7 => simp [memTsFieldOf, defaultBusMap] at h
  | (n + 8) => simp [memTsFieldOf, defaultBusMap] at h

/-- With no entry pc supplied, ENTRY_KEY is vacuous. -/
theorem memEntryKeyOf_none {busId : Nat} :
    memEntryKeyOf (p := babyBear) defaultBusMap none busId = none := by
  simp [memEntryKeyOf]

/-- The stateful messages each chip writes, and their per-bus slices, at `bsOF`. -/
theorem badChip2_msgsOF (asg : ChipAssignment babyBear) :
    (badChip2.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bsOF.isStateful m.busId)
    = [ { busId := 0, multiplicity := -1, payload := [0, 1] },
        { busId := 0, multiplicity := 1, payload := [1, 4] },
        { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] },
        { busId := 1, multiplicity := -1, payload := [2, 7, 5, 0, 0, 0, 0] } ] := by
  rfl

theorem badChip2_msgs0OF (asg : ChipAssignment babyBear) :
    ((badChip2.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bsOF.isStateful m.busId)).filter
      (fun m => m.busId = 0)
    = [ { busId := 0, multiplicity := -1, payload := [0, 1] },
        { busId := 0, multiplicity := 1, payload := [1, 4] } ] := by
  rfl

theorem badChip2_msgs1OF (asg : ChipAssignment babyBear) :
    ((badChip2.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bsOF.isStateful m.busId)).filter
      (fun m => m.busId = 1)
    = [ { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] },
        { busId := 1, multiplicity := -1, payload := [2, 7, 5, 0, 0, 0, 0] } ] := by
  rfl

theorem badChip_msgs1OF (asg : ChipAssignment babyBear) :
    ((badChip.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bsOF.isStateful m.busId)).filter
      (fun m => m.busId = 1)
    = [ { busId := 1, multiplicity := -1, payload := [2, 7, 1, 0, 0, 0, 0] },
        { busId := 1, multiplicity := 1, payload := [2, 7, 1, 0, 0, 0, 2] },
        { busId := 1, multiplicity := -1, payload := [2, 7, 2, 0, 0, 0, 0] },
        { busId := 1, multiplicity := 1, payload := [2, 7, 2, 0, 0, 0, 3] } ] := by
  rfl

/-- **The order-free rely accepts `badChip2`.** Its single memory access brings one record into
    the block at `(2,7)`, which is all `admissibleMemoryBusM` asks; the list order that the
    positional discipline read as a stale read is invisible to it. -/
theorem badChip2_admissibleOF (asg : ChipAssignment babyBear) :
    badChip2.admissible bsOF asg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro busId shape h
    rcases memShapeOf_default h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [badChip2_msgs0OF asg]
      exact fun addr => le_trans (card_excessAt_le_recvs _ addr _) (by decide)
    · rw [badChip2_msgs1OF asg]
      exact fun addr => le_trans (card_excessAt_le_recvs _ addr _) (by decide)
  · rintro busId tsField h
    rcases memTsFieldOf_default h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [badChip2_msgs0OF asg]; simp only [tsBounded]; decide
    · rw [badChip2_msgs1OF asg]; simp only [tsBounded]; decide
  · rintro busId slot key shape - hk
    exact absurd hk (by simp [memEntryKeyOf_none])
  · rw [badChip2_msgsOF asg]; simp only [x0ReturnsZero]; decide

/-- **The order-free rely still rejects `badChip`** — and correctly: *two* records enter the block
    at cell `(2,7)`, which no window can supply. -/
theorem badChip_not_admissibleOF (asg : ChipAssignment babyBear) :
    ¬ badChip.admissible bsOF asg := by
  rintro ⟨h1, -⟩
  have hmem := h1 1 _ memShape_one
  rw [badChip_msgs1OF asg] at hmem
  exact absurd (hmem [some 2, some 7]) (by decide)

/-! `not_forcesAdmissibleOF` stood here — `badChip`, legal and inadmissible, sitting in a
    satisfying run. Retracted by `initEffect_not_producible` above. -/

--------- Order-free rely + distinct send times + functional init: still not enough ---------

/-! Two chips running back to back. `chipA` writes cell `(2,7)` twice, at `t = 2` and `t = 3`;
    `chipB`, in the next window, reads both records back and writes nothing. Between them the
    memory bus balances with **no initial image at all**, so a functional-init repair is vacuously
    satisfied, and neither chip has two memory sends at one time.

    `chipB` is still inadmissible: two records enter its window at one address. What it violates is
    **access pairing** — a memory access is a receive *and* a send at the same address, and neither
    chip's accesses pair up. -/

def chipA : Circuit babyBear where
  algebraicConstraints := []
  busInteractions :=
    [ kc 0 (-1) [0, 1]
    , kc 0 1 [1, 4]
    , kc 1 1 [2, 7, 9, 0, 0, 0, 2]
    , kc 1 1 [2, 7, 8, 0, 0, 0, 3] ]

def chipB : Circuit babyBear where
  algebraicConstraints := []
  busInteractions :=
    [ kc 0 (-1) [1, 4]
    , kc 0 1 [3, 7]
    , kc 1 (-1) [2, 7, 9, 0, 0, 0, 2]
    , kc 1 (-1) [2, 7, 8, 0, 0, 0, 3] ]

def n0 : BusMessage babyBear := (0, [0, 1])
def n1 : BusMessage babyBear := (0, [1, 4])
def n2 : BusMessage babyBear := (0, [3, 7])
def n3 : BusMessage babyBear := (1, [2, 7, 9, 0, 0, 0, 2])
def n4 : BusMessage babyBear := (1, [2, 7, 8, 0, 0, 0, 3])

/-- **`chipB` makes no memory send at all**, so "no two memory sends at the same time" holds
    vacuously — as it does for `chipA`, whose two sends sit at `t = 2` and `t = 3`. -/
theorem chipB_no_memSend (asg : ChipAssignment babyBear)
    (i : Fin chipB.busInteractions.length) : ¬ chipB.memSend rr asg i := by
  intro hi
  fin_cases i
  · exact absurd hi.2 (by decide)
  · exact absurd hi.2 (by decide)
  · exact absurd hi.1.2 (show ¬((-1 : ZMod babyBear) = 1) by decide)
  · exact absurd hi.1.2 (show ¬((-1 : ZMod babyBear) = 1) by decide)

theorem chipA_sends_distinct (asg : ChipAssignment babyBear)
    (i j : Fin chipA.busInteractions.length)
    (hi : chipA.memSend rr asg i) (hj : chipA.memSend rr asg j)
    (hts : rr.getTimestamp (chipA.msgAt asg i) = rr.getTimestamp (chipA.msgAt asg j)) : i = j := by
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | exact absurd hi.2 (by decide)
      | exact absurd hj.2 (by decide)
      | exact absurd hts (show ¬((2 : ZMod babyBear) = 3) by decide)
      | exact absurd hts (show ¬((3 : ZMod babyBear) = 2) by decide)

theorem chipB_msgs1OF (asg : ChipAssignment babyBear) :
    ((chipB.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bsOF.isStateful m.busId)).filter
      (fun m => m.busId = 1)
    = [ { busId := 1, multiplicity := -1, payload := [2, 7, 9, 0, 0, 0, 2] },
        { busId := 1, multiplicity := -1, payload := [2, 7, 8, 0, 0, 0, 3] } ] := by
  rfl

/-- **`chipB` is inadmissible under the order-free rely**: two records enter its window at cell
    `(2,7)`. -/
theorem chipB_not_admissibleOF (asg : ChipAssignment babyBear) :
    ¬ chipB.admissible bsOF asg := by
  rintro ⟨h1, -⟩
  have hmem := h1 1 _ memShape_one
  rw [chipB_msgs1OF asg] at hmem
  exact absurd (hmem [some 2, some 7]) (by decide)

theorem chipA_payloadOk (asg : ChipAssignment babyBear)
    (i : Fin chipA.busInteractions.length) : rr.payloadOk (chipA.msgAt asg i) := by
  fin_cases i
  · exact trivial
  · exact trivial
  all_goals
    show (2 : ZMod babyBear).val = 1 ∨ (2 : ZMod babyBear).val = 2 → _
    intro _ d hd
    simp [Expression.eval] at hd
    rcases hd with rfl | rfl <;> · simp only [isByte]; decide

def offsA : List ℤ := [0, 3, 1, 2]
def offsB : List ℤ := [0, 3, -2, -1]

def chipALayout (P : OpenVmParams babyBear) (asg : ChipAssignment babyBear) :
    StepLayout chipA rr asg P.maxWindow openVmTimestampBound where
  pcFrom := 0
  pcTo := 1
  tStart := 1
  tWindow := 3
  tWindowPos := by decide
  tWindowLt := P.inputWindowOk
  bridgeRecv := by rfl
  bridgeSend := by rfl
  bridgeNoOther := by
    rintro ⟨b, pl⟩ hb h1 h2
    simp only at hb
    subst hb
    simp only [Prod.mk.injEq, true_and, ne_eq] at h1 h2
    have h2' : ¬ pl = [(1 : ZMod babyBear), 4] := fun h => h2 (by rw [h]; decide)
    have e1 : ¬ (([0, 1] : List (ZMod babyBear)) = pl) := fun h => h1 h.symm
    have e2 : ¬ (([1, 4] : List (ZMod babyBear)) = pl) := fun h => h2' h.symm
    simp [Circuit.allEffects, chipA, kc, BusInteraction.eval, Expression.eval,
      show rr.execBusId = 0 from rfl, e1, e2]
  tOffset := fun i => offsA.getD i.val 0
  tOffsetMatch := by
    intro i _
    fin_cases i
    · exact ⟨by decide, by decide, by show (1 : ZMod babyBear) = 1 + ((0 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (4 : ZMod babyBear) = 1 + ((3 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (2 : ZMod babyBear) = 1 + ((1 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (3 : ZMod babyBear) = 1 + ((2 : ℤ) : ZMod babyBear); decide⟩
  memSendsOk := fun i _ _ => chipA_payloadOk asg i

def chipBLayout (P : OpenVmParams babyBear) (asg : ChipAssignment babyBear) :
    StepLayout chipB rr asg P.maxWindow openVmTimestampBound where
  pcFrom := 1
  pcTo := 3
  tStart := 4
  tWindow := 3
  tWindowPos := by decide
  tWindowLt := P.inputWindowOk
  bridgeRecv := by rfl
  bridgeSend := by rfl
  bridgeNoOther := by
    rintro ⟨b, pl⟩ hb h1 h2
    simp only at hb
    subst hb
    simp only [Prod.mk.injEq, true_and, ne_eq] at h1 h2
    have h2' : ¬ pl = [(3 : ZMod babyBear), 7] := fun h => h2 (by rw [h]; decide)
    have e1 : ¬ (([1, 4] : List (ZMod babyBear)) = pl) := fun h => h1 h.symm
    have e2 : ¬ (([3, 7] : List (ZMod babyBear)) = pl) := fun h => h2' h.symm
    simp [Circuit.allEffects, chipB, kc, BusInteraction.eval, Expression.eval,
      show rr.execBusId = 0 from rfl, e1, e2]
  tOffset := fun i => offsB.getD i.val 0
  tOffsetMatch := by
    intro i _
    fin_cases i
    · exact ⟨by decide, by decide, by show (4 : ZMod babyBear) = 4 + ((0 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (7 : ZMod babyBear) = 4 + ((3 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (2 : ZMod babyBear) = 4 + ((-2 : ℤ) : ZMod babyBear); decide⟩
    · exact ⟨by decide, by decide, by show (3 : ZMod babyBear) = 4 + ((-1 : ℤ) : ZMod babyBear); decide⟩
  memSendsOk := fun i hi _ => absurd hi (chipB_no_memSend asg i)

/-- `chipA` has no active memory *receive* — it only writes. -/
theorem chipA_no_memRecv (asg : ChipAssignment babyBear)
    (i : Fin chipA.busInteractions.length) :
    ¬ (chipA.activeMem rr asg i ∧ chipA.multAt asg i = -1) := by
  rintro ⟨hact, hrecv⟩
  fin_cases i
  · exact absurd hact.2 (by decide)
  · exact absurd hact.2 (by decide)
  · exact absurd hrecv oneNeNegOne
  · exact absurd hrecv oneNeNegOne

theorem chipA_sat (asg : ChipAssignment babyBear) :
    chipA.satisfiesAlgebraic asg ∧ chipA.satisfiesStateless rr asg :=
  ⟨by intro e he; simp [chipA] at he,
   by intro bi hbi hst; fin_cases hbi <;> exact absurd hst (by decide)⟩

theorem chipB_sat (asg : ChipAssignment babyBear) :
    chipB.satisfiesAlgebraic asg ∧ chipB.satisfiesStateless rr asg :=
  ⟨by intro e he; simp [chipB] at he,
   by intro bi hbi hst; fin_cases hbi <;> exact absurd hst (by decide)⟩

/-- **The pairing clause closes this counterexample.** `chipA` writes two records it never read,
    so `accessPartner_onto` — every memory send is some receive's partner — has nothing to offer;
    `chipB` reads two records it never replaces, so `accessPartner_spec` cannot produce the send
    half of either access. Neither is a legal guest of `openVmHost` any more.

    The run itself (`theAsg3_vmSat` below) is untouched: `VmSat` never mentions legality. What
    changed is that `Host.forcesAdmissible` no longer has to account for it. -/
theorem chipA_not_legalGuest (P : OpenVmParams babyBear) :
    ¬ (openVmHost P).legalGuest chipA := by
  intro h
  obtain ⟨L⟩ := h.stepLayout asg0 (chipA_sat asg0).1 (chipA_sat asg0).2
  have key := L.memPartner_mult ⟨2, by decide⟩ rfl
  revert key
  generalize L.memPartner ⟨2, by decide⟩ = j
  -- No index can be interaction `2`'s partner: the two memory interactions carry the *same*
  -- multiplicity, so `memPartner_mult`'s negation fails, and the two bridge interactions carry a
  -- different `memAddress`.
  fin_cases j <;> intro key <;> exact absurd key (by decide)

theorem chipB_not_legalGuest (P : OpenVmParams babyBear) :
    ¬ (openVmHost P).legalGuest chipB := by
  intro h
  obtain ⟨L⟩ := h.stepLayout asg0 (chipB_sat asg0).1 (chipB_sat asg0).2
  have key := L.memPartner_mult ⟨2, by decide⟩ rfl
  revert key
  generalize L.memPartner ⟨2, by decide⟩ = j
  -- No index can be interaction `2`'s partner: the two memory interactions carry the *same*
  -- multiplicity, so `memPartner_mult`'s negation fails, and the two bridge interactions carry a
  -- different `memAddress`.
  fin_cases j <;> intro key <;> exact absurd key (by decide)

def theBoundary3 : ConnectorBoundary babyBear where
  initialPc := 0
  finalPc := 3
  finalTimestamp := 7
  finalTimestampBounded := by decide

def connEffect3 : BusState babyBear := fun m => if n0 = m then 1 else if n2 = m then -1 else 0

theorem connEffect3_eq : connEffect3 = busStateOf (theBoundary3.interactions openVmExecBusId) := by
  funext m
  simp only [connEffect3, busStateOf, theBoundary3, ConnectorBoundary.interactions, n0, n2,
    List.filter_cons, List.filter_nil, decide_eq_true_eq]
  by_cases h0 : ((0 : Nat), ([0, 1] : List (ZMod babyBear))) = m
  · simp only [h0]
    by_cases h2 : ((0 : Nat), ([3, 7] : List (ZMod babyBear))) = m
    · exact absurd (h0.trans h2.symm) (by decide)
    · simp [h2]
  · by_cases h2 : ((0 : Nat), ([3, 7] : List (ZMod babyBear))) = m
    · simp [h0, h2]
    · simp [h0, h2]

theorem gnet_n0 : chipA.allEffects asg0 n0 + chipB.allEffects asg0 n0 = -1 := by decide
theorem gnet_n1 : chipA.allEffects asg0 n1 + chipB.allEffects asg0 n1 = 0 := by decide
theorem gnet_n2 : chipA.allEffects asg0 n2 + chipB.allEffects asg0 n2 = 1 := by decide
theorem gnet_n3 : chipA.allEffects asg0 n3 + chipB.allEffects asg0 n3 = 0 := by decide
theorem gnet_n4 : chipA.allEffects asg0 n4 + chipB.allEffects asg0 n4 = 0 := by decide

theorem gnet_other (m : BusMessage babyBear) (h0 : n0 ≠ m) (h1 : n1 ≠ m) (h2 : n2 ≠ m)
    (h3 : n3 ≠ m) (h4 : n4 ≠ m) :
    chipA.allEffects asg0 m + chipB.allEffects asg0 m = 0 := by
  simp only [n0, n1, n2, n3, n4] at h0 h1 h2 h3 h4
  simp [Circuit.allEffects, chipA, chipB, kc, BusInteraction.eval, Expression.eval,
    h0, h1, h2, h3, h4]

theorem host_eff3 (m : BusMessage babyBear) :
    connEffect3 m = - (chipA.allEffects asg0 m + chipB.allEffects asg0 m) := by
  by_cases h0 : n0 = m
  · subst h0; rw [gnet_n0]; decide
  by_cases h1 : n1 = m
  · subst h1; rw [gnet_n1]; decide
  by_cases h2 : n2 = m
  · subst h2; rw [gnet_n2]; decide
  by_cases h3 : n3 = m
  · subst h3; rw [gnet_n3]; decide
  by_cases h4 : n4 = m
  · subst h4; rw [gnet_n4]; decide
  · rw [gnet_other m h0 h1 h2 h3 h4]
    simp [connEffect3, h0, h2]

noncomputable def theVm3 (P : OpenVmParams babyBear) : Vm babyBear :=
  ⟨openVmHost P, [chipA, chipB]⟩

noncomputable def theAsg3 (P : OpenVmParams babyBear) : VmAssignment babyBear (theVm3 P) where
  guestAssignments := fun _ => [asg0]
  hostAssignment := fun t => if t.val = 7 then [connEffect3] else []

theorem theAsg3_balances (P : OpenVmParams babyBear) (m : BusMessage babyBear) :
    (theAsg3 P).busEffect m = 0 := by
  have hg : (theAsg3 P).guestAssignments.busEffect m
      = chipA.allEffects asg0 m + chipB.allEffects asg0 m := by
    show ∑ t : Fin 2, (([asg0] : List (ChipAssignment babyBear)).map
        (fun asg => ([chipA, chipB].get t).allEffects asg m)).sum = _
    simp [Fin.sum_univ_two]
  have hh : (theAsg3 P).hostAssignment.busEffect m = connEffect3 m := by
    show ∑ x : Fin 8, (List.map (fun effect => effect m)
        (if (x : ℕ) = 7 then [connEffect3] else [])).sum = _
    simp [Fin.sum_univ_eight]
  rw [VmAssignment.busEffect, hg, hh, host_eff3 m, add_neg_cancel]

theorem theAsg3_satisfiesHost (P : OpenVmParams babyBear) :
    (theAsg3 P).hostAssignment.satisfies where
  producible := by
    intro t effect he
    fin_cases t <;> simp [theAsg3, theVm3, openVmHost] at he ⊢
    · subst he; exact ⟨theBoundary3, connEffect3_eq⟩
  withinBound := by
    intro t
    fin_cases t <;>
      simp [theAsg3, theVm3, openVmHost, connectorHostChip, singletonWitnessChip]

theorem theAsg3_vmSat (P : OpenVmParams babyBear) (hN : 2 ≤ P.maxInstances) :
    VmSat (theVm3 P) (theAsg3 P) where
  satisfiesGuest := by
    intro t asg _ c hc
    fin_cases t <;> simp [theVm3, chipA, chipB] at hc
  satisfiesHost := theAsg3_satisfiesHost P
  balances := theAsg3_balances P
  withinBudget := by
    simpa [GuestAssignment.instanceCount, theAsg3, theVm3, openVmHost, Fin.sum_univ_two] using hN

/-! `not_forcesAdmissibleOF'` stood here: the two-chip run above refuted `forcesAdmissible` under
    the order-free rely with distinct send times and no initial image at all. It is retracted —
    `chipA_not_legalGuest`/`chipB_not_legalGuest` show `legalGuest`'s pairing clause rules both
    chips out, so the run is no longer a run of legal guests. -/

end ApcOptimizer.OpenVM.AdmissibleGap
