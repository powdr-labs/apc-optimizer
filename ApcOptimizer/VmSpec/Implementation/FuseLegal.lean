import ApcOptimizer.VmSpec.Implementation.Fusion
import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! # Legality is closed under fusion

    `Circuit.fuse` concatenates two instruction chips and pins `c1`'s outgoing bridge message to
    `c2`'s incoming one. This file shows the result is a legal guest whenever the ingredients are:
    the fused step is one arc from `c1`'s entry to `c2`'s exit, and the middle bridge message
    cancels between the two halves. -/

variable {p : ℕ} {c1 c2 : Circuit p} {pcOut tOut pcIn tIn : Expression p}

namespace Circuit

--------- The index embeddings ---------

@[simp] theorem fuse_busInteractions :
    (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions
      = c1.busInteractions ++ c2.busInteractions := rfl

theorem fuse_length :
    (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length
      = c1.busInteractions.length + c2.busInteractions.length := by
  simp

/-- `c1`'s `i`th interaction, as an index into the fused chip. -/
def fuseInl (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    (i : Fin c1.busInteractions.length) :
    Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length :=
  ⟨i.val, by rw [fuse_length]; exact Nat.lt_add_right _ i.isLt⟩

/-- `c2`'s `j`th interaction, as an index into the fused chip. -/
def fuseInr (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    (j : Fin c2.busInteractions.length) :
    Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length :=
  ⟨c1.busInteractions.length + j.val, by rw [fuse_length]; omega⟩

theorem fuse_get_inl (i : Fin c1.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.get (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      = c1.busInteractions.get i := by
  simp only [List.get_eq_getElem, fuseInl, fuse_busInteractions]
  exact List.getElem_append_left i.isLt

theorem fuse_get_inr (j : Fin c2.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.get (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      = c2.busInteractions.get j := by
  simp only [List.get_eq_getElem, fuseInr, fuse_busInteractions]
  rw [List.getElem_append_right (Nat.le_add_right _ _)]
  simp

/-- Every fused index is one half's or the other's. -/
theorem fuse_cases (k : Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length) :
    (∃ i, k = fuseInl c1 c2 pcOut tOut pcIn tIn i)
      ∨ (∃ j, k = fuseInr c1 c2 pcOut tOut pcIn tIn j) := by
  have hk : (k : ℕ) < c1.busInteractions.length + c2.busInteractions.length := by
    simpa using k.isLt
  by_cases h : k.val < c1.busInteractions.length
  · exact Or.inl ⟨⟨k.val, h⟩, by apply Fin.ext; simp [fuseInl]⟩
  · refine Or.inr ⟨⟨k.val - c1.busInteractions.length, by omega⟩, ?_⟩
    apply Fin.ext; simp only [fuseInr]; omega

--------- Transfer along the embeddings ---------

variable {asg : ChipAssignment p} {r : GuestBusRules p}

theorem fuse_busId_inl (i : Fin c1.busInteractions.length) :
    ((c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.get
      (fuseInl c1 c2 pcOut tOut pcIn tIn i)).busId = (c1.busInteractions.get i).busId := by
  rw [fuse_get_inl]

theorem fuse_busId_inr (j : Fin c2.busInteractions.length) :
    ((c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.get
      (fuseInr c1 c2 pcOut tOut pcIn tIn j)).busId = (c2.busInteractions.get j).busId := by
  rw [fuse_get_inr]

theorem fuse_multAt_inl (i : Fin c1.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).multAt asg (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      = c1.multAt asg i := by
  unfold Circuit.multAt; rw [fuse_get_inl]

theorem fuse_multAt_inr (j : Fin c2.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).multAt asg (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      = c2.multAt asg j := by
  unfold Circuit.multAt; rw [fuse_get_inr]

theorem fuse_msgAt_inl (i : Fin c1.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).msgAt asg (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      = c1.msgAt asg i := by
  unfold Circuit.msgAt; rw [fuse_get_inl]

theorem fuse_msgAt_inr (j : Fin c2.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).msgAt asg (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      = c2.msgAt asg j := by
  unfold Circuit.msgAt; rw [fuse_get_inr]

theorem fuse_activeStateful_inl (i : Fin c1.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).activeStateful r asg (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      ↔ c1.activeStateful r asg i := by
  simp only [Circuit.activeStateful, fuse_busId_inl, fuse_multAt_inl]

theorem fuse_activeStateful_inr (j : Fin c2.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).activeStateful r asg (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      ↔ c2.activeStateful r asg j := by
  simp only [Circuit.activeStateful, fuse_busId_inr, fuse_multAt_inr]

theorem fuse_memSend_inl (i : Fin c1.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).memSend r asg (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      ↔ c1.memSend r asg i := by
  simp only [Circuit.memSend, Circuit.statefulSend, fuse_busId_inl, fuse_multAt_inl]

theorem fuse_memSend_inr (j : Fin c2.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).memSend r asg (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      ↔ c2.memSend r asg j := by
  simp only [Circuit.memSend, Circuit.statefulSend, fuse_busId_inr, fuse_multAt_inr]

theorem fuse_activeMem_inl (i : Fin c1.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).activeMem r asg (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      ↔ c1.activeMem r asg i := by
  simp only [Circuit.activeMem, Circuit.activeStateful, fuse_busId_inl, fuse_multAt_inl]

theorem fuse_activeMem_inr (j : Fin c2.busInteractions.length) :
    (c1.fuse c2 pcOut tOut pcIn tIn).activeMem r asg (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      ↔ c2.activeMem r asg j := by
  simp only [Circuit.activeMem, Circuit.activeStateful, fuse_busId_inr, fuse_multAt_inr]

--------- The two clauses that are just a union ---------

theorem fuse_algebraicallyForces {stateful : Bool} {P : BusInteraction (ZMod p) → Prop}
    (h1 : c1.algebraicallyForces r stateful P) (h2 : c2.algebraicallyForces r stateful P) :
    (c1.fuse c2 pcOut tOut pcIn tIn).algebraicallyForces r stateful P := by
  intro asg halg bi hbi hst
  rcases List.mem_append.mp hbi with h | h
  · exact h1 asg (Circuit.fuse_satisfiesAlgebraic_left c1 c2 pcOut tOut pcIn tIn halg) bi h hst
  · exact h2 asg (Circuit.fuse_satisfiesAlgebraic_right c1 c2 pcOut tOut pcIn tIn halg) bi h hst

theorem fuse_satisfiesStateless_left
    (h : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesStateless r asg) :
    c1.satisfiesStateless r asg :=
  fun bi hbi => h bi (List.mem_append.mpr (Or.inl hbi))

theorem fuse_satisfiesStateless_right
    (h : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesStateless r asg) :
    c2.satisfiesStateless r asg :=
  fun bi hbi => h bi (List.mem_append.mpr (Or.inr hbi))

theorem fuse_idx_lt {k : Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length}
    (h : ¬ (k : ℕ) < c1.busInteractions.length) :
    (k : ℕ) - c1.busInteractions.length < c2.busInteractions.length := by
  have hk : (k : ℕ) < c1.busInteractions.length + c2.busInteractions.length := by simpa using k.isLt
  omega

@[simp] theorem fuseInl_val (i : Fin c1.busInteractions.length) :
    ((fuseInl c1 c2 pcOut tOut pcIn tIn i : Fin _) : ℕ) = (i : ℕ) := rfl

@[simp] theorem fuseInr_val (j : Fin c2.busInteractions.length) :
    ((fuseInr c1 c2 pcOut tOut pcIn tIn j : Fin _) : ℕ)
      = c1.busInteractions.length + (j : ℕ) := rfl

/-- `c1`'s offsets, then `c2`'s shifted past `c1`'s window. -/
def fuseOffset (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    (o1 : Fin c1.busInteractions.length → ℤ) (o2 : Fin c2.busInteractions.length → ℤ) (w1 : ℕ)
    (k : Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length) : ℤ :=
  if h : (k : ℕ) < c1.busInteractions.length then o1 ⟨k, h⟩
  else (w1 : ℤ) + o2 ⟨(k : ℕ) - c1.busInteractions.length, fuse_idx_lt h⟩

variable {o1 : Fin c1.busInteractions.length → ℤ} {o2 : Fin c2.busInteractions.length → ℤ} {w1 : ℕ}

@[simp] theorem fuseOffset_inl (i : Fin c1.busInteractions.length) :
    fuseOffset c1 c2 pcOut tOut pcIn tIn o1 o2 w1 (fuseInl c1 c2 pcOut tOut pcIn tIn i) = o1 i := by
  simp [fuseOffset]

@[simp] theorem fuseOffset_inr (j : Fin c2.busInteractions.length) :
    fuseOffset c1 c2 pcOut tOut pcIn tIn o1 o2 w1 (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      = (w1 : ℤ) + o2 j := by
  simp only [fuseOffset, fuseInr_val, Nat.add_sub_cancel_left,
    dif_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))]

/-- `c1`'s pairing on its own half, `c2`'s on its own. -/
def fusePartner (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    (m1 : Fin c1.busInteractions.length → Fin c1.busInteractions.length)
    (m2 : Fin c2.busInteractions.length → Fin c2.busInteractions.length)
    (k : Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length) :
    Fin (c1.fuse c2 pcOut tOut pcIn tIn).busInteractions.length :=
  if h : (k : ℕ) < c1.busInteractions.length then
    fuseInl c1 c2 pcOut tOut pcIn tIn (m1 ⟨k, h⟩)
  else fuseInr c1 c2 pcOut tOut pcIn tIn (m2 ⟨(k : ℕ) - c1.busInteractions.length, fuse_idx_lt h⟩)

variable {m1 : Fin c1.busInteractions.length → Fin c1.busInteractions.length}
  {m2 : Fin c2.busInteractions.length → Fin c2.busInteractions.length}

@[simp] theorem fusePartner_inl (i : Fin c1.busInteractions.length) :
    fusePartner c1 c2 pcOut tOut pcIn tIn m1 m2 (fuseInl c1 c2 pcOut tOut pcIn tIn i)
      = fuseInl c1 c2 pcOut tOut pcIn tIn (m1 i) := by
  simp [fusePartner]

@[simp] theorem fusePartner_inr (j : Fin c2.busInteractions.length) :
    fusePartner c1 c2 pcOut tOut pcIn tIn m1 m2 (fuseInr c1 c2 pcOut tOut pcIn tIn j)
      = fuseInr c1 c2 pcOut tOut pcIn tIn (m2 j) := by
  simp only [fusePartner, fuseInr_val, Nat.add_sub_cancel_left,
    dif_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))]

theorem fuseInl_ne_inr (i : Fin c1.busInteractions.length) (j : Fin c2.busInteractions.length) :
    fuseInl c1 c2 pcOut tOut pcIn tIn i ≠ fuseInr c1 c2 pcOut tOut pcIn tIn j := by
  intro h
  have := congrArg Fin.val h
  simp only [fuseInl_val, fuseInr_val] at this
  have := i.isLt
  omega

theorem fuseInl_inj {i i' : Fin c1.busInteractions.length}
    (h : fuseInl c1 c2 pcOut tOut pcIn tIn i = fuseInl c1 c2 pcOut tOut pcIn tIn i') : i = i' := by
  apply Fin.ext; simpa using congrArg Fin.val h

theorem fuseInr_inj {j j' : Fin c2.busInteractions.length}
    (h : fuseInr c1 c2 pcOut tOut pcIn tIn j = fuseInr c1 c2 pcOut tOut pcIn tIn j') : j = j' := by
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [fuseInr_val] at this
  omega

--------- The fusion equations, and which bridge message is which ---------

open ApcOptimizer.Spec.Dsl in
theorem eval_sub (a b : Expression p) (asg : ChipAssignment p) :
    (a - b).eval asg = a.eval asg - b.eval asg := by
  show (Expression.add a (Expression.mul (Expression.const (-1)) b)).eval asg = _
  simp [Expression.eval]
  ring

open ApcOptimizer.Spec.Dsl in
theorem fuse_pcOut_eq (halg : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesAlgebraic asg) :
    pcOut.eval asg = pcIn.eval asg := by
  have h := halg (pcOut - pcIn) (by simp [Circuit.fuse])
  rw [eval_sub] at h
  exact sub_eq_zero.mp h

open ApcOptimizer.Spec.Dsl in
theorem fuse_tOut_eq (halg : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesAlgebraic asg) :
    tOut.eval asg = tIn.eval asg := by
  have h := halg (tOut - tIn) (by simp [Circuit.fuse])
  rw [eval_sub] at h
  exact sub_eq_zero.mp h

end Circuit

/-- `1 ≠ -1` also rules out the degenerate field where `1 = 0`. -/
theorem one_ne_zero_of_ne_neg_one {p : ℕ} (hne : (1 : ZMod p) ≠ -1) : (1 : ZMod p) ≠ 0 := by
  intro h
  exact hne (by rw [h]; simp)

variable {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
  {memAddress : BusMessage p → List (Option (ZMod p))} {maxWindow maxLookback : ℕ}

/-- A bridge message the chip *sends* is its outgoing one: `StepLayout` allows no other. -/
theorem StepLayout.send_eq (L : StepLayout c r asg memAddress maxWindow maxLookback)
    (hne : (1 : ZMod p) ≠ -1) {pc t : ZMod p}
    (h : c.allEffects asg (r.execBusId, [pc, t]) = 1) :
    pc = L.pcTo ∧ t = L.tStart + (L.tWindow : ZMod p) := by
  by_cases h1 : ((r.execBusId, [pc, t]) : BusMessage p) = (r.execBusId, [L.pcFrom, L.tStart])
  · rw [h1, L.bridgeRecv] at h; exact absurd h.symm hne
  by_cases h2 : ((r.execBusId, [pc, t]) : BusMessage p)
      = (r.execBusId, [L.pcTo, L.tStart + (L.tWindow : ZMod p)])
  · simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h2
    exact ⟨h2.1, h2.2⟩
  · rw [L.bridgeNoOther _ rfl h1 h2] at h
    exact absurd h.symm (one_ne_zero_of_ne_neg_one hne)

/-- …and one it *receives* is its incoming one. -/
theorem StepLayout.recv_eq (L : StepLayout c r asg memAddress maxWindow maxLookback)
    (hne : (1 : ZMod p) ≠ -1) {pc t : ZMod p}
    (h : c.allEffects asg (r.execBusId, [pc, t]) = -1) :
    pc = L.pcFrom ∧ t = L.tStart := by
  by_cases h1 : ((r.execBusId, [pc, t]) : BusMessage p) = (r.execBusId, [L.pcFrom, L.tStart])
  · simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h1
    exact ⟨h1.1, h1.2⟩
  by_cases h2 : ((r.execBusId, [pc, t]) : BusMessage p)
      = (r.execBusId, [L.pcTo, L.tStart + (L.tWindow : ZMod p)])
  · rw [h2, L.bridgeSend] at h; exact absurd h hne
  · rw [L.bridgeNoOther _ rfl h1 h2] at h
    exact absurd h.symm (neg_ne_zero.mpr (one_ne_zero_of_ne_neg_one hne))

--------- The fused step layout ---------

/-- `Circuit.fuse`'s four expression arguments really are the two halves' bridge messages:
    `pcOut`/`tOut` is where `c1` sends, `pcIn`/`tIn` where `c2` receives. `fuse` only *equates*
    them, so this is a hypothesis rather than something it enforces. -/
structure FuseBridge (c1 c2 : Circuit p) (r : GuestBusRules p)
    (pcOut tOut pcIn tIn : Expression p) : Prop where
  sendsOut : ∀ asg : ChipAssignment p, c1.satisfiesAlgebraic asg →
    c1.allEffects asg (r.execBusId, [pcOut.eval asg, tOut.eval asg]) = 1
  recvsIn : ∀ asg : ChipAssignment p, c2.satisfiesAlgebraic asg →
    c2.allEffects asg (r.execBusId, [pcIn.eval asg, tIn.eval asg]) = -1

theorem natCast_ne_zero_of_lt {n : ℕ} [NeZero p] (h0 : 0 < n) (h : n < p) :
    ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd h0 hdvd
  omega

/-- **The fused chip lays out as one step**: `c1`'s entry to `c2`'s exit, with the middle bridge
    message cancelling between the halves. The window is the sum of the two, hence the conclusion
    at `2 * maxWindow`. -/
def StepLayout.fuse [NeZero p]
    (hne : (1 : ZMod p) ≠ -1) (hp : 2 * maxWindow ≤ p)
    (hb : FuseBridge c1 c2 r pcOut tOut pcIn tIn)
    (halg : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesAlgebraic asg)
    (L1 : StepLayout c1 r asg memAddress maxWindow maxLookback)
    (L2 : StepLayout c2 r asg memAddress maxWindow maxLookback) :
    StepLayout (c1.fuse c2 pcOut tOut pcIn tIn) r asg memAddress (2 * maxWindow) maxLookback := by
  classical
  have halg1 := Circuit.fuse_satisfiesAlgebraic_left c1 c2 pcOut tOut pcIn tIn halg
  have halg2 := Circuit.fuse_satisfiesAlgebraic_right c1 c2 pcOut tOut pcIn tIn halg
  obtain ⟨hpc1, ht1⟩ := L1.send_eq hne (hb.sendsOut asg halg1)
  obtain ⟨hpc2, ht2⟩ := L2.recv_eq hne (hb.recvsIn asg halg2)
  have hpcEq : L1.pcTo = L2.pcFrom := by rw [← hpc1, ← hpc2, Circuit.fuse_pcOut_eq halg]
  have htEq : L2.tStart = L1.tStart + (L1.tWindow : ZMod p) := by
    rw [← ht2, ← ht1, Circuit.fuse_tOut_eq halg]
  have hw1 := L1.tWindowPos; have hw2 := L2.tWindowPos
  have hl1 := L1.tWindowLt; have hl2 := L2.tWindowLt
  have hd1 : ((L1.tWindow : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hw1 (by omega)
  have hd2 : ((L2.tWindow : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hw2 (by omega)
  have hd12 : ((L1.tWindow + L2.tWindow : ℕ) : ZMod p) ≠ 0 :=
    natCast_ne_zero_of_lt (by omega) (by omega)
  -- The middle bridge message: `c1`'s send is `c2`'s receive.
  have hmid : ((r.execBusId, [L1.pcTo, L1.tStart + (L1.tWindow : ZMod p)]) : BusMessage p)
      = (r.execBusId, [L2.pcFrom, L2.tStart]) := by rw [hpcEq, htEq]
  -- The fused chip's outgoing message is `c2`'s.
  have hout : ((r.execBusId,
        [L2.pcTo, L1.tStart + ((L1.tWindow + L2.tWindow : ℕ) : ZMod p)]) : BusMessage p)
      = (r.execBusId, [L2.pcTo, L2.tStart + (L2.tWindow : ZMod p)]) := by
    rw [htEq]; push_cast; ring_nf
  -- `c2` contributes nothing where the fused chip receives …
  have hc2recv : c2.allEffects asg (r.execBusId, [L1.pcFrom, L1.tStart]) = 0 := by
    refine L2.bridgeNoOther _ rfl (fun h => ?_) (fun h => ?_)
    · simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
      rw [htEq] at h
      exact hd1 (by linear_combination -h.2)
    · simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
      rw [htEq] at h
      exact hd12 (by push_cast; linear_combination -h.2)
  -- … and `c1` nothing where it sends.
  have hc1send : c1.allEffects asg
      (r.execBusId, [L2.pcTo, L1.tStart + ((L1.tWindow + L2.tWindow : ℕ) : ZMod p)]) = 0 := by
    refine L1.bridgeNoOther _ rfl (fun h => ?_) (fun h => ?_)
    · simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
      exact hd12 (by linear_combination h.2)
    · simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
      exact hd2 (by push_cast at h ⊢; linear_combination h.2)
  refine
    { pcFrom := L1.pcFrom
      pcTo := L2.pcTo
      tStart := L1.tStart
      tWindow := L1.tWindow + L2.tWindow
      tOffset := Circuit.fuseOffset c1 c2 pcOut tOut pcIn tIn L1.tOffset L2.tOffset L1.tWindow
      memPartner := Circuit.fusePartner c1 c2 pcOut tOut pcIn tIn L1.memPartner L2.memPartner
      tWindowPos := by omega
      tWindowLt := by omega
      bridgeRecv := ?bridgeRecv
      bridgeSend := ?bridgeSend
      bridgeNoOther := ?bridgeNoOther
      tOffsetMatch := ?tOffsetMatch
      memSendsOk := ?memSendsOk
      sendTimesDistinct := ?sendTimesDistinct
      sendInWindow := ?sendInWindow
      negOffsetOnlyMemRecv := ?negOffsetOnlyMemRecv
      memPartner_invol := ?memPartner_invol
      memPartner_mult := ?memPartner_mult
      memPartner_time := ?memPartner_time }
  case bridgeRecv =>
    rw [Circuit.fuse_allEffects, L1.bridgeRecv, hc2recv, add_zero]
  case bridgeSend =>
    rw [Circuit.fuse_allEffects, hc1send, zero_add, hout, L2.bridgeSend]
  case bridgeNoOther =>
    intro m hm hne1 hne2
    rw [Circuit.fuse_allEffects]
    by_cases hm1 : m = (r.execBusId, [L1.pcTo, L1.tStart + (L1.tWindow : ZMod p)])
    · subst hm1
      rw [L1.bridgeSend, hmid, L2.bridgeRecv]
      ring
    · rw [L1.bridgeNoOther m hm hne1 hm1,
        L2.bridgeNoOther m hm (by rwa [← hmid]) (by rwa [← hout])]
      ring
  case tOffsetMatch =>
    intro k hk
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨ha, hbb, hc⟩ := L1.tOffsetMatch i ((Circuit.fuse_activeStateful_inl i).mp hk)
      rw [Circuit.fuseOffset_inl, Circuit.fuse_msgAt_inl]
      exact ⟨ha, by push_cast; omega, hc⟩
    · obtain ⟨ha, hbb, hc⟩ := L2.tOffsetMatch j ((Circuit.fuse_activeStateful_inr j).mp hk)
      rw [Circuit.fuseOffset_inr, Circuit.fuse_msgAt_inr]
      refine ⟨by omega, by push_cast; omega, ?_⟩
      rw [hc, htEq]; push_cast; ring
  case memSendsOk =>
    intro k hk hprev
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [Circuit.fuse_msgAt_inl]
      refine L1.memSendsOk i ((Circuit.fuse_memSend_inl i).mp hk) (fun j0 hlt hact => ?_)
      have := hprev (Circuit.fuseInl c1 c2 pcOut tOut pcIn tIn j0)
        (by rwa [Circuit.fuseOffset_inl, Circuit.fuseOffset_inl])
        ((Circuit.fuse_activeMem_inl j0).mpr hact)
      rwa [Circuit.fuse_msgAt_inl] at this
    · rw [Circuit.fuse_msgAt_inr]
      refine L2.memSendsOk j ((Circuit.fuse_memSend_inr j).mp hk) (fun j0 hlt hact => ?_)
      have := hprev (Circuit.fuseInr c1 c2 pcOut tOut pcIn tIn j0)
        (by rw [Circuit.fuseOffset_inr, Circuit.fuseOffset_inr]; omega)
        ((Circuit.fuse_activeMem_inr j0).mpr hact)
      rwa [Circuit.fuse_msgAt_inr] at this
  case sendTimesDistinct =>
    intro k1 k2 hs1 hs2 haddr hoff
    rcases Circuit.fuse_cases k1 with ⟨i1, rfl⟩ | ⟨j1, rfl⟩ <;>
      rcases Circuit.fuse_cases k2 with ⟨i2, rfl⟩ | ⟨j2, rfl⟩
    · rw [Circuit.fuseOffset_inl, Circuit.fuseOffset_inl] at hoff
      rw [Circuit.fuse_msgAt_inl, Circuit.fuse_msgAt_inl] at haddr
      exact congrArg _ (L1.sendTimesDistinct i1 i2 ((Circuit.fuse_memSend_inl i1).mp hs1)
        ((Circuit.fuse_memSend_inl i2).mp hs2) haddr hoff)
    · exfalso
      have h1 := L1.sendInWindow i1 ((Circuit.fuse_memSend_inl i1).mp hs1)
      have h2 := L2.sendInWindow j2 ((Circuit.fuse_memSend_inr j2).mp hs2)
      rw [Circuit.fuseOffset_inl, Circuit.fuseOffset_inr] at hoff
      omega
    · exfalso
      have h1 := L2.sendInWindow j1 ((Circuit.fuse_memSend_inr j1).mp hs1)
      have h2 := L1.sendInWindow i2 ((Circuit.fuse_memSend_inl i2).mp hs2)
      rw [Circuit.fuseOffset_inr, Circuit.fuseOffset_inl] at hoff
      omega
    · rw [Circuit.fuseOffset_inr, Circuit.fuseOffset_inr] at hoff
      rw [Circuit.fuse_msgAt_inr, Circuit.fuse_msgAt_inr] at haddr
      exact congrArg _ (L2.sendTimesDistinct j1 j2 ((Circuit.fuse_memSend_inr j1).mp hs1)
        ((Circuit.fuse_memSend_inr j2).mp hs2) haddr (by omega))
  case sendInWindow =>
    intro k hk
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have := L1.sendInWindow i ((Circuit.fuse_memSend_inl i).mp hk)
      rw [Circuit.fuseOffset_inl]
      constructor
      · omega
      · push_cast; omega
    · have := L2.sendInWindow j ((Circuit.fuse_memSend_inr j).mp hk)
      rw [Circuit.fuseOffset_inr]
      constructor
      · omega
      · push_cast; omega
  case negOffsetOnlyMemRecv =>
    intro k hact hneg
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [Circuit.fuseOffset_inl] at hneg
      have := L1.negOffsetOnlyMemRecv i ((Circuit.fuse_activeStateful_inl i).mp hact) hneg
      rwa [Circuit.fuse_busId_inl, Circuit.fuse_multAt_inl]
    · rw [Circuit.fuseOffset_inr] at hneg
      have := L2.negOffsetOnlyMemRecv j ((Circuit.fuse_activeStateful_inr j).mp hact) (by omega)
      rwa [Circuit.fuse_busId_inr, Circuit.fuse_multAt_inr]
  case memPartner_invol =>
    intro k hk
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [Circuit.fuse_busId_inl] at hk
      obtain ⟨e1, e2, e3⟩ := L1.memPartner_invol i hk
      refine ⟨by rw [Circuit.fusePartner_inl, Circuit.fusePartner_inl, e1], ?_, ?_⟩
      · rw [Circuit.fusePartner_inl]
        exact fun h => e2 (Circuit.fuseInl_inj h)
      · rw [Circuit.fusePartner_inl, Circuit.fuse_busId_inl]; exact e3
    · rw [Circuit.fuse_busId_inr] at hk
      obtain ⟨e1, e2, e3⟩ := L2.memPartner_invol j hk
      refine ⟨by rw [Circuit.fusePartner_inr, Circuit.fusePartner_inr, e1], ?_, ?_⟩
      · rw [Circuit.fusePartner_inr]
        exact fun h => e2 (Circuit.fuseInr_inj h)
      · rw [Circuit.fusePartner_inr, Circuit.fuse_busId_inr]; exact e3
  case memPartner_mult =>
    intro k hk
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [Circuit.fuse_busId_inl] at hk
      obtain ⟨e1, e2⟩ := L1.memPartner_mult i hk
      rw [Circuit.fusePartner_inl, Circuit.fuse_multAt_inl, Circuit.fuse_multAt_inl,
        Circuit.fuse_msgAt_inl, Circuit.fuse_msgAt_inl]
      exact ⟨e1, e2⟩
    · rw [Circuit.fuse_busId_inr] at hk
      obtain ⟨e1, e2⟩ := L2.memPartner_mult j hk
      rw [Circuit.fusePartner_inr, Circuit.fuse_multAt_inr, Circuit.fuse_multAt_inr,
        Circuit.fuse_msgAt_inr, Circuit.fuse_msgAt_inr]
      exact ⟨e1, e2⟩
  case memPartner_time =>
    intro k hk hmult
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [Circuit.fuse_busId_inl] at hk
      rw [Circuit.fuse_multAt_inl] at hmult
      rw [Circuit.fusePartner_inl, Circuit.fuseOffset_inl, Circuit.fuseOffset_inl]
      exact L1.memPartner_time i hk hmult
    · rw [Circuit.fuse_busId_inr] at hk
      rw [Circuit.fuse_multAt_inr] at hmult
      rw [Circuit.fusePartner_inr, Circuit.fuseOffset_inr, Circuit.fuseOffset_inr]
      have := L2.memPartner_time j hk hmult
      omega

--------- Legality is closed under fusion ---------

variable {maxInteractions maxInteractions' : ℕ}

theorem Circuit.fuse_hasStepLayout [NeZero p]
    (hne : (1 : ZMod p) ≠ -1) (hp : 2 * maxWindow ≤ p)
    (hb : FuseBridge c1 c2 r pcOut tOut pcIn tIn)
    (h1 : c1.hasStepLayout r memAddress maxWindow maxLookback)
    (h2 : c2.hasStepLayout r memAddress maxWindow maxLookback) :
    (c1.fuse c2 pcOut tOut pcIn tIn).hasStepLayout r memAddress (2 * maxWindow) maxLookback := by
  intro asg halg hsl
  obtain ⟨L1⟩ := h1 asg (Circuit.fuse_satisfiesAlgebraic_left c1 c2 pcOut tOut pcIn tIn halg)
    (Circuit.fuse_satisfiesStateless_left hsl)
  obtain ⟨L2⟩ := h2 asg (Circuit.fuse_satisfiesAlgebraic_right c1 c2 pcOut tOut pcIn tIn halg)
    (Circuit.fuse_satisfiesStateless_right hsl)
  exact ⟨StepLayout.fuse hne hp hb halg L1 L2⟩

/-- **Fusing two legal guest chips gives a legal guest chip.** The window doubles (the fused step
    runs both instructions) and the interaction count adds, so the conclusion is at `2 * maxWindow`
    and at whatever bound `hsize` supplies; `maxLookback` is unchanged, since the fused chip reaches
    no further back than `c1` already did.

    `hb` is what `Circuit.fuse` assumes but does not enforce — that its four expression arguments
    are really the two halves' bridge messages. Without it `fuse` equates two arbitrary expressions
    and the halves need not line up at all. -/
theorem Circuit.legalGuest_fuse [NeZero p]
    (hne : (1 : ZMod p) ≠ -1) (hp : 2 * maxWindow ≤ p)
    (hb : FuseBridge c1 c2 r pcOut tOut pcIn tIn)
    (hsize : c1.busInteractions.length + c2.busInteractions.length ≤ maxInteractions')
    (h1 : c1.legalGuest r memAddress maxWindow maxLookback maxInteractions)
    (h2 : c2.legalGuest r memAddress maxWindow maxLookback maxInteractions) :
    (c1.fuse c2 pcOut tOut pcIn tIn).legalGuest r memAddress
      (2 * maxWindow) maxLookback maxInteractions' where
  sendOnly := Circuit.fuse_algebraicallyForces h1.sendOnly h2.sendOnly
  polarity := Circuit.fuse_algebraicallyForces h1.polarity h2.polarity
  stepLayout := Circuit.fuse_hasStepLayout hne hp hb h1.stepLayout h2.stepLayout
  size := by simpa using hsize
  x0Zero := by
    intro asg halg hsl k hk h0 h1'
    rcases Circuit.fuse_cases k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [Circuit.fuse_msgAt_inl] at h0 h1' ⊢
      exact h1.x0Zero asg (Circuit.fuse_satisfiesAlgebraic_left c1 c2 pcOut tOut pcIn tIn halg)
        (Circuit.fuse_satisfiesStateless_left hsl) i ((Circuit.fuse_memSend_inl i).mp hk) h0 h1'
    · rw [Circuit.fuse_msgAt_inr] at h0 h1' ⊢
      exact h2.x0Zero asg (Circuit.fuse_satisfiesAlgebraic_right c1 c2 pcOut tOut pcIn tIn halg)
        (Circuit.fuse_satisfiesStateless_right hsl) j ((Circuit.fuse_memSend_inr j).mp hk) h0 h1'
