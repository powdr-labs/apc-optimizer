import ApcOptimizer.VmSpec.Implementation.ChainDisjoint
import ApcOptimizer.VmSpec.Implementation.Excess
import ApcOptimizer.VmSpec.Implementation.HostCounts
import ApcOptimizer.VmSpec.Implementation.OrderFreeRealizes

set_option autoImplicit false

/-! # Placing a run's memory records on the clock

    The first half of discharging `Host.forcesAdmissible` for `openVmHost`; the counting argument
    that finishes it is `Implementation/MemChain.lean`, which also carries the final theorem.

    ## What is here

    * `sum_eq_countP_sub` — the signed analogue of `Counting.sum_eq_countP_mul`. `Counting.lean`'s
      `uniformAt` asks that every multiplicity at a message be `0` or one fixed `v`; that is right
      on a lookup bus but wrong on memory, where a run carries a `+1` and a `-1` at the *same*
      record. False at `p = 2`, hence the two hypotheses.
    * `openVm_admissibleBridge` — **the execution-bridge half of the order-free memory
      discipline**, and it is entirely local: the bridge is declared memory-shaped with a single
      global cell, and `bridgeRecv`/`bridgeSend`/`bridgeNoOther` already pin a step's whole bridge
      traffic, so the one record entering is the one the step receives.
    * `openVmHost_recv_has_sender` / `openVmHost_no_recv_of_no_send` — **record matching.** Every
      memory message a realized instance receives is sent by a guest instance, the initial image, or
      an input-chip instance. This is where the *sign* of the host's contribution matters, which is
      why `openVmHost_memNet_or_sender` (`Implementation/HostCounts.lean`) computes it exactly:
      `memoryFinalizeHostChip` is routinely nonzero at a message while only ever receiving, so
      "the host net is nonzero" is not enough.
    * `openVmHost_arcsPlaced` — every bridge arc, guest instance *and* input-chip instance alike,
      starts at an honest natural timestamp low enough to fit under `2 ^ 29`, and no two arcs'
      windows overlap. Guests come back with a `StepLayout`, so a caller gets `sendInWindow`,
      `memPartner` and the placement together.
    * `openVmHost_recordGood` — TS_BOUND and `x0ReturnsZero` in one statement, for every memory
      record a realized guest instance touches: sends by their own placement, receives by record
      matching plus the goodness of whichever of the three producers supplied them.
    * `card_excessAt_le_one_of_counts` (`Implementation/Excess.lean`) — `excessAt`'s cardinality
      bound reduced to a count on the underlying list, so a bus's admissibility becomes arithmetic.

    ## Modelling gaps — all four closed

    1. `memoryInitHostChip` pins `x0` to zero (the initial memory state's hardwired zero
       register). Without it `x0ReturnsZero` is false of any chip that *reads* `x0`, which
       `Audit/Apcs/AndBranch` and `Keccak2105000` both do. Its address injectivity is what makes
       the initial image a *function* of the address — `init(τ) ≤ 1` in `MemChain.lean`'s count.
    2. `OpenVmParams.ptrRegNeZero`. `InputRead.interactions` writes address space `1` at `ptrReg`
       carrying byte-valued `ptrLimbs`; at `ptrReg = 0` that is a nonzero write to `x0`. As a
       field element, which is the form `x0ReturnsZero` compares against.
    3. `StepLayout.negOffsetOnlyMemRecv` — only a memory `getPrevious` may reach backwards.
       `bridgeNoOther` constrains only the *net* at a message, so a pair carrying the same
       execution-bridge message with multiplicities `-1` and `+1` nets to zero and may sit at
       offset `-(2^29 - 1)`, where the timestamp has wrapped. `Audit/BridgeOffsetGap.lean` proves
       such a chip satisfies the original `StepLayout` in full, and that this clause is what
       rejects it. With it, TS_BOUND on the bridge is `openVmHost_bridgeGood`.
    4. `InputRead.ptrOffsetOk`/`wordOffsetOk` — §4.6.1's `t_prev < t` for the input chip's own two
       memory accesses. `Audit/InputTimeGap.lean` audits the clauses and carries the balancing run
       they exclude.

    One configuration precondition also had to be strengthened: `OpenVmParams.budgetOk` now budgets
    the *host's* interactions too, since a record-matching balance counts guest receives alongside
    `memoryFinalizeHostChip`'s and each input instance's. -/

namespace ApcOptimizer.OpenVM

open ApcOptimizer.OpenVM.OrderFree

variable {p : ℕ}

--------- Signed counting ---------

/-- **The signed analogue of `Counting.sum_eq_countP_mul`.** A list of `0`/`±1` sums to its count
    of `1`s minus its count of `-1`s.

    `Counting.lean`'s `uniformAt` machinery asks that every multiplicity at a message be `0` or one
    fixed `v`. That is the right shape on a lookup bus, where a chip only ever sends, but not on
    memory, where a run carries both a `+1` and a `-1` at the same record — one chip's `setNew` and
    the next chip's `getPrevious`. This is the primitive the memory argument needs instead.

    Both hypotheses are load-bearing rather than tidiness: at `p = 2` the conclusion is false, since
    `1 = -1` collapses the two counts. `openVm_negOne_ne_one` supplies `h1` for OpenVM. -/
theorem sum_eq_countP_sub {l : List (ZMod p)} (h0 : (1 : ZMod p) ≠ 0) (h1 : (1 : ZMod p) ≠ -1)
    (h : ∀ x ∈ l, x = 0 ∨ x = 1 ∨ x = -1) :
    l.sum = ((l.countP (fun x => decide (x = 1)) : ℕ) : ZMod p)
      - ((l.countP (fun x => decide (x = -1)) : ℕ) : ZMod p) := by
  classical
  have hne0 : ¬ ((0 : ZMod p) = 1) := fun hc => h0 hc.symm
  have hne0' : ¬ ((0 : ZMod p) = -1) := fun hc => h0 (neg_eq_zero.mp hc.symm)
  induction l with
  | nil => simp
  | cons a t ih =>
    have hmem : ∀ x ∈ t, x = 0 ∨ x = 1 ∨ x = -1 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a (by simp)
    rw [List.sum_cons, ih hmem, List.countP_cons, List.countP_cons]
    rcases ha with rfl | rfl | rfl
    · simp [hne0, hne0']
    · simp only [decide_true, decide_eq_true_eq, if_true, h1, if_false, Nat.cast_add,
        Nat.cast_one]
      push_cast
      ring
    · simp only [Ne.symm h1, decide_eq_true_eq, if_false, decide_true, if_true, Nat.cast_add,
        Nat.cast_one]
      push_cast
      ring

--------- Signed counts, per chip and per run ---------

/-- How many of a chip's interactions *send* `m`. -/
def _root_.Circuit.sendAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : ℕ :=
  (c.multsAt asg m).countP (fun v => decide (v = 1))

/-- …and how many *receive* it. -/
def _root_.Circuit.recvAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : ℕ :=
  (c.multsAt asg m).countP (fun v => decide (v = -1))

/-- Every multiplicity the chip puts on `m` is `0` or `±1` — what `statefulPolarity` gives at a
    stateful message, and the signed analogue of `Circuit.uniformAt`. -/
def _root_.Circuit.pmAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : Prop :=
  ∀ bi ∈ c.busInteractions, ((bi.eval asg).busId, (bi.eval asg).payload) = m →
    (bi.eval asg).multiplicity = 0 ∨ (bi.eval asg).multiplicity = 1 ∨
      (bi.eval asg).multiplicity = -1

theorem multsAt_of_pmAt {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h : c.pmAt asg m) : ∀ x ∈ c.multsAt asg m, x = 0 ∨ x = 1 ∨ x = -1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  exact h bi hbi (of_decide_eq_true hy2)

/-- **One chip's net at `m` is its sends minus its receives.** -/
theorem allEffects_eq_send_sub_recv {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h0 : (1 : ZMod p) ≠ 0) (h1 : (1 : ZMod p) ≠ -1) (h : c.pmAt asg m) :
    c.allEffects asg m = (c.sendAt asg m : ZMod p) - (c.recvAt asg m : ZMod p) :=
  sum_eq_countP_sub h0 h1 (multsAt_of_pmAt h)

/-- A list of differences sums to the difference of the sums. -/
theorem list_sum_map_sub {α : Type} (l : List α) (f g : α → ZMod p) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
      List.map_cons, List.sum_cons]; ring

theorem list_sum_map_cast {α : Type} (l : List α) (f : α → ℕ) :
    (l.map (fun x => (f x : ZMod p))).sum = ((l.map f).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]; push_cast; ring

/-- The run's total sends and receives of `m`, across every realized guest instance. -/
def _root_.GuestAssignment.sendCount {G : Guest p} (gA : GuestAssignment p G) (m : BusMessage p) : ℕ :=
  ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).sendAt asg m)).sum

def _root_.GuestAssignment.recvCount {G : Guest p} (gA : GuestAssignment p G) (m : BusMessage p) : ℕ :=
  ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).recvAt asg m)).sum

/-- **The guests' net at `m` is their sends minus their receives**, as honest counts. -/
theorem guestNet_eq_send_sub_recv {G : Guest p} {gA : GuestAssignment p G} {m : BusMessage p}
    (h0 : (1 : ZMod p) ≠ 0) (h1 : (1 : ZMod p) ≠ -1)
    (hpm : ∀ (t : Fin G.length), ∀ asg ∈ gA t, (G.get t).pmAt asg m) :
    gA.busEffect m = (gA.sendCount m : ZMod p) - (gA.recvCount m : ZMod p) := by
  show (∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg m)).sum) = _
  rw [_root_.GuestAssignment.sendCount, _root_.GuestAssignment.recvCount, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← list_sum_map_cast (gA t) (fun asg => (G.get t).sendAt asg m),
    ← list_sum_map_cast (gA t) (fun asg => (G.get t).recvAt asg m),
    ← list_sum_map_sub]
  refine congrArg List.sum (List.map_congr_left (fun asg hasg => ?_))
  exact allEffects_eq_send_sub_recv h0 h1 (hpm t asg hasg)

theorem recvAt_le_countAt {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h0 : (1 : ZMod p) ≠ 0) : c.recvAt asg m ≤ c.countAt asg m := by
  refine List.countP_mono_left (fun x _ hx => ?_)
  simp only [decide_eq_true_eq] at hx
  simp only [ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  rw [hx]
  exact fun hc => h0 (neg_eq_zero.mp hc)

theorem list_sum_map_le {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) ih

theorem recvCount_le_count {G : Guest p} {gA : GuestAssignment p G} {m : BusMessage p}
    (h0 : (1 : ZMod p) ≠ 0) : gA.recvCount m ≤ gA.count m :=
  Finset.sum_le_sum (fun _ _ => list_sum_map_le _ _ _ (fun _ => recvAt_le_countAt h0))

/-- **The heart of record matching.** If no guest instance sends `m` and the host is silent there,
    then nobody receives it either: the guests' net is `-(recvCount)`, which is an honest natural
    below `p` and so cannot wrap to zero. -/
theorem recvCount_eq_zero_of_no_send [Fact p.Prime] {host : Host p} {G : Guest p}
    {a : VmAssignment p ⟨host, G⟩} {m : BusMessage p} (hsat : VmSat ⟨host, G⟩ a)
    (h0 : (1 : ZMod p) ≠ 0) (h1 : (1 : ZMod p) ≠ -1)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ host.maxInteractions)
    (hpm : ∀ (t : Fin G.length), ∀ asg ∈ a.guestAssignments t, (G.get t).pmAt asg m)
    (hS : a.guestAssignments.sendCount m = 0)
    (hhost : a.hostAssignment.busEffect m = 0) :
    a.guestAssignments.recvCount m = 0 := by
  have hbal := hsat.balances m
  rw [busEffect_apply, hhost, add_zero,
    guestNet_eq_send_sub_recv h0 h1 hpm, hS] at hbal
  have hzero : ((a.guestAssignments.recvCount m : ℕ) : ZMod p) = 0 := by
    simp only [Nat.cast_zero, zero_sub, neg_eq_zero] at hbal
    exact hbal
  have hle : a.guestAssignments.recvCount m ≤ host.maxInstances * host.maxInteractions :=
    le_trans (recvCount_le_count h0)
      (le_trans (guestCount_le hSize) (Nat.mul_le_mul_right _ hsat.withinBudget))
  have hlt : a.guestAssignments.recvCount m < p := by
    have hmo := host.noMultOverflow
    have : host.maxInstances * host.maxInteractions
        = host.maxInteractions * host.maxInstances := Nat.mul_comm _ _
    omega
  exact VmChain.natCast_eq_zero_of_lt hlt hzero

--------- The rely's own message list, bus by bus ---------

/-- The list `Circuit.admissible` is stated about — the chip's active stateful interactions —
    restricted to one bus. -/
def admissibleAt (c : Circuit p) (asg : ChipAssignment p) (b : Nat) :
    List (BusInteraction (ZMod p)) :=
  ((c.busInteractions.map (fun bi => bi.eval asg)).filter
    (fun m => decide (m.multiplicity ≠ 0) &&
      (openVmBusSemanticsOF p defaultBusMap none).isStateful m.busId)).filter
    (fun m => decide (m.busId = b))

/-- On a stateful bus, counting a nonzero multiplicity over `admissibleAt` is the same as counting
    it over the chip's raw multiplicities at that message: the two extra filters
    (`multiplicity ≠ 0`, `isStateful`) are implied. -/
theorem countP_admissibleAt {c : Circuit p} {asg : ChipAssignment p} {b : Nat}
    {Q : List (ZMod p)} {v : ZMod p} (hv : v ≠ 0)
    (hst : (openVmBusSemanticsOF p defaultBusMap none).isStateful b = true) :
    (admissibleAt c asg b).countP (fun m => decide (m.multiplicity = v) && decide (Q = m.payload))
      = (c.multsAt asg (b, Q)).countP (fun x => decide (x = v)) := by
  have hL : (admissibleAt c asg b).countP
        (fun m => decide (m.multiplicity = v) && decide (Q = m.payload))
      = (c.busInteractions.map (fun bi => bi.eval asg)).countP
        (fun m => decide (m.multiplicity = v) && decide (Q = m.payload) && decide (m.busId = b)
          && (decide (m.multiplicity ≠ 0) &&
            (openVmBusSemanticsOF p defaultBusMap none).isStateful m.busId)) := by
    rw [admissibleAt, List.countP_filter, List.countP_filter]
  have hR : (c.multsAt asg (b, Q)).countP (fun x => decide (x = v))
      = (c.busInteractions.map (fun bi => bi.eval asg)).countP
        (fun m => decide (m.multiplicity = v) && decide ((m.busId, m.payload) = (b, Q))) := by
    rw [Circuit.multsAt, List.countP_map, List.countP_filter]
    rfl
  rw [hL, hR]
  refine List.countP_congr (fun m _ => ?_)
  simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hmv, hQ⟩, hb⟩, -⟩
    exact ⟨hmv, hb, hQ.symm⟩
  · rintro ⟨hmv, hb, hQ⟩
    exact ⟨⟨⟨hmv, hQ.symm⟩, hb⟩, hmv ▸ hv, hb ▸ hst⟩

--------- Naming the interaction behind a count ---------

/-- A nonzero signed count at `m` names an interaction carrying it. -/
theorem exists_index_of_countP {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {v : ZMod p} (h : (c.multsAt asg m).countP (fun x => decide (x = v)) ≠ 0) :
    ∃ i : Fin c.busInteractions.length, c.msgAt asg i = m ∧ c.multAt asg i = v := by
  classical
  obtain ⟨w, hw, hwv⟩ : ∃ x ∈ c.multsAt asg m, decide (x = v) = true := by
    by_contra hc
    exact h (List.countP_eq_zero.mpr (fun x hx hp => hc ⟨x, hx, hp⟩))
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hw
  obtain ⟨hbi1, hbi2⟩ := List.mem_filter.mp hbi
  obtain ⟨bi0, hbi0, hbieq⟩ := List.mem_map.mp hbi1
  obtain ⟨i, hi⟩ := List.get_of_mem hbi0
  refine ⟨i, ?_, ?_⟩
  · rw [Circuit.msgAt, hi, hbieq]
    exact of_decide_eq_true hbi2
  · rw [Circuit.multAt, hi, hbieq]
    exact of_decide_eq_true hwv

theorem exists_send_index {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h : c.sendAt asg m ≠ 0) :
    ∃ i : Fin c.busInteractions.length, c.msgAt asg i = m ∧ c.multAt asg i = 1 :=
  exists_index_of_countP h

/-- …and conversely, an interaction carrying `m` at multiplicity `v` makes the chip's signed
    count at `v` nonzero. -/
theorem countP_ne_zero_of_index {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {v : ZMod p} {i : Fin c.busInteractions.length} (hmsg : c.msgAt asg i = m)
    (hmult : c.multAt asg i = v) :
    (c.multsAt asg m).countP (fun x => decide (x = v)) ≠ 0 := by
  classical
  have hmem : v ∈ c.multsAt asg m := by
    refine List.mem_map.mpr ⟨(c.busInteractions.get i).eval asg, ?_, hmult⟩
    exact List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩, decide_eq_true hmsg⟩
  exact fun hz => (List.countP_eq_zero.mp hz) v hmem (by simp)

theorem sendAt_ne_zero_of_index {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {i : Fin c.busInteractions.length} (hmsg : c.msgAt asg i = m)
    (hmult : c.multAt asg i = 1) : c.sendAt asg m ≠ 0 :=
  countP_ne_zero_of_index hmsg hmult

/-- …and at the level of a whole run, one receiving interaction makes `recvCount` nonzero — the
    hypothesis `openVmHost_recv_has_sender` asks for. -/
theorem recvCount_ne_zero_of_index {G : Guest p} {gA : GuestAssignment p G} {m : BusMessage p}
    (t : Fin G.length) {asg : ChipAssignment p} (hasg : asg ∈ gA t)
    {i : Fin (G.get t).busInteractions.length} (hmsg : (G.get t).msgAt asg i = m)
    (hmult : (G.get t).multAt asg i = -1) : gA.recvCount m ≠ 0 := by
  classical
  have hpos : (G.get t).recvAt asg m ≠ 0 := countP_ne_zero_of_index hmsg hmult
  intro hzero
  have h1 := (Finset.sum_eq_zero_iff.mp hzero) t (Finset.mem_univ t)
  exact hpos (List.sum_eq_zero_iff.mp h1 _ (List.mem_map.mpr ⟨asg, hasg, rfl⟩))

--------- The execution bridge's own admissibility ---------

theorem sendAt_le_length {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p} :
    c.sendAt asg m ≤ c.busInteractions.length := by
  refine le_trans List.countP_le_length ?_
  rw [Circuit.multsAt, List.length_map]
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_map]

theorem recvAt_le_length {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p} :
    c.recvAt asg m ≤ c.busInteractions.length := by
  refine le_trans List.countP_le_length ?_
  rw [Circuit.multsAt, List.length_map]
  refine le_trans (List.length_filter_le _ _) ?_
  rw [List.length_map]

/-- Two naturals below `p` with equal casts are equal. -/
theorem natCast_inj_of_lt [Fact p.Prime] {A B : ℕ} (hA : A < p) (hB : B < p)
    (h : ((A : ℕ) : ZMod p) = ((B : ℕ) : ZMod p)) : A = B := by
  haveI : NeZero p := ⟨(Nat.Prime.one_lt (Fact.out)).ne_bot⟩
  rw [← ZMod.val_cast_of_lt hA, ← ZMod.val_cast_of_lt hB, h]

/-- **The execution-bridge half of the order-free memory discipline, from `StepLayout` alone.**

    The bridge is declared memory-shaped with a single global cell (`memShapeOf`'s
    `.executionBridge` arm, `addressFields := []`), so `excessAt` there is just the step's receives
    in excess of its sends. `bridgeRecv`/`bridgeSend`/`bridgeNoOther` pin those nets to `-1`, `+1`
    and `0`, and the counts are honest naturals below `p`, so exactly one record enters: the
    `(pcFrom, tStart)` the step receives. No global argument is needed — unlike the memory bus. -/
theorem openVm_admissibleBridge [Fact p.Prime] {c : Circuit p} {asg : ChipAssignment p}
    {maxWindow maxLookback : ℕ}
    (L : StepLayout c (openVmGuestRules defaultBusMap openVmMemBusId) asg openVmMemAddress
      maxWindow maxLookback)
    (h0 : (1 : ZMod p) ≠ 0) (h1 : (1 : ZMod p) ≠ -1)
    (hsize : c.busInteractions.length + 1 < p)
    (hpm : ∀ Q : List (ZMod p), c.pmAt asg ((openVmExecBusId, Q) : BusMessage p)) :
    admissibleMemoryBusM ⟨[], .receiveThenSend⟩
      (↑(admissibleAt c asg openVmExecBusId) : Multiset (BusInteraction (ZMod p))) := by
  classical
  intro addr
  refine card_excessAt_le_one_of_counts (A := [L.pcFrom, L.tStart]) (fun Q => ?_)
  by_cases haddr : addr = ([] : List (Option (ZMod p)))
  · subst haddr
    -- The address condition is vacuous here, so the counts are the chip's own send/receive counts.
    have hrw : ∀ v : ZMod p, v ≠ 0 →
        (admissibleAt c asg openVmExecBusId).countP (fun m =>
            decide (m.multiplicity = v ∧
              (⟨[], .receiveThenSend⟩ : MemoryBusShape).address m = ([] : List (Option (ZMod p))))
            && decide (Q = m.payload))
          = (c.multsAt asg ((openVmExecBusId, Q) : BusMessage p)).countP
              (fun x => decide (x = v)) := by
      intro v hv
      rw [← countP_admissibleAt (c := c) (asg := asg) (b := openVmExecBusId) (Q := Q) hv rfl]
      exact List.countP_congr (fun m _ => by simp [MemoryBusShape.address])
    rw [show ((⟨[], .receiveThenSend⟩ : MemoryBusShape).setNewMult : ZMod p) = 1 from rfl,
      hrw 1 h0, hrw (-1) (fun h => h0 (neg_eq_zero.mp h))]
    show c.recvAt asg _ ≤ c.sendAt asg _ + _
    have heff := allEffects_eq_send_sub_recv h0 h1 (hpm Q)
    have hSle : c.sendAt asg ((openVmExecBusId, Q) : BusMessage p)
        ≤ c.busInteractions.length := sendAt_le_length
    have hRle : c.recvAt asg ((openVmExecBusId, Q) : BusMessage p)
        ≤ c.busInteractions.length := recvAt_le_length
    by_cases hQA : Q = [L.pcFrom, L.tStart]
    · rw [if_pos hQA]
      rw [show c.allEffects asg ((openVmExecBusId, Q) : BusMessage p) = -1 from hQA ▸ L.bridgeRecv]
        at heff
      have hcast : ((c.sendAt asg ((openVmExecBusId, Q) : BusMessage p) + 1 : ℕ) : ZMod p)
          = ((c.recvAt asg ((openVmExecBusId, Q) : BusMessage p) : ℕ) : ZMod p) := by
        push_cast
        linear_combination -heff
      have := natCast_inj_of_lt (by omega) (by omega) hcast
      omega
    · rw [if_neg hQA]
      by_cases hQB : Q = [L.pcTo, L.tStart + (L.tWindow : ZMod p)]
      · rw [show c.allEffects asg ((openVmExecBusId, Q) : BusMessage p) = 1
          from hQB ▸ L.bridgeSend] at heff
        have hcast : ((c.sendAt asg ((openVmExecBusId, Q) : BusMessage p) : ℕ) : ZMod p)
            = ((c.recvAt asg ((openVmExecBusId, Q) : BusMessage p) + 1 : ℕ) : ZMod p) := by
          push_cast
          linear_combination -heff
        have := natCast_inj_of_lt (by omega) (by omega) hcast
        omega
      · rw [show c.allEffects asg ((openVmExecBusId, Q) : BusMessage p) = 0
          from L.bridgeNoOther _ rfl (fun h => hQA (congrArg Prod.snd h))
            (fun h => hQB (congrArg Prod.snd h))] at heff
        have hcast : ((c.sendAt asg ((openVmExecBusId, Q) : BusMessage p) : ℕ) : ZMod p)
            = ((c.recvAt asg ((openVmExecBusId, Q) : BusMessage p) : ℕ) : ZMod p) := by
          linear_combination -heff
        have := natCast_inj_of_lt (by omega) (by omega) hcast
        omega
  · have hz : ∀ v : ZMod p, (admissibleAt c asg openVmExecBusId).countP (fun m =>
        decide (m.multiplicity = v ∧
          (⟨[], .receiveThenSend⟩ : MemoryBusShape).address m = addr)
        && decide (Q = m.payload)) = 0 := fun v =>
      List.countP_eq_zero.mpr (fun x _ hc => by
        simp only [Bool.and_eq_true, decide_eq_true_eq, MemoryBusShape.address,
          List.map_nil] at hc
        exact haddr hc.1.2.symm)
    rw [hz, hz]
    omega

--------- Placement on the run's clock ---------

/-- `openVmHost_bridge_isolated` restated for a *given* input-chip witness family. The original
    chooses its own; both are pinned to the same `HostAssignment`, so the two agree message by
    message. -/
theorem openVmHost_bridge_isolated_of (P : OpenVmParams p)
    {hA : HostAssignment p (openVmHost P)} (hlegal : hA.satisfies)
    (iR : Fin (hA (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (hA (openVmInputChip P)).get i = busStateOf ((iR i).interactions P.ptrReg 0 1)) :
    ∃ r : ConnectorBoundary p, ∀ m : BusMessage p, m.1 = 0 →
      hA.busEffect m = busStateOf (r.interactions 0) m +
        ∑ i, busStateOf ((iR i).interactions P.ptrReg 0 1) m := by
  obtain ⟨r, iR', hiR', hnet⟩ := openVmHost_bridge_isolated P hlegal
  refine ⟨r, fun m hm => ?_⟩
  rw [hnet m hm]
  refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
  rw [← congrFun (hiR' i) m, congrFun (hiR i) m]

/-- **Every arc of a run's execution bridge starts at an honest natural timestamp inside the
    range OpenVM checks, and no two arcs' windows overlap.** Guest instances get a `StepLayout` —
    the *strong* layout, so callers can use `sendInWindow`, `memPartner` and friends and the
    timestamp equation at the same time — and input-chip instances get their `InputRead.base`.

    Everything here comes off one `bridgeChain`, so it is proved together: the chain is what turns
    the connector's single range check (`ConnectorBoundary.finalTimestampBounded`) into a bound on
    every instance in the run, and its Eulerian structure is what makes the windows disjoint
    (`bridge_windows_disjoint_arc`). Disjointness is what makes a memory send's timestamp name its
    own instance, which is the whole of send-uniqueness. -/
theorem openVmHost_arcsPlaced [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1)) :
    ∃ (L : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
        StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
          ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound)
      (Tg : ((s : Fin G.length) × Fin (a.guestAssignments s).length) → ℕ)
      (Ti : Fin (a.hostAssignment (openVmInputChip P)).length → ℕ),
      (∀ x, 1 + Tg x + (L x).tWindow < openVmTimestampBound ∧
          (L x).tStart = ((1 + Tg x : ℕ) : ZMod p))
      ∧ (∀ i, 1 + Ti i + inputStepWindow < openVmTimestampBound ∧
          (iR i).base = ((1 + Ti i : ℕ) : ZMod p))
      ∧ (∀ x x', x ≠ x' → Tg x + (L x).tWindow ≤ Tg x' ∨ Tg x' + (L x').tWindow ≤ Tg x)
      ∧ (∀ i i', i ≠ i' → Ti i + inputStepWindow ≤ Ti i' ∨ Ti i' + inputStepWindow ≤ Ti i)
      ∧ (∀ x i, Tg x + (L x).tWindow ≤ Ti i ∨ Ti i + inputStepWindow ≤ Tg x) := by
  classical
  have hp := P.windowOk
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  have hNonempty : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      Nonempty (StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound) :=
    fun x => (hGuests _ (List.get_mem G x.1)).stepLayout
      _ (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
      (satisfiesStateless_of_sinks (openVmHost_legalGuest_unpack P) (openVmHost_sinksAreTables P)
        hGuests hsat x.1 _ (List.get_mem _ _))
  set L : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound :=
    fun x => Classical.choice (hNonempty x) with hL
  set S : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound :=
    fun x => (L x) with hS
  obtain ⟨r, hrnet⟩ := openVmHost_bridge_isolated_of P hsat.satisfiesHost iR hiR
  have hbal : ∀ m : BusMessage p, m.1 = 0 →
      a.guestAssignments.busEffect m +
        (∑ i, busStateOf ((iR i).interactions P.ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0 := by
    intro m hm
    have hb := hsat.balances m
    rw [busEffect_apply, hrnet m hm] at hb
    linear_combination hb
  have hcount : (∑ s : Fin G.length, (a.guestAssignments s).length) ≤ P.maxInstances :=
    hsat.withinBudget
  have hcountI : (a.hostAssignment (openVmInputChip P)).length ≤ P.maxInputInstances :=
    hsat.satisfiesHost.withinBound (openVmInputChip P)
  have hconn := r.finalTimestampBounded
  obtain ⟨T, hT, hdisj⟩ :=
    bridge_windows_disjoint_arc a.guestAssignments S iR P.ptrReg r (openVm_negOne_ne_one P) hbal
      P.inputWindowOk hcount hcountI hp
  refine ⟨L, fun x => T (some (.inl x)), fun i => T (some (.inr i)), fun x => ?_, fun i => ?_,
    fun x x' hne => ?_, fun i i' hne => ?_, fun x i => ?_⟩
  · obtain ⟨hbase, hfit⟩ := hT (some (.inl x)) (Option.some_ne_none _)
    refine ⟨?_, hbase⟩
    have hw : bridgeAdv a.guestAssignments S
        (some (.inl x) :
          BridgeArc a.guestAssignments (a.hostAssignment (openVmInputChip P)).length)
        = (L x).tWindow := rfl
    dsimp only
    omega
  · obtain ⟨hbase, hfit⟩ := hT (some (.inr i)) (Option.some_ne_none _)
    refine ⟨?_, hbase⟩
    have hw : bridgeAdv a.guestAssignments S
        (some (.inr i) :
          BridgeArc a.guestAssignments (a.hostAssignment (openVmInputChip P)).length)
        = inputStepWindow := rfl
    dsimp only
    omega
  · exact hdisj (some (.inl x)) (some (.inl x')) (Option.some_ne_none _) (Option.some_ne_none _)
      (by simpa using hne)
  · exact hdisj (some (.inr i)) (some (.inr i')) (Option.some_ne_none _) (Option.some_ne_none _)
      (by simpa using hne)
  · exact hdisj (some (.inl x)) (some (.inr i)) (Option.some_ne_none _) (Option.some_ne_none _)
      (by simp)

--------- What a record inherits from its producer ---------

/-- The two facts the order-free rely needs of a memory record: an honest timestamp inside the
    range OpenVM range-checks (TS_BOUND), and a zero at register `x0` (`x0ReturnsZero`). Both are
    properties of the record itself, so a receive inherits them from whatever sent it. -/
def openVmRecordGood (m : BusMessage p) : Prop :=
  (openVmTimestamp openVmMemBusId m).val < openVmTimestampBound
  ∧ (m.2[0]? = some 1 → m.2[1]? = some 0 →
      m.2[2]? = some 0 ∧ m.2[3]? = some 0 ∧ m.2[4]? = some 0 ∧ m.2[5]? = some 0)

theorem openVmTimestampBound_lt (P : OpenVmParams p) : openVmTimestampBound < p :=
  lt_trans (by norm_num [openVmRankBound, openVmRankShift, openVmTimestampBound,
    openVmTimestampBits]) P.rankWindowOk

/-- A field element that *is* an honest natural below OpenVM's ceiling reads back as one. -/
theorem val_lt_of_cast [Fact p.Prime] (P : OpenVmParams p) {x : ZMod p} {n : ℕ}
    (hx : x = ((n : ℕ) : ZMod p)) (hn : n < openVmTimestampBound) :
    x.val < openVmTimestampBound := by
  haveI : NeZero p := ⟨(Nat.Prime.one_lt (Fact.out)).ne_bot⟩
  rw [hx, ZMod.val_cast_of_lt (lt_trans hn (openVmTimestampBound_lt P))]
  exact hn

/-- The one way this development establishes `openVmRecordGood`: exhibit the record's timestamp as
    an honest natural below the ceiling. -/
theorem openVmRecordGood_of_ts [Fact p.Prime] (P : OpenVmParams p) {m : BusMessage p} {n : ℕ}
    (hts : openVmTimestamp openVmMemBusId m = ((n : ℕ) : ZMod p))
    (hfit : n < openVmTimestampBound)
    (hx0 : m.2[0]? = some 1 → m.2[1]? = some 0 →
      m.2[2]? = some 0 ∧ m.2[3]? = some 0 ∧ m.2[4]? = some 0 ∧ m.2[5]? = some 0) :
    openVmRecordGood m :=
  ⟨val_lt_of_cast P hts hfit, hx0⟩

/-- A base plus a non-negative integer offset, as one honest natural. -/
theorem cast_base_add_offset {T : ℕ} {off : ℤ} (hoff : 0 ≤ off) :
    ((1 + T : ℕ) : ZMod p) + ((off : ℤ) : ZMod p) = ((1 + T + off.toNat : ℕ) : ZMod p) := by
  conv_lhs => rw [← Int.toNat_of_nonneg hoff]
  push_cast
  ring

/-- **A record the initial memory image sends is good.** Its timestamp is `0` (§4.6.2) and its
    `x0` is zero (`memoryInitHostChip`'s third conjunct). -/
theorem openVmHost_initSend_good [Fact p.Prime] (P : OpenVmParams p) {e : BusState p}
    (hcan : (memoryInitHostChip (p := p)).canProduce e) {m : BusMessage p} (hne : e m ≠ 0) :
    openVmRecordGood m := by
  obtain ⟨hshape, -, hx0⟩ := hcan
  obtain ⟨hbus, -, f, -, -, ht, -⟩ := hshape m hne
  refine openVmRecordGood_of_ts P (n := 0) ?_ ?_ (hx0 m hne)
  · simp only [openVmTimestamp, if_pos hbus, ht, Option.getD_some, Nat.cast_zero]
  · norm_num [openVmTimestampBound, openVmTimestampBits]

/-- **A record an input-chip instance sends is good.** Its two memory sends land at `base + 1` and
    `base + 2`, and `bridge_chain_bound_input` puts `base` at an honest natural low enough for
    both. Neither addresses register `0`: the register write-back goes to `ptrReg`
    (`OpenVmParams.ptrRegNeZero`) and the hinted word to address space `2`. -/
theorem openVmHost_inputSend_good [Fact p.Prime] (P : OpenVmParams p) {r : InputRead p} {T : ℕ}
    (hbase : r.base = ((1 + T : ℕ) : ZMod p))
    (hfit : 1 + T + inputStepWindow < openVmTimestampBound)
    {e : BusInteraction (ZMod p)} (he : e ∈ r.interactions P.ptrReg 0 1)
    (hmult : e.multiplicity = 1) (hbus : e.busId = openVmMemBusId) :
    openVmRecordGood (e.busId, e.payload) := by
  have hp2 : 2 < p := lt_trans (by norm_num [openVmTimestampBound, openVmTimestampBits])
    (openVmTimestampBound_lt P)
  have hlen : r.ptrLimbs.toList.length = 4 := by simp
  have hstep : inputStepWindow = 3 := rfl
  rw [InputRead.interactions] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hmult (openVm_negOne_ne_one P)
  · exact absurd hbus (by simp [openVmMemBusId])
  · exact absurd hmult (openVm_negOne_ne_one P)
  · -- the pointer register's write-back, at `base + 1`
    refine openVmRecordGood_of_ts P (n := 1 + T + 1) ?_ (by omega) ?_
    · have h6 : ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[6]?
          = some (r.base + 1) := by simp [hlen]
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[6]?.getD 0 = _
      rw [h6, Option.getD_some, hbase]
      push_cast
      ring
    · rintro - h1
      exfalso
      refine P.ptrRegNeZero ?_
      have h1' : ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[1]?
          = some (P.ptrReg : ZMod p) := by simp [hlen]
      have := h1
      rw [show ((1 : Nat), ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList
        ++ [r.base + 1])).2 = ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList
        ++ [r.base + 1]) from rfl, h1'] at this
      exact Option.some_inj.mp this
  · exact absurd hmult (openVm_negOne_ne_one P)
  · -- the hinted word, at `base + 2`, in address space `2`
    refine openVmRecordGood_of_ts P (n := 1 + T + 2) ?_ (by omega) ?_
    · show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([(2 : ZMod p), r.ptr, r.byte, 0, 0, 0, r.base + 2])[6]?.getD 0 = _
      rw [show ([(2 : ZMod p), r.ptr, r.byte, 0, 0, 0, r.base + 2])[6]? = some (r.base + 2)
        from rfl, Option.getD_some, hbase]
      push_cast
      ring
    · rintro h0 -
      exfalso
      have h2 : ((2 : ZMod p)) = 1 := by
        rw [show ((1 : Nat), [(2 : ZMod p), r.ptr, r.byte, 0, 0, 0, r.base + 2]).2[0]?
          = some (2 : ZMod p) from rfl] at h0
        exact Option.some_inj.mp h0
      exact absurd (by linear_combination h2 : (1 : ZMod p) = 0) one_ne_zero

--------- Record matching ---------

/-- On a stateful bus a guest chip's multiplicities are `0`/`±1` — `Circuit.pmAt`, from
    `legalGuest.polarity`. -/
theorem openVmHost_pmAt (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    {m : BusMessage p} (hm : openVmIsStateful defaultBusMap m.1 = true)
    (t : Fin G.length) : ∀ asg ∈ a.guestAssignments t, (G.get t).pmAt asg m := by
  intro asg hasg bi hbi heq
  have hleg := (hGuests _ (List.get_mem G t)).polarity
  refine hleg asg (hsat.satisfiesGuest t asg hasg) bi hbi ?_
  have hid : bi.busId = m.1 := congrArg Prod.fst heq
  rw [show (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).isStateful
      = openVmIsStateful defaultBusMap from rfl, hid]
  exact hm

/-- **Something in the run sends the memory message `m`.** The three producers that can put a
    `+1` on the memory bus: a guest instance, the initial memory image, or an input-chip
    instance. Everything else the host does there can only receive. -/
def OpenVmSends (P : OpenVmParams p) {G : Guest p} (a : VmAssignment p ⟨openVmHost P, G⟩)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (m : BusMessage p) : Prop :=
  (∃ t : Fin G.length, ∃ asg ∈ a.guestAssignments t, (G.get t).sendAt asg m ≠ 0)
  ∨ (∃ e ∈ a.hostAssignment (openVmMemInitChip P), e m ≠ 0)
  ∨ (∃ i : Fin (a.hostAssignment (openVmInputChip P)).length,
      ∃ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) = m ∧ e.multiplicity = 1)

/-- **Record matching.** If nothing in the run sends a memory message, then nothing receives it
    either — no guest instance, no input-chip instance, and not memory finalization.

    Balance leaves `guestRecv + kf + ki ≡ 0` for honest naturals, `OpenVmParams.budgetOk` keeps the
    sum below `p`, so all three vanish; `openVmHost_memNet_or_sender`'s exact counts then say the
    host chips did not touch `m` at all. -/
theorem openVmHost_no_recv_of_no_send [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) (hns : ¬ OpenVmSends P a iR m) :
    a.guestAssignments.recvCount m = 0
    ∧ (∀ e ∈ a.hostAssignment (openVmMemFinalizeChip P), e m = 0)
    ∧ (∀ i : Fin (a.hostAssignment (openVmInputChip P)).length,
        ∀ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) ≠ m) := by
  classical
  have hg : ¬ (∃ t : Fin G.length, ∃ asg ∈ a.guestAssignments t, (G.get t).sendAt asg m ≠ 0) :=
    fun h => hns (Or.inl h)
  have hinit : ¬ (∃ e ∈ a.hostAssignment (openVmMemInitChip P), e m ≠ 0) :=
    fun h => hns (Or.inr (Or.inl h))
  have hin : ¬ (∃ i : Fin (a.hostAssignment (openVmInputChip P)).length,
      ∃ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) = m ∧ e.multiplicity = 1) :=
    fun h => hns (Or.inr (Or.inr h))
  have hS : a.guestAssignments.sendCount m = 0 := by
    refine Finset.sum_eq_zero (fun t _ => List.sum_eq_zero (fun v hv => ?_))
    obtain ⟨asg, hasg, rfl⟩ := List.mem_map.mp hv
    by_contra hne
    exact hg ⟨t, asg, hasg, hne⟩
  have hst : openVmIsStateful defaultBusMap m.1 = true := by rw [hm]; rfl
  have hpm := openVmHost_pmAt P hGuests hsat hst
  have h0 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h1 : (1 : ZMod p) ≠ -1 := fun h => openVm_negOne_ne_one P h.symm
  obtain ⟨kf, ki, hkf, hki, hFeq, hkfz, hkiz⟩ :
      ∃ kf ki : ℕ, kf ≤ 1 ∧ ki ≤ 6 * P.maxInputInstances ∧
        a.hostAssignment.busEffect m = -((kf + ki : ℕ) : ZMod p) ∧
        (kf = 0 → ∀ e ∈ a.hostAssignment (openVmMemFinalizeChip P), e m = 0) ∧
        (ki = 0 → ∀ i : Fin (a.hostAssignment (openVmInputChip P)).length,
          ∀ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) ≠ m) := by
    rcases openVmHost_memNet_or_sender P hsat.satisfiesHost iR hiR hm with h | h | h
    · exact absurd h hinit
    · exact absurd h hin
    · exact h
  have hbal := hsat.balances m
  rw [busEffect_apply, hFeq, guestNet_eq_send_sub_recv h0 h1 hpm, hS] at hbal
  have hzero : ((a.guestAssignments.recvCount m + (kf + ki) : ℕ) : ZMod p) = 0 := by
    push_cast
    push_cast at hbal
    linear_combination -hbal
  have hle : a.guestAssignments.recvCount m ≤ P.maxInstances * P.maxInteractions :=
    le_trans (recvCount_le_count h0)
      (le_trans (guestCount_le (fun c hc => (hGuests c hc).size))
        (Nat.mul_le_mul_right _ hsat.withinBudget))
  have hlt : a.guestAssignments.recvCount m + (kf + ki) < p := by
    have hb := P.budgetOk
    have hcomm : P.maxInstances * P.maxInteractions = P.maxInteractions * P.maxInstances :=
      Nat.mul_comm _ _
    omega
  have hz := VmChain.natCast_eq_zero_of_lt hlt hzero
  exact ⟨by omega, hkfz (by omega), hkiz (by omega)⟩

/-- **Every memory message a realized guest instance receives is sent by something in the run.**
    The contrapositive of `openVmHost_no_recv_of_no_send`. -/
theorem openVmHost_recv_has_sender [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {m : BusMessage p} (hm : m.1 = openVmMemBusId)
    (hrecv : a.guestAssignments.recvCount m ≠ 0) :
    OpenVmSends P a iR m := by
  by_contra hns
  exact hrecv (openVmHost_no_recv_of_no_send P hGuests hsat iR hiR hm hns).1

/-- …and so is every memory message an *input-chip* instance touches. Its two memory receives are
    as much part of the run's record chain as a guest's. -/
theorem openVmHost_inputTouch_has_sender [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {m : BusMessage p} (hm : m.1 = openVmMemBusId)
    {i : Fin (a.hostAssignment (openVmInputChip P)).length} {e : BusInteraction (ZMod p)}
    (he : e ∈ (iR i).interactions P.ptrReg 0 1) (heq : (e.busId, e.payload) = m) :
    OpenVmSends P a iR m := by
  by_contra hns
  exact (openVmHost_no_recv_of_no_send P hGuests hsat iR hiR hm hns).2.2 i e he heq

--------- Every record a realized instance touches is good ---------

theorem openVmHost_inputWitnesses (P : OpenVmParams p)
    {hA : HostAssignment p (openVmHost P)} (hlegal : hA.satisfies) :
    ∃ iR : Fin (hA (openVmInputChip P)).length → InputRead p,
      ∀ i, (hA (openVmInputChip P)).get i = busStateOf ((iR i).interactions P.ptrReg 0 1) := by
  classical
  have hchoice : ∀ i : Fin (hA (openVmInputChip P)).length, ∃ r : InputRead p,
      (hA (openVmInputChip P)).get i = busStateOf (r.interactions P.ptrReg 0 1) :=
    fun i => hlegal.producible (openVmInputChip P) _ (List.get_mem _ _)
  exact ⟨fun i => (hchoice i).choose, fun i => (hchoice i).choose_spec⟩

/-- **A record a guest instance sends is good.** `sendInWindow` puts the send at a non-negative
    offset inside the step's own window, `openVmHost_arcsPlaced` puts the window's base at an
    honest natural, and `legalGuest.x0Zero` is the `x0` half. -/
theorem openVmHost_guestSend_good [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    {L : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
        StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
          ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound}
    (hL : ∀ x, ∃ T : ℕ, 1 + T + (L x).tWindow < openVmTimestampBound ∧
        (L x).tStart = ((1 + T : ℕ) : ZMod p))
    (x : (s : Fin G.length) × Fin (a.guestAssignments s).length)
    {m : BusMessage p} (hm : m.1 = openVmMemBusId)
    (hsend : (G.get x.1).sendAt ((a.guestAssignments x.1).get x.2) m ≠ 0) :
    openVmRecordGood m := by
  obtain ⟨i, hmsg, hmult⟩ := exists_send_index hsend
  have hbusi : ((G.get x.1).busInteractions.get i).busId = openVmMemBusId := by
    have h := congrArg Prod.fst hmsg
    rw [hm] at h
    exact h
  have hstateful :
      (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).isStateful
        ((G.get x.1).busInteractions.get i).busId = true := by
    rw [hbusi]; rfl
  have hact : (G.get x.1).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId)
      ((a.guestAssignments x.1).get x.2) i := ⟨hstateful, by rw [hmult]; exact one_ne_zero⟩
  have hmemsend : (G.get x.1).memSend (openVmGuestRules defaultBusMap openVmMemBusId)
      ((a.guestAssignments x.1).get x.2) i := ⟨⟨hstateful, hmult⟩, hbusi⟩
  obtain ⟨T, hfit, htstart⟩ := hL x
  obtain ⟨hoff0, hofflt⟩ := (L x).sendInWindow i hmemsend
  obtain ⟨-, -, hts⟩ := (L x).tOffsetMatch i hact
  refine openVmRecordGood_of_ts P (n := 1 + T + ((L x).tOffset i).toNat) ?_ (by omega) ?_
  · rw [← hmsg]
    show (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).getTimestamp
      ((G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) i) = _
    rw [hts, htstart, cast_base_add_offset hoff0]
  · rw [← hmsg]
    exact (hGuests _ (List.get_mem G x.1)).x0Zero _
      (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
      (satisfiesStateless_of_sinks (openVmHost_legalGuest_unpack P) (openVmHost_sinksAreTables P)
        hGuests hsat x.1 _ (List.get_mem _ _))
      i hmemsend

/-- **Every memory record a realized guest instance touches is good** — sends by their own
    placement, receives by record matching plus the goodness of whichever of the three producers
    supplied them. This is TS_BOUND and `x0ReturnsZero` for the memory bus in one statement. -/
theorem openVmHost_recordGood [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (t : Fin G.length) {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    (i : Fin (G.get t).busInteractions.length)
    (hact : (G.get t).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg i)
    (hbus : ((G.get t).busInteractions.get i).busId = openVmMemBusId) :
    openVmRecordGood ((G.get t).msgAt asg i) := by
  classical
  obtain ⟨jx, hjx⟩ := List.get_of_mem hasg
  subst hjx
  obtain ⟨iR, hiR⟩ := openVmHost_inputWitnesses P hsat.satisfiesHost
  obtain ⟨L, Tg, Ti, hgP, hiP, -, -, -⟩ := openVmHost_arcsPlaced P hGuests hsat iR hiR
  have hL : ∀ x, ∃ T : ℕ, 1 + T + (L x).tWindow < openVmTimestampBound ∧
      (L x).tStart = ((1 + T : ℕ) : ZMod p) := fun x => ⟨Tg x, (hgP x).1, (hgP x).2⟩
  have hm : ((G.get t).msgAt ((a.guestAssignments t).get jx) i).1 = openVmMemBusId := hbus
  have hpol := (hGuests _ (List.get_mem G t)).polarity
    ((a.guestAssignments t).get jx) (hsat.satisfiesGuest t _ (List.get_mem _ jx))
    ((G.get t).busInteractions.get i) (List.get_mem _ i) hact.1
  rcases hpol with h | h | h
  · exact absurd h hact.2
  · exact openVmHost_guestSend_good P hGuests hsat hL ⟨t, jx⟩ hm
      (sendAt_ne_zero_of_index (i := i) rfl h)
  · rcases openVmHost_recv_has_sender P hGuests hsat iR hiR hm
      (recvCount_ne_zero_of_index (gA := a.guestAssignments) t
        (asg := (a.guestAssignments t).get jx) (List.get_mem _ _) (i := i) rfl h)
      with hg | hin | hinp
    · obtain ⟨t', asg', hasg', hsend⟩ := hg
      obtain ⟨jx', hjx'⟩ := List.get_of_mem hasg'
      subst hjx'
      exact openVmHost_guestSend_good P hGuests hsat hL ⟨t', jx'⟩ hm hsend
    · obtain ⟨e, he, hne⟩ := hin
      exact openVmHost_initSend_good P
        (hsat.satisfiesHost.producible (openVmMemInitChip P) e he) hne
    · obtain ⟨i', e, he, heq, hone⟩ := hinp
      obtain ⟨hfit, hbase⟩ := hiP i'
      have hbe : e.busId = openVmMemBusId := by
        rw [← hm, ← heq]
      exact heq ▸ openVmHost_inputSend_good P hbase hfit he hone hbe

--------- Reading the rely's own message list ---------

/-- A message in the list `Circuit.admissible` is stated about names an interaction of the chip
    that is active and on a stateful bus. -/
theorem openVm_mem_admissible_msgs {c : Circuit p} {asg : ChipAssignment p}
    {m : BusInteraction (ZMod p)}
    (hmem : m ∈ (c.busInteractions.map (fun bi => bi.eval asg)).filter
      (fun m => decide (m.multiplicity ≠ 0) &&
        (openVmBusSemanticsOF p defaultBusMap none).isStateful m.busId)) :
    ∃ i : Fin c.busInteractions.length,
      c.activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg i ∧
      (c.busInteractions.get i).eval asg = m := by
  obtain ⟨hm1, hm2⟩ := List.mem_filter.mp hmem
  obtain ⟨bi, hbi, hbieq⟩ := List.mem_map.mp hm1
  obtain ⟨i, hi⟩ := List.get_of_mem hbi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm2
  have hid : bi.busId = m.busId := by rw [← hbieq]; rfl
  refine ⟨i, ⟨?_, ?_⟩, by rw [hi, hbieq]⟩
  · show openVmIsStateful defaultBusMap ((c.busInteractions.get i)).busId = true
    rw [hi, hid]
    exact hm2.2
  · rw [Circuit.multAt, hi, hbieq]
    exact hm2.1

/-- The only buses `defaultBusMap` declares memory-shaped are memory itself (timestamp in slot 6)
    and the execution bridge (slot 1). -/
theorem memTsFieldOf_default {busId tsField : Nat}
    (h : memTsFieldOf defaultBusMap busId = some tsField) :
    (busId = openVmMemBusId ∧ tsField = 6) ∨ (busId = openVmExecBusId ∧ tsField = 1) := by
  match busId with
  | 0 => exact Or.inr ⟨rfl, by simpa [memTsFieldOf, defaultBusMap] using h.symm⟩
  | 1 => exact Or.inl ⟨rfl, by simpa [memTsFieldOf, defaultBusMap] using h.symm⟩
  | 2 | 3 | 4 | 5 | 6 | 7 => simp [memTsFieldOf, defaultBusMap] at h
  | (n + 8) => simp [memTsFieldOf, defaultBusMap] at h

/-- **An execution-bridge state a realized instance touches carries an honest timestamp.** The
    clause that makes this true is `StepLayout.negOffsetOnlyMemRecv`: without it a chip may
    carry a cancelling pair of bridge messages at an offset of `-(2^29 - 1)`, where the timestamp
    has wrapped — `Audit/BridgeOffsetGap.lean` exhibits exactly that. -/
theorem openVmHost_bridgeGood [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (t : Fin G.length) {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    (i : Fin (G.get t).busInteractions.length)
    (hact : (G.get t).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId) asg i)
    (hbus : ((G.get t).busInteractions.get i).busId = openVmExecBusId) :
    (openVmTimestamp openVmMemBusId ((G.get t).msgAt asg i)).val < openVmTimestampBound := by
  classical
  obtain ⟨jx, hjx⟩ := List.get_of_mem hasg
  subst hjx
  obtain ⟨iR, hiR⟩ := openVmHost_inputWitnesses P hsat.satisfiesHost
  obtain ⟨L, Tg, -, hgP, -, -, -, -⟩ := openVmHost_arcsPlaced P hGuests hsat iR hiR
  obtain ⟨hfit, htstart⟩ := hgP ⟨t, jx⟩
  have hoff0 : 0 ≤ (L ⟨t, jx⟩).tOffset i := by
    by_contra hneg
    have hmem := ((L ⟨t, jx⟩).negOffsetOnlyMemRecv i hact (by omega)).1
    rw [hbus] at hmem
    have h01 : (0 : Nat) = 1 := hmem
    omega
  obtain ⟨-, hoffle, hts⟩ := (L ⟨t, jx⟩).tOffsetMatch i hact
  refine val_lt_of_cast P (n := 1 + Tg ⟨t, jx⟩ + ((L ⟨t, jx⟩).tOffset i).toNat) ?_ (by omega)
  show (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).getTimestamp
    ((G.get t).msgAt ((a.guestAssignments t).get jx) i) = _
  rw [hts, htstart, cast_base_add_offset hoff0]

/-- The only buses `defaultBusMap` declares memory-shaped, with their shapes. -/
theorem memShapeOf_default {busId : Nat} {shape : MemoryBusShape}
    (h : memShapeOf defaultBusMap busId = some shape) :
    (busId = openVmMemBusId ∧ shape = ⟨[0, 1], .receiveThenSend⟩) ∨
    (busId = openVmExecBusId ∧ shape = ⟨[], .receiveThenSend⟩) := by
  match busId with
  | 0 => exact Or.inr ⟨rfl, by simpa [memShapeOf, defaultBusMap] using h.symm⟩
  | 1 => exact Or.inl ⟨rfl, by simpa [memShapeOf, defaultBusMap] using h.symm⟩
  | 2 | 3 | 4 | 5 | 6 | 7 => simp [memShapeOf, defaultBusMap] at h
  | (n + 8) => simp [memShapeOf, defaultBusMap] at h

/-- A run that realizes any instance at all has `1 ≤ maxInstances`, so `OpenVmParams.budgetOk`
    bounds one chip's interaction count on its own. -/
theorem openVmHost_maxInteractions_lt [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (t : Fin G.length) {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t) :
    P.maxInteractions + 1 < p := by
  classical
  have h1 : 1 ≤ (a.guestAssignments t).length := List.length_pos_of_mem hasg
  have h2 : (a.guestAssignments t).length ≤ P.maxInstances :=
    le_trans (Finset.single_le_sum
      (f := fun s : Fin G.length => (a.guestAssignments s).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)) hsat.withinBudget
  have h3 : P.maxInteractions ≤ P.maxInteractions * P.maxInstances :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hb := P.budgetOk
  omega

end ApcOptimizer.OpenVM
