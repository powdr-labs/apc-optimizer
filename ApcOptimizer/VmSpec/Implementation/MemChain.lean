import ApcOptimizer.VmSpec.Implementation.Forces

set_option autoImplicit false

/-! # The run's memory records, counted — and `Host.forcesAdmissible`

    `Implementation/Forces.lean` places every instance of a run on the execution bridge's clock and
    matches every memory receive to a producer. This file does the counting that turns those into
    the order-free memory discipline, and carries `openVmHost_forcesAdmissible` — the VM-level
    completeness theorem's last assumption, now discharged.

    ## The two global invariants

    * **Send-uniqueness** (`runSendCount_le_one`): no memory record is written twice in a run. A
      guest send sits at a non-negative offset inside its own instance's window (`sendInWindow`),
      an input-chip send at `base + 1` or `base + 2` inside its own, and the initial image at
      timestamp `0` — before every window. The windows are pairwise disjoint
      (`bridge_windows_disjoint_arc`), so a record's timestamp names the instance that wrote it,
      and inside one instance `sendTimesDistinct` allows one send per address and tick. This is
      §4.6's "if and only if" for a single segment.
    * **Receive-uniqueness** (`runRecvCount_le_one`): hence no record is read back twice, by bus
      balance as an equation between honest naturals (`runSend_eq_runRecv`), with
      `OpenVmParams.budgetOk` keeping both counts below `p`.

    ## The counting argument

    Fix an address and read every memory interaction in the run as half of an *access pair*
    `(receive at t_prev, send at t)` with `t_prev < t` (§4.6.1) — `RunAcc` is the index of those
    pairs, guest and input-chip alike, and `recvT_lt_sendT` is the ordering. For a threshold `τ`
    write `A` for the accesses whose receive precedes it and `B` for those whose send does; since
    `t_prev < t`, `B ⊆ A`.

    Sending each `c ∈ A` to the producer of the record it reads (`exists_producer`, i.e. record
    matching) lands in `B ⊎ {the initial image}`: the producer's send happens exactly when `c`'s
    receive does, so it precedes `τ` too. The map is injective, because a record is read back at
    most once in a run (`acc_inj`) and the initial image holds one record per address. Hence
    `A.card ≤ B.card + 1`, so `A \ B` — the accesses *crossing* `τ` — has at most one element
    (`crossing_le_one`). This is the identity `X(τ) + fin(τ) = init(τ) ≤ 1`, run as an injection
    rather than as a sum over messages.

    Take `τ` to be one instance's window start. Its accesses crossing `τ` are exactly the ones
    reading a record older than its window, and there is at most one; everything it reads from
    *inside* the window it wrote itself, since no other producer writes there
    (`inWindow_sender_is_own`). That is `card (excessAt …) ≤ 1` — `openVm_admissibleMem`.

    No per-address chain decomposition is needed, and — unlike the bridge — no `Chain.lean`
    machinery: `Chain.totalLt` wants `∑ adv < p`, and a memory access advances by up to the
    lookback `2 ^ 29` with no bound on how many accesses share an address. -/

namespace ApcOptimizer.OpenVM

open ApcOptimizer.OpenVM.OrderFree

variable {p : ℕ}

--------- Signed counting on an interaction list ---------

/-- How many of a list's interactions send `m`. -/
def sendCountOf (l : List (BusInteraction (ZMod p))) (m : BusMessage p) : ℕ :=
  l.countP (fun e => decide ((e.busId, e.payload) = m) && decide (e.multiplicity = 1))

/-- …and how many receive it. -/
def recvCountOf (l : List (BusInteraction (ZMod p))) (m : BusMessage p) : ℕ :=
  l.countP (fun e => decide ((e.busId, e.payload) = m) && decide (e.multiplicity = -1))

theorem sendCountOf_le (l : List (BusInteraction (ZMod p))) (m : BusMessage p) :
    sendCountOf l m ≤ l.length :=
  List.countP_le_length

theorem recvCountOf_le (l : List (BusInteraction (ZMod p))) (m : BusMessage p) :
    recvCountOf l m ≤ l.length :=
  List.countP_le_length

theorem no_send_of_sendCountOf_zero {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : sendCountOf l m = 0) :
    ∀ e ∈ l, (e.busId, e.payload) = m → e.multiplicity ≠ 1 := by
  intro e he heq hmult
  exact absurd (by simp [heq, hmult]) (List.countP_eq_zero.mp h e he)

theorem no_recv_of_recvCountOf_zero {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : recvCountOf l m = 0) :
    ∀ e ∈ l, (e.busId, e.payload) = m → e.multiplicity ≠ -1 := by
  intro e he heq hmult
  exact absurd (by simp [heq, hmult]) (List.countP_eq_zero.mp h e he)

/-- **A list of `±1` interactions nets its sends minus its receives at every message.** -/
theorem busStateOf_eq_send_sub_recv {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h1 : (1 : ZMod p) ≠ -1)
    (h : ∀ e ∈ l, (e.busId, e.payload) = m → e.multiplicity = 1 ∨ e.multiplicity = -1) :
    busStateOf l m = ((sendCountOf l m : ℕ) : ZMod p) - ((recvCountOf l m : ℕ) : ZMod p) := by
  induction l with
  | nil => simp [busStateOf_nil, sendCountOf, recvCountOf]
  | cons a t ih =>
    have iht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    rw [busStateOf_cons, sendCountOf, recvCountOf, List.countP_cons, List.countP_cons]
    by_cases ha : (a.busId, a.payload) = m
    · rcases h a (by simp) ha with hv | hv
      · rw [if_pos ha, hv, if_pos (by simp [ha]), if_neg (by simp [ha]; exact h1), iht]
        show _ = ((sendCountOf t m + 1 : ℕ) : ZMod p) - ((recvCountOf t m + 0 : ℕ) : ZMod p)
        push_cast
        ring
      · rw [if_pos ha, hv, if_neg (by simp [ha]; exact fun hc => h1 hc.symm), if_pos (by simp [ha]), iht]
        show _ = ((sendCountOf t m + 0 : ℕ) : ZMod p) - ((recvCountOf t m + 1 : ℕ) : ZMod p)
        push_cast
        ring
    · rw [if_neg ha, if_neg (by simp [ha]), if_neg (by simp [ha]), iht, zero_add]
      rfl

--------- The host's memory traffic, split into sends and receives ---------

/-- Every interaction an `InputRead` describes carries `±1`. -/
theorem inputRead_pm (r : InputRead p) (ptrReg : Nat) :
    ∀ e ∈ r.interactions ptrReg 0 1, e.multiplicity = 1 ∨ e.multiplicity = -1 := by
  intro e he
  rw [InputRead.interactions] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **The host's net at a memory message, split into its sends and its receives.** The four lookup
    chips and the connector are silent on the memory bus; the initial image only sends, memory
    finalization only receives, and an input-chip instance does both. -/
theorem openVmHost_memNet_split (P : OpenVmParams p)
    {hA : HostAssignment p (openVmHost P)} (hlegal : hA.satisfies)
    (iR : Fin (hA (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (hA (openVmInputChip P)).get i = busStateOf ((iR i).interactions P.ptrReg 0 1))
    (h1 : (1 : ZMod p) ≠ -1)
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) :
    hA.busEffect m
      = ((((hA (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) : ℕ) : ZMod p)
          + ((∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m : ℕ) : ZMod p))
        - ((((hA (openVmMemFinalizeChip P)).countP (fun e => decide (e m ≠ 0)) : ℕ) : ZMod p)
          + ((∑ i, recvCountOf ((iR i).interactions P.ptrReg 0 1) m : ℕ) : ZMod p)) := by
  classical
  -- The lookup chips and the connector do not touch the memory bus.
  have hzero : ∀ t : Fin (openVmHost P).chips.length,
      (t : ℕ) ≠ 4 → (t : ℕ) ≠ 5 → (t : ℕ) ≠ 6 →
      ((hA t).map (fun effect => effect m)).sum = 0 := by
    intro t ht4 ht5 ht6
    refine List.sum_eq_zero (fun v hv => ?_)
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    have hleg := hlegal.producible t e he
    by_contra hne
    fin_cases t
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd rfl ht4
    · exact absurd rfl ht5
    · exact absurd rfl ht6
    · obtain ⟨c, hc⟩ := hleg
      exact hne (by
        rw [hc]
        refine busStateOf_eq_zero_of_busId_ne (fun e' he' => ?_)
        rw [hm]
        rw [ConnectorBoundary.interactions] at he'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with rfl | rfl <;> simp [openVmMemBusId])
  -- The initial image only sends, and at most once.
  have hinit : ((hA (openVmMemInitChip P)).map (fun effect => effect m)).sum
      = (((hA (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) : ℕ) : ZMod p) := by
    have hlen : (hA (openVmMemInitChip P)).length ≤ 1 :=
      hlegal.withinBound (openVmMemInitChip P)
    match hc : hA (openVmMemInitChip P), hlen with
    | [], _ => simp
    | [e], _ =>
      have hleg := hlegal.producible (openVmMemInitChip P) e
        (by rw [hc]; exact List.mem_singleton_self e)
      by_cases hne : e m = 0
      · simp [hne]
      · simp [(hleg.1 m hne).2.1]
  -- Memory finalization only receives, and at most once.
  have hfin : ((hA (openVmMemFinalizeChip P)).map (fun effect => effect m)).sum
      = -(((hA (openVmMemFinalizeChip P)).countP (fun e => decide (e m ≠ 0)) : ℕ) : ZMod p) := by
    have hlen : (hA (openVmMemFinalizeChip P)).length ≤ 1 :=
      hlegal.withinBound (openVmMemFinalizeChip P)
    match hc : hA (openVmMemFinalizeChip P), hlen with
    | [], _ => simp
    | [e], _ =>
      have hleg := hlegal.producible (openVmMemFinalizeChip P) e
        (by rw [hc]; exact List.mem_singleton_self e)
      by_cases hne : e m = 0
      · simp [hne]
      · simp [(hleg m hne).2.1]
  -- Each input-chip instance sends and receives what its own interaction list says.
  have hinp : ((hA (openVmInputChip P)).map (fun effect => effect m)).sum
      = ((∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m : ℕ) : ZMod p)
        - ((∑ i, recvCountOf ((iR i).interactions P.ptrReg 0 1) m : ℕ) : ZMod p) := by
    rw [list_map_sum_eq_sum_fin, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hiR i]
    exact busStateOf_eq_send_sub_recv h1 (fun e he _ => inputRead_pm (iR i) P.ptrReg e he)
  -- Only those three chips contribute.
  have hne45 : openVmMemInitChip P ≠ openVmMemFinalizeChip P := by
    intro h; have : (4 : ℕ) = 5 := congrArg Fin.val h; omega
  have hne46 : openVmMemInitChip P ≠ openVmInputChip P := by
    intro h; have : (4 : ℕ) = 6 := congrArg Fin.val h; omega
  have hne56 : openVmMemFinalizeChip P ≠ openVmInputChip P := by
    intro h; have : (5 : ℕ) = 6 := congrArg Fin.val h; omega
  have hnet : hA.busEffect m
      = ∑ t : Fin (openVmHost P).chips.length, ((hA t).map (fun effect => effect m)).sum := rfl
  have hsum : (∑ t : Fin (openVmHost P).chips.length, ((hA t).map (fun effect => effect m)).sum)
      = ∑ t ∈ ({openVmMemInitChip P, openVmMemFinalizeChip P, openVmInputChip P} :
          Finset (Fin (openVmHost P).chips.length)),
          ((hA t).map (fun effect => effect m)).sum := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro t _ ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact hzero t (fun h => ht.1 (Fin.ext h)) (fun h => ht.2.1 (Fin.ext h))
      (fun h => ht.2.2 (Fin.ext h))
  rw [hnet, hsum, Finset.sum_insert (by simp [hne45, hne46]),
    Finset.sum_insert (by simp [hne56]), Finset.sum_singleton, hinit, hfin, hinp]
  ring

--------- The run's own send and receive counts ---------

theorem sendAt_le_countAt {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h0 : (1 : ZMod p) ≠ 0) : c.sendAt asg m ≤ c.countAt asg m := by
  refine List.countP_mono_left (fun x _ hx => ?_)
  simp only [decide_eq_true_eq] at hx
  simp only [ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  rw [hx]
  exact h0

theorem sendCount_le_count {G : Guest p} {gA : GuestAssignment p G} {m : BusMessage p}
    (h0 : (1 : ZMod p) ≠ 0) : gA.sendCount m ≤ gA.count m :=
  Finset.sum_le_sum (fun _ _ => list_sum_map_le _ _ _ (fun _ => sendAt_le_countAt h0))

/-- **How often the whole run sends the memory message `m`**: guest instances, the initial memory
    image, and input-chip instances — the three producers `OpenVmSends` names. -/
noncomputable def runSendCount (P : OpenVmParams p) {G : Guest p} (a : VmAssignment p ⟨openVmHost P, G⟩)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (m : BusMessage p) : ℕ :=
  a.guestAssignments.sendCount m
    + (a.hostAssignment (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0))
    + ∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m

/-- …and how often it receives it: guest instances, memory finalization, and input-chip
    instances. -/
noncomputable def runRecvCount (P : OpenVmParams p) {G : Guest p} (a : VmAssignment p ⟨openVmHost P, G⟩)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (m : BusMessage p) : ℕ :=
  a.guestAssignments.recvCount m
    + (a.hostAssignment (openVmMemFinalizeChip P)).countP (fun e => decide (e m ≠ 0))
    + ∑ i, recvCountOf ((iR i).interactions P.ptrReg 0 1) m

theorem runSendCount_lt (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (h0 : (1 : ZMod p) ≠ 0) (m : BusMessage p) : runSendCount P a iR m < p := by
  have hg : a.guestAssignments.sendCount m ≤ P.maxInstances * P.maxInteractions :=
    le_trans (sendCount_le_count h0)
      (le_trans (guestCount_le (fun c hc => (hGuests c hc).size))
        (Nat.mul_le_mul_right _ hsat.withinBudget))
  have hi : (a.hostAssignment (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) ≤ 1 :=
    le_trans List.countP_le_length (hsat.satisfiesHost.withinBound (openVmMemInitChip P))
  have hn : (∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m) ≤ 6 * P.maxInputInstances := by
    have hb : (a.hostAssignment (openVmInputChip P)).length ≤ P.maxInputInstances :=
      hsat.satisfiesHost.withinBound (openVmInputChip P)
    calc (∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m)
        ≤ ∑ _i : Fin (a.hostAssignment (openVmInputChip P)).length, 6 :=
          Finset.sum_le_sum (fun i _ => by
            simpa [InputRead.interactions] using
              sendCountOf_le ((iR i).interactions P.ptrReg 0 1) m)
      _ = (a.hostAssignment (openVmInputChip P)).length * 6 := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ ≤ 6 * P.maxInputInstances := by omega
  have hb := P.budgetOk
  have hcomm : P.maxInstances * P.maxInteractions = P.maxInteractions * P.maxInstances :=
    Nat.mul_comm _ _
  rw [runSendCount]
  omega

theorem runRecvCount_lt (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (h0 : (1 : ZMod p) ≠ 0) (m : BusMessage p) : runRecvCount P a iR m < p := by
  have hg : a.guestAssignments.recvCount m ≤ P.maxInstances * P.maxInteractions :=
    le_trans (recvCount_le_count h0)
      (le_trans (guestCount_le (fun c hc => (hGuests c hc).size))
        (Nat.mul_le_mul_right _ hsat.withinBudget))
  have hi : (a.hostAssignment (openVmMemFinalizeChip P)).countP (fun e => decide (e m ≠ 0)) ≤ 1 :=
    le_trans List.countP_le_length (hsat.satisfiesHost.withinBound (openVmMemFinalizeChip P))
  have hn : (∑ i, recvCountOf ((iR i).interactions P.ptrReg 0 1) m) ≤ 6 * P.maxInputInstances := by
    have hb : (a.hostAssignment (openVmInputChip P)).length ≤ P.maxInputInstances :=
      hsat.satisfiesHost.withinBound (openVmInputChip P)
    calc (∑ i, recvCountOf ((iR i).interactions P.ptrReg 0 1) m)
        ≤ ∑ _i : Fin (a.hostAssignment (openVmInputChip P)).length, 6 :=
          Finset.sum_le_sum (fun i _ => by
            simpa [InputRead.interactions] using
              recvCountOf_le ((iR i).interactions P.ptrReg 0 1) m)
      _ = (a.hostAssignment (openVmInputChip P)).length * 6 := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ ≤ 6 * P.maxInputInstances := by omega
  have hb := P.budgetOk
  have hcomm : P.maxInstances * P.maxInteractions = P.maxInteractions * P.maxInstances :=
    Nat.mul_comm _ _
  rw [runRecvCount]
  omega

/-- **Bus balance, as an equation between honest naturals.** Every memory message the run sends it
    also receives, and exactly as often. `OpenVmParams.budgetOk` is what keeps both counts below
    `p`, so the field equation cannot be wrapping. -/
theorem runSend_eq_runRecv [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) :
    runSendCount P a iR m = runRecvCount P a iR m := by
  have h0 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h1 : (1 : ZMod p) ≠ -1 := fun h => openVm_negOne_ne_one P h.symm
  have hst : openVmIsStateful defaultBusMap m.1 = true := by rw [hm]; rfl
  have hpm := openVmHost_pmAt P hGuests hsat hst
  have hbal := hsat.balances m
  rw [busEffect_apply, guestNet_eq_send_sub_recv h0 h1 hpm,
    openVmHost_memNet_split P hsat.satisfiesHost iR hiR h1 hm] at hbal
  refine natCast_inj_of_lt (runSendCount_lt P hGuests hsat iR h0 m)
    (runRecvCount_lt P hGuests hsat iR h0 m) ?_
  rw [runSendCount, runRecvCount]
  push_cast
  push_cast at hbal
  linear_combination hbal

--------- Sums that are at most one ---------

/-- A finite sum of naturals, each at most one and at most one of them nonzero, is at most one. -/
theorem sum_le_one_of_unique {X : Type} [Fintype X] {f : X → ℕ}
    (h1 : ∀ x, f x ≤ 1) (h2 : ∀ x y, f x ≠ 0 → f y ≠ 0 → x = y) : (∑ x, f x) ≤ 1 := by
  classical
  by_cases h : ∃ x, f x ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h
    rw [Finset.sum_eq_single x₀
      (fun y _ hy => by by_contra hc; exact hy (h2 y x₀ hc hx₀))
      (fun hc => absurd (Finset.mem_univ x₀) hc)]
    exact h1 x₀
  · simp only [not_exists, ne_eq, Decidable.not_not] at h
    simp [h]

/-- A list has at most one entry satisfying `Q` when no two *positions* can both satisfy it. -/
theorem countP_le_one_of_index_unique {α : Type} {l : List α} {Q : α → Bool}
    (h : ∀ i j : Fin l.length, Q l[i] = true → Q l[j] = true → i = j) : l.countP Q ≤ 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons]
    by_cases ha : Q a = true
    · have hz : t.countP Q = 0 := by
        refine List.countP_eq_zero.mpr (fun x hx hQ => ?_)
        obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
        have h0 := h ⟨0, Nat.succ_pos _⟩ ⟨k + 1, by simp; omega⟩
          (by show Q ((a :: t)[0]) = true; rw [List.getElem_cons_zero]; exact ha)
          (by
            show Q ((a :: t)[k + 1]'(by simp; omega)) = true
            rw [List.getElem_cons_succ, hkx]
            exact hQ)
        exact absurd (congrArg Fin.val h0) (by simp)
      simp [hz, ha]
    · refine le_trans (le_of_eq (by simp [ha])) (ih (fun i j hi hj => ?_))
      have h1 := h ⟨i.val + 1, by simp⟩ ⟨j.val + 1, by simp⟩
        (by
          show Q ((a :: t)[i.val + 1]'(by simp)) = true
          rw [List.getElem_cons_succ]
          exact hi)
        (by
          show Q ((a :: t)[j.val + 1]'(by simp)) = true
          rw [List.getElem_cons_succ]
          exact hj)
      exact Fin.ext (by simpa using congrArg Fin.val h1)

--------- Reading uniqueness back as "the same slot" ---------

theorem eq_of_sum_le_one {X : Type} [Fintype X] [DecidableEq X] {f : X → ℕ}
    (h : (∑ x, f x) ≤ 1) {x y : X} (hx : f x ≠ 0) (hy : f y ≠ 0) : x = y := by
  by_contra hne
  have hsub : ({x, y} : Finset X) ⊆ Finset.univ := Finset.subset_univ _
  have h2 : (∑ z ∈ ({x, y} : Finset X), f z) ≤ ∑ z, f z :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hne] at h2
  omega

/-- The converse of `countP_le_one_of_index_unique`: a list with at most one satisfying entry has
    at most one satisfying *position*. -/
theorem index_unique_of_countP_le_one {α : Type} {l : List α} {Q : α → Bool}
    (h : l.countP Q ≤ 1) : ∀ i j : Fin l.length, Q l[i] = true → Q l[j] = true → i = j := by
  induction l with
  | nil => intro i; exact absurd i.isLt (by simp)
  | cons b t ih =>
    rw [List.countP_cons] at h
    intro i j hi hj
    rw [Fin.getElem_fin] at hi hj
    by_cases hb : Q b = true
    · rw [if_pos hb] at h
      have hz : t.countP Q = 0 := by omega
      have hzero : ∀ k : Fin (b :: t).length, Q (b :: t)[k.val] = true → k.val = 0 := by
        intro k hk
        by_contra hk0
        obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := ⟨k.val - 1, by omega⟩
        have hlt : n < t.length := by have := k.isLt; simp only [List.length_cons] at this; omega
        simp only [hn, List.getElem_cons_succ] at hk
        exact absurd hk (by simpa using List.countP_eq_zero.mp hz t[n] (List.getElem_mem hlt))
      exact Fin.ext ((hzero i hi).trans (hzero j hj).symm)
    · rw [if_neg hb] at h
      have hne0 : ∀ k : Fin (b :: t).length, Q (b :: t)[k.val] = true → k.val ≠ 0 := by
        intro k hk hk0
        simp only [hk0, List.getElem_cons_zero] at hk
        exact hb hk
      obtain ⟨ni, hni⟩ : ∃ n, i.val = n + 1 := ⟨i.val - 1, by have := hne0 i hi; omega⟩
      obtain ⟨nj, hnj⟩ : ∃ n, j.val = n + 1 := ⟨j.val - 1, by have := hne0 j hj; omega⟩
      have hilt : ni < t.length := by
        have := i.isLt; simp only [List.length_cons] at this; omega
      have hjlt : nj < t.length := by
        have := j.isLt; simp only [List.length_cons] at this; omega
      simp only [hni, List.getElem_cons_succ] at hi
      simp only [hnj, List.getElem_cons_succ] at hj
      have heq := ih (by omega) ⟨ni, hilt⟩ ⟨nj, hjlt⟩ (by rw [Fin.getElem_fin]; exact hi)
        (by rw [Fin.getElem_fin]; exact hj)
      have hij : ni = nj := congrArg Fin.val heq
      exact Fin.ext (by omega)

--------- Where a memory send sits on the run's clock ---------

/-- A record's timestamp, read as an honest natural below OpenVM's ceiling. At most one natural
    answers to a given record (`tsNat_unique`), which is what lets a send's *position* identify
    the instance that made it. -/
def tsNat (m : BusMessage p) (u : ℕ) : Prop :=
  openVmTimestamp openVmMemBusId m = ((u : ℕ) : ZMod p) ∧ u < openVmTimestampBound

theorem tsNat_unique [Fact p.Prime] (P : OpenVmParams p) {m : BusMessage p} {u v : ℕ}
    (hu : tsNat m u) (hv : tsNat m v) : u = v :=
  natCast_inj_of_lt (lt_trans hu.2 (openVmTimestampBound_lt P))
    (lt_trans hv.2 (openVmTimestampBound_lt P)) (hu.1 ▸ hv.1)

/-- A signed count at `m`, read as a count over the chip's own interaction list. -/
theorem multsAt_countP_rw {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {v : ZMod p} :
    (c.multsAt asg m).countP (fun x => decide (x = v))
      = c.busInteractions.countP (fun bi => decide ((bi.eval asg).multiplicity = v)
          && decide (((bi.eval asg).busId, (bi.eval asg).payload) = m)) := by
  rw [Circuit.multsAt, List.countP_map, List.countP_filter, List.countP_map]
  rfl

/-- A chip sends `m` at most once when no two of its interactions can both do so. -/
theorem sendAt_le_one_of_unique {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h : ∀ i j : Fin c.busInteractions.length, c.msgAt asg i = m → c.multAt asg i = 1 →
      c.msgAt asg j = m → c.multAt asg j = 1 → i = j) : c.sendAt asg m ≤ 1 := by
  rw [Circuit.sendAt, multsAt_countP_rw]
  refine countP_le_one_of_index_unique (fun i j hi hj => ?_)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi hj
  exact h i j hi.2 hi.1 hj.2 hj.1

/-- …and conversely, a chip that receives `m` at most once does so at one interaction. -/
theorem recvIdx_unique {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    (h : c.recvAt asg m ≤ 1) {i j : Fin c.busInteractions.length}
    (hmi : c.msgAt asg i = m) (hvi : c.multAt asg i = -1)
    (hmj : c.msgAt asg j = m) (hvj : c.multAt asg j = -1) : i = j := by
  rw [Circuit.recvAt, multsAt_countP_rw] at h
  exact index_unique_of_countP_le_one h i j
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hvi, hmi⟩)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hvj, hmj⟩)

/-- **A guest memory send sits at a non-negative offset inside its own instance's window**, and
    the record it writes carries the corresponding honest timestamp. -/
theorem openVmHost_guestSend_ts [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    {a : VmAssignment p ⟨openVmHost P, G⟩}
    {L : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
        StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
          ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound}
    {Tg : ((s : Fin G.length) × Fin (a.guestAssignments s).length) → ℕ}
    (hgP : ∀ x, 1 + Tg x + (L x).tWindow < openVmTimestampBound ∧
        (L x).tStart = ((1 + Tg x : ℕ) : ZMod p))
    (x : (s : Fin G.length) × Fin (a.guestAssignments s).length)
    {j : Fin (G.get x.1).busInteractions.length}
    (hsend : (G.get x.1).memSend (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) j) :
    ∃ o : ℕ, (L x).tOffset j = (o : ℤ) ∧ o < (L x).tWindow ∧
      tsNat ((G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) j) (1 + Tg x + o) := by
  obtain ⟨hfit, htstart⟩ := hgP x
  obtain ⟨hoff0, hofflt⟩ := (L x).sendInWindow j hsend
  have hact : (G.get x.1).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId)
      ((a.guestAssignments x.1).get x.2) j := ⟨hsend.1.1, by rw [hsend.1.2]; exact one_ne_zero⟩
  obtain ⟨-, -, hts⟩ := (L x).tOffsetMatch j hact
  refine ⟨((L x).tOffset j).toNat, (Int.toNat_of_nonneg hoff0).symm, by omega, ?_, by omega⟩
  show (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).getTimestamp
    ((G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) j) = _
  rw [hts, htstart, cast_base_add_offset hoff0]

/-- **The initial memory image stamps every record it sends with `0`** (§4.6.2). -/
theorem openVmHost_initSend_ts {e : BusState p}
    (hcan : (memoryInitHostChip (p := p)).canProduce e) {m : BusMessage p} (hne : e m ≠ 0) :
    tsNat m 0 := by
  obtain ⟨hshape, -, -⟩ := hcan
  obtain ⟨hbus, -, f, -, -, ht, -⟩ := hshape m hne
  refine ⟨?_, by norm_num [openVmTimestampBound, openVmTimestampBits]⟩
  simp only [openVmTimestamp, if_pos hbus, ht, Option.getD_some, Nat.cast_zero]

/-- **An input-chip instance's two memory sends sit at `base + 1` and `base + 2`.** -/
theorem openVmHost_inputSend_ts [Fact p.Prime] (P : OpenVmParams p) {r : InputRead p} {T : ℕ}
    (hbase : r.base = ((1 + T : ℕ) : ZMod p))
    (hfit : 1 + T + inputStepWindow < openVmTimestampBound)
    {e : BusInteraction (ZMod p)} (he : e ∈ r.interactions P.ptrReg 0 1)
    (hmult : e.multiplicity = 1) (hbus : e.busId = openVmMemBusId) :
    ∃ o : ℕ, (o = 1 ∨ o = 2) ∧ tsNat (e.busId, e.payload) (1 + T + o) := by
  have hlen : r.ptrLimbs.toList.length = 4 := by simp
  have hstep : inputStepWindow = 3 := rfl
  rw [InputRead.interactions] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hmult (openVm_negOne_ne_one P)
  · exact absurd hbus (by simp [openVmMemBusId])
  · exact absurd hmult (openVm_negOne_ne_one P)
  · refine ⟨1, Or.inl rfl, ?_, by omega⟩
    have h6 : ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[6]?
        = some (r.base + 1) := by simp [hlen]
    show (if (1 : Nat) = openVmMemBusId then _ else _) = _
    rw [if_pos rfl]
    show ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[6]?.getD 0 = _
    rw [h6, Option.getD_some, hbase]
    push_cast
    ring
  · exact absurd hmult (openVm_negOne_ne_one P)
  · refine ⟨2, Or.inr rfl, ?_, by omega⟩
    show (if (1 : Nat) = openVmMemBusId then _ else _) = _
    rw [if_pos rfl]
    show ([(2 : ZMod p), r.ptr, r.byte, 0, 0, 0, r.base + 2])[6]?.getD 0 = _
    rw [show ([(2 : ZMod p), r.ptr, r.byte, 0, 0, 0, r.base + 2])[6]? = some (r.base + 2)
      from rfl, Option.getD_some, hbase]
    push_cast
    ring

--------- Send-uniqueness ---------

/-- **An input-chip instance sends a given memory record at most once.** Its two memory writes go
    to different address spaces — the peeked register to `1`, the hinted word to `2` — so no
    message can be both. -/
theorem inputSendCountOf_le_one [Fact p.Prime] (P : OpenVmParams p) (r : InputRead p)
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) :
    sendCountOf (r.interactions P.ptrReg 0 1) m ≤ 1 := by
  have h1 : (-1 : ZMod p) ≠ 1 := openVm_negOne_ne_one P
  have hp2 : 2 < p := lt_trans (by norm_num [openVmTimestampBound, openVmTimestampBits])
    (openVmTimestampBound_lt P)
  have hkey : ∀ i j : Fin (r.interactions P.ptrReg 0 1).length,
      (fun e => decide ((e.busId, e.payload) = m) && decide (e.multiplicity = 1))
          (r.interactions P.ptrReg 0 1)[i] = true →
      (fun e => decide ((e.busId, e.payload) = m) && decide (e.multiplicity = 1))
          (r.interactions P.ptrReg 0 1)[j] = true → i = j := by
    intro i j hi hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi hj
    have hlist : (r.interactions P.ptrReg 0 1).length = 6 := rfl
    have hlen : r.ptrLimbs.toList.length = 4 := by simp
    have hslot : ∀ k : Fin (r.interactions P.ptrReg 0 1).length,
        ((r.interactions P.ptrReg 0 1)[k].busId,
          (r.interactions P.ptrReg 0 1)[k].payload) = m →
        (r.interactions P.ptrReg 0 1)[k].multiplicity = 1 →
        (k.val = 3 ∧ m.2[0]? = some 1) ∨ (k.val = 5 ∧ m.2[0]? = some 2) := by
      intro k hk1 hk2
      have h6 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 := by
        have := k.isLt
        omega
      rcases h6 with h | h | h | h | h | h
      · rw [show k = ⟨0, by omega⟩ from Fin.ext h] at hk2
        exact absurd hk2 h1
      · rw [show k = ⟨1, by omega⟩ from Fin.ext h] at hk1
        have h01 : (0 : Nat) = openVmMemBusId := (congrArg Prod.fst hk1).trans hm
        exact absurd h01 (by decide)
      · rw [show k = ⟨2, by omega⟩ from Fin.ext h] at hk2
        exact absurd hk2 h1
      · rw [show k = ⟨3, by omega⟩ from Fin.ext h] at hk1
        refine Or.inl ⟨h, ?_⟩
        rw [← hk1]
        rfl
      · rw [show k = ⟨4, by omega⟩ from Fin.ext h] at hk2
        exact absurd hk2 h1
      · rw [show k = ⟨5, by omega⟩ from Fin.ext h] at hk1
        exact Or.inr ⟨h, by rw [← hk1]; rfl⟩
    have hone : ¬ ((1 : ZMod p) = 2) := by
      intro hc
      exact absurd (by linear_combination -hc : (1 : ZMod p) = 0) one_ne_zero
    rcases hslot i hi.1 hi.2 with ⟨hi3, hia⟩ | ⟨hi5, hia⟩ <;>
      rcases hslot j hj.1 hj.2 with ⟨hj3, hja⟩ | ⟨hj5, hja⟩
    · exact Fin.ext (by omega)
    · exact absurd (Option.some_inj.mp (hia.symm.trans hja)) hone
    · exact absurd (Option.some_inj.mp (hja.symm.trans hia)) hone
    · exact Fin.ext (by omega)
  exact countP_le_one_of_index_unique hkey

theorem exists_ne_zero_of_sum_ne_zero {X : Type} [Fintype X] {f : X → ℕ}
    (h : (∑ x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hc
  simp only [not_exists, ne_eq, Decidable.not_not] at hc
  exact h (by simp [hc])

theorem exists_mem_of_countP_ne_zero {α : Type} {l : List α} {Q : α → Bool}
    (h : l.countP Q ≠ 0) : ∃ x ∈ l, Q x = true := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  exact h (List.countP_eq_zero.mpr (fun x hx => by simpa using hc x hx))

/-- **Send-uniqueness: no memory record is written twice in a run.**

    A guest send sits at a non-negative offset inside its instance's own bridge window
    (`sendInWindow`), an input-chip send at `base + 1` or `base + 2` inside its own, and the
    initial image at timestamp `0` — before every window. The windows are pairwise disjoint
    (`bridge_windows_disjoint_arc`), so a record's timestamp names the instance that wrote it; and
    within one instance `sendTimesDistinct` allows one send per address and tick.

    This is §4.6's "if and only if" for a single segment: a message appears in the send multiset
    exactly when the data memory held those values at that time, so the values are a function of
    the address and the time. -/
theorem runSendCount_le_one [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    {L : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
        StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
          ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound}
    {Tg : ((s : Fin G.length) × Fin (a.guestAssignments s).length) → ℕ}
    {Ti : Fin (a.hostAssignment (openVmInputChip P)).length → ℕ}
    (hgP : ∀ x, 1 + Tg x + (L x).tWindow < openVmTimestampBound ∧
        (L x).tStart = ((1 + Tg x : ℕ) : ZMod p))
    (hiP : ∀ i, 1 + Ti i + inputStepWindow < openVmTimestampBound ∧
        (iR i).base = ((1 + Ti i : ℕ) : ZMod p))
    (hgg : ∀ x x', x ≠ x' → Tg x + (L x).tWindow ≤ Tg x' ∨ Tg x' + (L x').tWindow ≤ Tg x)
    (hii : ∀ i i', i ≠ i' → Ti i + inputStepWindow ≤ Ti i' ∨ Ti i' + inputStepWindow ≤ Ti i)
    (hgi : ∀ x i, Tg x + (L x).tWindow ≤ Ti i ∨ Ti i + inputStepWindow ≤ Tg x)
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) :
    runSendCount P a iR m ≤ 1 := by
  classical
  have hstep : inputStepWindow = 3 := rfl
  -- A guest send names an index, and that index is a `memSend`.
  have hmemSend : ∀ (x : (s : Fin G.length) × Fin (a.guestAssignments s).length)
      (j : Fin (G.get x.1).busInteractions.length),
      (G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) j = m →
      (G.get x.1).multAt ((a.guestAssignments x.1).get x.2) j = 1 →
      (G.get x.1).memSend (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) j := by
    intro x j hmsg hmult
    have hbusj : ((G.get x.1).busInteractions.get j).busId = openVmMemBusId := by
      have h := congrArg Prod.fst hmsg
      rw [hm] at h
      exact h
    have hstateful : (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).isStateful
        ((G.get x.1).busInteractions.get j).busId = true := by rw [hbusj]; rfl
    exact ⟨⟨hstateful, hmult⟩, hbusj⟩
  -- …and pins the record's timestamp inside that instance's window.
  have hgTime : ∀ x : (s : Fin G.length) × Fin (a.guestAssignments s).length,
      (G.get x.1).sendAt ((a.guestAssignments x.1).get x.2) m ≠ 0 →
      ∃ u : ℕ, tsNat m u ∧ 1 + Tg x ≤ u ∧ u < 1 + Tg x + (L x).tWindow := by
    intro x hx
    obtain ⟨j, hmsg, hmult⟩ := exists_send_index hx
    obtain ⟨o, -, holt, hts⟩ := openVmHost_guestSend_ts P hgP x (hmemSend x j hmsg hmult)
    exact ⟨1 + Tg x + o, hmsg ▸ hts, by omega, by omega⟩
  -- One send per instance, by `sendTimesDistinct`.
  have hgOne : ∀ x : (s : Fin G.length) × Fin (a.guestAssignments s).length,
      (G.get x.1).sendAt ((a.guestAssignments x.1).get x.2) m ≤ 1 := by
    intro x
    refine sendAt_le_one_of_unique (fun i j hmi hvi hmj hvj => ?_)
    obtain ⟨oi, hoi, -, htsi⟩ := openVmHost_guestSend_ts P hgP x (hmemSend x i hmi hvi)
    obtain ⟨oj, hoj, -, htsj⟩ := openVmHost_guestSend_ts P hgP x (hmemSend x j hmj hvj)
    have hoeq : oi = oj := by
      have := tsNat_unique P (hmi ▸ htsi) (hmj ▸ htsj)
      omega
    refine (L x).sendTimesDistinct i j (hmemSend x i hmi hvi) (hmemSend x j hmj hvj)
      (by rw [hmi, hmj]) ?_
    rw [hoi, hoj, hoeq]
  -- The guest side as one sum over realized instances.
  have hgSum : a.guestAssignments.sendCount m
      = ∑ x : (s : Fin G.length) × Fin (a.guestAssignments s).length,
          (G.get x.1).sendAt ((a.guestAssignments x.1).get x.2) m := by
    rw [Fintype.sum_sigma
      (fun x : (s : Fin G.length) × Fin (a.guestAssignments s).length =>
        (G.get x.1).sendAt ((a.guestAssignments x.1).get x.2) m)]
    exact Finset.sum_congr rfl (fun t _ => list_map_sum_eq_sum_fin _ _)
  have hgS : a.guestAssignments.sendCount m ≤ 1 := by
    rw [hgSum]
    refine sum_le_one_of_unique hgOne (fun x y hx hy => ?_)
    by_contra hne
    obtain ⟨u, hu, hu1, hu2⟩ := hgTime x hx
    obtain ⟨v, hv, hv1, hv2⟩ := hgTime y hy
    have : u = v := tsNat_unique P hu hv
    rcases hgg x y hne with h | h <;> omega
  -- The initial image runs at most once, at timestamp `0`.
  have hinitLe : (a.hostAssignment (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) ≤ 1 :=
    le_trans List.countP_le_length (hsat.satisfiesHost.withinBound (openVmMemInitChip P))
  have hinitTime : (a.hostAssignment (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) ≠ 0 →
      tsNat m 0 := by
    intro hne
    obtain ⟨e, he, hQ⟩ := exists_mem_of_countP_ne_zero hne
    exact openVmHost_initSend_ts (hsat.satisfiesHost.producible (openVmMemInitChip P) e he)
      (by simpa using hQ)
  -- An input-chip instance writes at `base + 1` or `base + 2`, inside its own window.
  have hinTime : ∀ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m ≠ 0 →
      ∃ u : ℕ, tsNat m u ∧ 1 + Ti i ≤ u ∧ u < 1 + Ti i + inputStepWindow := by
    intro i hne
    obtain ⟨e, he, hQ⟩ := exists_mem_of_countP_ne_zero hne
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
    have hbe : e.busId = openVmMemBusId := by rw [← hm, ← hQ.1]
    obtain ⟨o, ho, hts⟩ := openVmHost_inputSend_ts P (hiP i).2 (hiP i).1 he hQ.2 hbe
    exact ⟨1 + Ti i + o, hQ.1 ▸ hts, by omega, by omega⟩
  have hinS : (∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m) ≤ 1 := by
    refine sum_le_one_of_unique (fun i => inputSendCountOf_le_one P (iR i) hm) (fun i j hi hj => ?_)
    by_contra hne
    obtain ⟨u, hu, hu1, hu2⟩ := hinTime i hi
    obtain ⟨v, hv, hv1, hv2⟩ := hinTime j hj
    have : u = v := tsNat_unique P hu hv
    rcases hii i j hne with h | h <;> omega
  -- No two kinds of sender can both fire: their windows are disjoint and none contains `0`.
  have hgi0 : a.guestAssignments.sendCount m ≠ 0 →
      (a.hostAssignment (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) = 0 := by
    intro hg
    by_contra hi
    rw [hgSum] at hg
    obtain ⟨x, hx⟩ := exists_ne_zero_of_sum_ne_zero hg
    obtain ⟨u, hu, hu1, -⟩ := hgTime x hx
    have := tsNat_unique P hu (hinitTime hi)
    omega
  have hgin : a.guestAssignments.sendCount m ≠ 0 →
      (∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m) = 0 := by
    intro hg
    by_contra hi
    rw [hgSum] at hg
    obtain ⟨x, hx⟩ := exists_ne_zero_of_sum_ne_zero hg
    obtain ⟨i, hix⟩ := exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨u, hu, hu1, hu2⟩ := hgTime x hx
    obtain ⟨v, hv, hv1, hv2⟩ := hinTime i hix
    have : u = v := tsNat_unique P hu hv
    rcases hgi x i with h | h <;> omega
  have hiin : (a.hostAssignment (openVmMemInitChip P)).countP (fun e => decide (e m ≠ 0)) ≠ 0 →
      (∑ i, sendCountOf ((iR i).interactions P.ptrReg 0 1) m) = 0 := by
    intro hinit
    by_contra hi
    obtain ⟨i, hix⟩ := exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨v, hv, hv1, -⟩ := hinTime i hix
    have := tsNat_unique P (hinitTime hinit) hv
    omega
  rw [runSendCount]
  omega

/-- **…hence receive-uniqueness: no memory record is read back twice.** Bus balance
    (`runSend_eq_runRecv`) transports `runSendCount_le_one` to the receiving side, which is what
    makes an instance's receives distinguishable records. -/
theorem runRecvCount_le_one [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {L : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
        StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
          ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound}
    {Tg : ((s : Fin G.length) × Fin (a.guestAssignments s).length) → ℕ}
    {Ti : Fin (a.hostAssignment (openVmInputChip P)).length → ℕ}
    (hgP : ∀ x, 1 + Tg x + (L x).tWindow < openVmTimestampBound ∧
        (L x).tStart = ((1 + Tg x : ℕ) : ZMod p))
    (hiP : ∀ i, 1 + Ti i + inputStepWindow < openVmTimestampBound ∧
        (iR i).base = ((1 + Ti i : ℕ) : ZMod p))
    (hgg : ∀ x x', x ≠ x' → Tg x + (L x).tWindow ≤ Tg x' ∨ Tg x' + (L x').tWindow ≤ Tg x)
    (hii : ∀ i i', i ≠ i' → Ti i + inputStepWindow ≤ Ti i' ∨ Ti i' + inputStepWindow ≤ Ti i)
    (hgi : ∀ x i, Tg x + (L x).tWindow ≤ Ti i ∨ Ti i + inputStepWindow ≤ Tg x)
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) :
    runRecvCount P a iR m ≤ 1 := by
  rw [← runSend_eq_runRecv P hGuests hsat iR hiR hm]
  exact runSendCount_le_one P hsat iR hgP hiP hgg hii hgi hm

theorem recvCount_eq_sigma {G : Guest p} (gA : GuestAssignment p G) (m : BusMessage p) :
    gA.recvCount m = ∑ x : (s : Fin G.length) × Fin (gA s).length,
      (G.get x.1).recvAt ((gA x.1).get x.2) m := by
  rw [Fintype.sum_sigma (fun x : (s : Fin G.length) × Fin (gA s).length =>
    (G.get x.1).recvAt ((gA x.1).get x.2) m)]
  exact Finset.sum_congr rfl (fun t _ => list_map_sum_eq_sum_fin _ _)

--------- A run, with its instances placed on the clock ---------

/-- A realized guest instance: which chip type, and which of its instances. -/
abbrev GuestInst (P : OpenVmParams p) {G : Guest p} (a : VmAssignment p ⟨openVmHost P, G⟩) :=
  (s : Fin G.length) × Fin (a.guestAssignments s).length

/-- **Everything the per-address counting argument needs about a satisfying run**, gathered once:
    a layout for every guest instance, an `InputRead` for every input-chip instance, each one's
    position on the bridge, and the disjointness of their windows. `openVmHost_runData` builds it
    from `openVmHost_arcsPlaced`. -/
structure RunData (P : OpenVmParams p) (G : Guest p) (a : VmAssignment p ⟨openVmHost P, G⟩) where
  iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p
  hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
      = busStateOf ((iR i).interactions P.ptrReg 0 1)
  L : ∀ x : GuestInst P a, StepLayout (G.get x.1)
      (openVmGuestRules defaultBusMap openVmMemBusId)
      ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound
  Tg : GuestInst P a → ℕ
  Ti : Fin (a.hostAssignment (openVmInputChip P)).length → ℕ
  gP : ∀ x, 1 + Tg x + (L x).tWindow < openVmTimestampBound ∧
      (L x).tStart = ((1 + Tg x : ℕ) : ZMod p)
  iP : ∀ i, 1 + Ti i + inputStepWindow < openVmTimestampBound ∧
      (iR i).base = ((1 + Ti i : ℕ) : ZMod p)
  gg : ∀ x x', x ≠ x' → Tg x + (L x).tWindow ≤ Tg x' ∨ Tg x' + (L x').tWindow ≤ Tg x
  ii : ∀ i i', i ≠ i' → Ti i + inputStepWindow ≤ Ti i' ∨ Ti i' + inputStepWindow ≤ Ti i
  gi : ∀ x i, Tg x + (L x).tWindow ≤ Ti i ∨ Ti i + inputStepWindow ≤ Tg x

theorem openVmHost_runData [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a) :
    Nonempty (RunData P G a) := by
  obtain ⟨iR, hiR⟩ := openVmHost_inputWitnesses P hsat.satisfiesHost
  obtain ⟨L, Tg, Ti, hgP, hiP, hgg, hii, hgi⟩ := openVmHost_arcsPlaced P hGuests hsat iR hiR
  exact ⟨⟨iR, hiR, L, Tg, Ti, hgP, hiP, hgg, hii, hgi⟩⟩

--------- The run's memory accesses, as one index type ---------

/-- A memory *access* somewhere in a run: for a guest instance, the index of its `getPrevious`
    half (the `setNew` half is `StepLayout.memPartner` of it); for an input-chip instance, which
    of its two accesses — `0` the pointer-register peek, `1` the hinted word. -/
abbrev RunAcc (P : OpenVmParams p) {G : Guest p} (a : VmAssignment p ⟨openVmHost P, G⟩) :=
  ((x : GuestInst P a) × Fin (G.get x.1).busInteractions.length)
  ⊕ (Fin (a.hostAssignment (openVmInputChip P)).length × Fin 2)

theorem int_eq_zero_of_dvd_of_lt {n u : ℤ} (hn : 0 < n) (hd : n ∣ u) (h1 : -n < u) (h2 : u < n) :
    u = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rcases lt_trichotomy k 0 with h | h | h
  · have : n * k ≤ n * (-1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt hn)
    omega
  · simp [h]
  · have : n * 1 ≤ n * k := mul_le_mul_of_nonneg_left (by omega) (le_of_lt hn)
    omega

/-- **Two integers in the lookback window that agree as field elements are equal.** The window
    `[-2^29, 2^29)` has width `openVmRankBound`, which `OpenVmParams.rankWindowOk` puts below `p` —
    the same headroom `AssertLtSubAir` already needs. This is what lets a record's timestamp name
    one instant of the run rather than a residue class. -/
theorem intCast_inj_window [Fact p.Prime] (P : OpenVmParams p) {u v : ℤ}
    (hu1 : -(openVmTimestampBound : ℤ) ≤ u) (hu2 : u < openVmTimestampBound)
    (hv1 : -(openVmTimestampBound : ℤ) ≤ v) (hv2 : v < openVmTimestampBound)
    (h : ((u : ℤ) : ZMod p) = ((v : ℤ) : ZMod p)) : u = v := by
  haveI : NeZero p := ⟨(Nat.Prime.one_lt (Fact.out)).ne_bot⟩
  have hzero : (((u - v : ℤ)) : ZMod p) = 0 := by push_cast; rw [h]; ring
  have hdvd : (p : ℤ) ∣ (u - v) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hpb : (openVmRankBound : ℤ) < (p : ℤ) := by exact_mod_cast P.rankWindowOk
  have hrb : (openVmRankBound : ℤ) = 2 * (openVmTimestampBound : ℤ) := by
    simp [openVmRankBound, openVmRankShift]
    ring
  have hppos : (0 : ℤ) < (p : ℤ) := by
    have : (0 : ℤ) < (openVmRankBound : ℤ) := by
      rw [hrb]; norm_num [openVmTimestampBound, openVmTimestampBits]
    omega
  have := int_eq_zero_of_dvd_of_lt hppos hdvd (by omega) (by omega)
  omega

namespace RunData

variable {P : OpenVmParams p} {G : Guest p} {a : VmAssignment p ⟨openVmHost P, G⟩}

/-- The record an access reads back. -/
def recvMsg (D : RunData P G a) : RunAcc P a → BusMessage p
  | .inl ⟨x, j⟩ => (G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) j
  | .inr (i, k) =>
      if k = 0 then
        ((1 : Nat), [1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList ++ [(D.iR i).ptrTime])
      else ((1 : Nat), [2, (D.iR i).ptr] ++ (D.iR i).oldWord.toList ++ [(D.iR i).wordTime])

/-- …and the one it writes. -/
def sendMsg (D : RunData P G a) : RunAcc P a → BusMessage p
  | .inl ⟨x, j⟩ => (G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) ((D.L x).memPartner j)
  | .inr (i, k) =>
      if k = 0 then
        ((1 : Nat), [1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList ++ [(D.iR i).base + 1])
      else ((1 : Nat), [2, (D.iR i).ptr, (D.iR i).byte, 0, 0, 0, (D.iR i).base + 2])

/-- When the record it reads back was written, on the run's clock. An integer, not a natural: a
    `getPrevious` may reach back before its own instance's window. -/
def recvT (D : RunData P G a) : RunAcc P a → ℤ
  | .inl ⟨x, j⟩ => ((1 + D.Tg x : ℕ) : ℤ) + (D.L x).tOffset j
  | .inr (i, k) =>
      ((1 + D.Ti i : ℕ) : ℤ) + (if k = 0 then (D.iR i).ptrOffset else (D.iR i).wordOffset)

/-- …and when it commits its own. -/
def sendT (D : RunData P G a) : RunAcc P a → ℤ
  | .inl ⟨x, j⟩ => ((1 + D.Tg x : ℕ) : ℤ) + (D.L x).tOffset ((D.L x).memPartner j)
  | .inr (i, k) => ((1 + D.Ti i : ℕ) : ℤ) + (if k = 0 then 1 else 2)

/-- The access is a real one at address `addr`: for a guest, an active memory `getPrevious` whose
    record sits there; for an input-chip instance, one of its two accesses landing there. -/
def IsAcc (D : RunData P G a) (addr : List (Option (ZMod p))) : RunAcc P a → Prop
  | .inl ⟨x, j⟩ =>
      (G.get x.1).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) j
      ∧ ((G.get x.1).busInteractions.get j).busId = openVmMemBusId
      ∧ (G.get x.1).multAt ((a.guestAssignments x.1).get x.2) j = -1
      ∧ openVmMemAddress ((G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) j) = addr
  | .inr (i, k) => openVmMemAddress (D.recvMsg (.inr (i, k))) = addr

noncomputable instance (D : RunData P G a) (addr : List (Option (ZMod p))) (c : RunAcc P a) :
    Decidable (D.IsAcc addr c) := Classical.dec _

/-- **§4.6.1's `t_prev < t`, for every access in the run.** Guests have it from
    `StepLayout.memPartner_time`, input-chip instances from `InputRead.ptrOffsetOk` and
    `wordOffsetOk`. This is the hypothesis the whole counting argument turns on. -/
theorem recvT_lt_sendT (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a}
    (hc : D.IsAcc addr c) : D.recvT c < D.sendT c := by
  match c with
  | .inl ⟨x, j⟩ =>
    obtain ⟨-, hbus, hmult, -⟩ := hc
    have := (D.L x).memPartner_time j hbus hmult
    simp only [recvT, sendT]
    omega
  | .inr (i, k) =>
    simp only [recvT, sendT]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]
      have := (D.iR i).ptrOffsetOk.2
      omega
    · rw [if_neg hk, if_neg hk]
      have := (D.iR i).wordOffsetOk.2
      omega

/-- The `setNew` half of a guest access is a memory send. -/
theorem partner_memSend (D : RunData P G a) {x : GuestInst P a}
    {j : Fin (G.get x.1).busInteractions.length}
    (hbus : ((G.get x.1).busInteractions.get j).busId = openVmMemBusId)
    (hmult : (G.get x.1).multAt ((a.guestAssignments x.1).get x.2) j = -1) :
    (G.get x.1).memSend (openVmGuestRules defaultBusMap openVmMemBusId)
      ((a.guestAssignments x.1).get x.2) ((D.L x).memPartner j) := by
  obtain ⟨-, -, hbus'⟩ := (D.L x).memPartner_invol j hbus
  obtain ⟨hm, -⟩ := (D.L x).memPartner_mult j hbus
  have hone : (G.get x.1).multAt ((a.guestAssignments x.1).get x.2) ((D.L x).memPartner j) = 1 := by
    rw [hm, hmult]; ring
  have hst : (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).isStateful
      ((G.get x.1).busInteractions.get ((D.L x).memPartner j)).busId = true := by
    rw [hbus']; rfl
  exact ⟨⟨hst, hone⟩, hbus'⟩

theorem sendT_range (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a}
    (hc : D.IsAcc addr c) : 0 ≤ D.sendT c ∧ D.sendT c < openVmTimestampBound := by
  match c with
  | .inl ⟨x, j⟩ =>
    obtain ⟨-, hbus, hmult, -⟩ := hc
    obtain ⟨h0, h1⟩ := (D.L x).sendInWindow _ (D.partner_memSend hbus hmult)
    have := (D.gP x).1
    simp only [sendT]
    omega
  | .inr (i, k) =>
    have := (D.iP i).1
    have hstep : inputStepWindow = 3 := rfl
    simp only [sendT]
    by_cases hk : k = 0
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega

theorem recvT_range (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a}
    (hc : D.IsAcc addr c) :
    -(openVmTimestampBound : ℤ) ≤ D.recvT c ∧ D.recvT c < openVmTimestampBound := by
  match c with
  | .inl ⟨x, j⟩ =>
    obtain ⟨hact, -, -, -⟩ := hc
    obtain ⟨h0, h1, -⟩ := (D.L x).tOffsetMatch j hact
    have := (D.gP x).1
    simp only [recvT]
    omega
  | .inr (i, k) =>
    have := (D.iP i).1
    have hstep : inputStepWindow = 3 := rfl
    have hp := (D.iR i).ptrOffsetOk
    have hw := (D.iR i).wordOffsetOk
    simp only [recvT]
    by_cases hk : k = 0
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega

theorem recvMsg_ts (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a}
    (hc : D.IsAcc addr c) :
    openVmTimestamp openVmMemBusId (D.recvMsg c) = ((D.recvT c : ℤ) : ZMod p) := by
  match c with
  | .inl ⟨x, j⟩ =>
    obtain ⟨hact, -, -, -⟩ := hc
    obtain ⟨-, -, hts⟩ := (D.L x).tOffsetMatch j hact
    show (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).getTimestamp
      ((G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) j) = _
    rw [hts, (D.gP x).2]
    simp only [recvT]
    push_cast
    ring
  | .inr (i, k) =>
    have hlenP : (D.iR i).ptrLimbs.toList.length = 4 := by simp
    have hlenW : (D.iR i).oldWord.toList.length = 4 := by simp
    simp only [recvMsg, recvT]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList
        ++ [(D.iR i).ptrTime])[6]?.getD 0 = _
      rw [show ([1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList
        ++ [(D.iR i).ptrTime])[6]? = some (D.iR i).ptrTime from by simp [hlenP],
        Option.getD_some, (D.iR i).ptrTimeMatch, (D.iP i).2]
      push_cast
      ring
    · rw [if_neg hk, if_neg hk]
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([2, (D.iR i).ptr] ++ (D.iR i).oldWord.toList
        ++ [(D.iR i).wordTime])[6]?.getD 0 = _
      rw [show ([2, (D.iR i).ptr] ++ (D.iR i).oldWord.toList
        ++ [(D.iR i).wordTime])[6]? = some (D.iR i).wordTime from by simp [hlenW],
        Option.getD_some, (D.iR i).wordTimeMatch, (D.iP i).2]
      push_cast
      ring

theorem sendMsg_ts [Fact p.Prime] (D : RunData P G a) {addr : List (Option (ZMod p))}
    {c : RunAcc P a}
    (hc : D.IsAcc addr c) :
    openVmTimestamp openVmMemBusId (D.sendMsg c) = ((D.sendT c : ℤ) : ZMod p) := by
  match c with
  | .inl ⟨x, j⟩ =>
    obtain ⟨-, hbus, hmult, -⟩ := hc
    have hsend := D.partner_memSend hbus hmult
    have hact : (G.get x.1).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) ((D.L x).memPartner j) :=
      ⟨hsend.1.1, by rw [hsend.1.2]; exact one_ne_zero⟩
    obtain ⟨-, -, hts⟩ := (D.L x).tOffsetMatch ((D.L x).memPartner j) hact
    show (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).getTimestamp
      ((G.get x.1).msgAt ((a.guestAssignments x.1).get x.2) ((D.L x).memPartner j)) = _
    rw [hts, (D.gP x).2]
    simp only [sendT]
    push_cast
    ring
  | .inr (i, k) =>
    have hlenP : (D.iR i).ptrLimbs.toList.length = 4 := by simp
    simp only [sendMsg, sendT]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList
        ++ [(D.iR i).base + 1])[6]?.getD 0 = _
      rw [show ([1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList
        ++ [(D.iR i).base + 1])[6]? = some ((D.iR i).base + 1) from by simp [hlenP],
        Option.getD_some, (D.iP i).2]
      push_cast
      ring
    · rw [if_neg hk, if_neg hk]
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([(2 : ZMod p), (D.iR i).ptr, (D.iR i).byte, 0, 0, 0,
        (D.iR i).base + 2])[6]?.getD 0 = _
      rw [show ([(2 : ZMod p), (D.iR i).ptr, (D.iR i).byte, 0, 0, 0,
        (D.iR i).base + 2])[6]? = some ((D.iR i).base + 2) from rfl,
        Option.getD_some, (D.iP i).2]
      push_cast
      ring

theorem recvMsg_busId (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a}
    (hc : D.IsAcc addr c) : (D.recvMsg c).1 = openVmMemBusId := by
  match c with
  | .inl ⟨x, j⟩ => exact hc.2.1
  | .inr (i, k) =>
    simp only [recvMsg]
    by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]

theorem recvMsg_addr (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a}
    (hc : D.IsAcc addr c) : openVmMemAddress (D.recvMsg c) = addr := by
  match c with
  | .inl ⟨x, j⟩ => exact hc.2.2.2
  | .inr (i, k) => exact hc

/-- An input-chip access reads and writes the same cell. -/
theorem input_addr_eq (D : RunData P G a)
    (i : Fin (a.hostAssignment (openVmInputChip P)).length) (k : Fin 2) :
    openVmMemAddress (D.recvMsg (.inr (i, k))) = openVmMemAddress (D.sendMsg (.inr (i, k))) := by
  have hlenP : (D.iR i).ptrLimbs.toList.length = 4 := by simp
  have hlenW : (D.iR i).oldWord.toList.length = 4 := by simp
  simp only [recvMsg, sendMsg]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk]
    simp [openVmMemAddress, hlenP]
  · rw [if_neg hk, if_neg hk]
    simp [openVmMemAddress, hlenW]

/-- An input-chip instance's memory sends are exactly the two `sendMsg` slots. -/
theorem input_send_slot [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    {a : VmAssignment p ⟨openVmHost P, G⟩} (D : RunData P G a)
    (i : Fin (a.hostAssignment (openVmInputChip P)).length)
    {m : BusMessage p} (hm : m.1 = openVmMemBusId)
    {e : BusInteraction (ZMod p)} (he : e ∈ (D.iR i).interactions P.ptrReg 0 1)
    (hmsg : (e.busId, e.payload) = m) (hmult : e.multiplicity = 1) :
    ∃ k : Fin 2, D.sendMsg (.inr (i, k)) = m := by
  have h1 : (-1 : ZMod p) ≠ 1 := openVm_negOne_ne_one P
  rw [InputRead.interactions] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hmult h1
  · have h0 : (0 : Nat) = openVmMemBusId := (congrArg Prod.fst hmsg).trans hm
    exact absurd h0 (by decide)
  · exact absurd hmult h1
  · refine ⟨0, ?_⟩
    rw [← hmsg]
    simp [sendMsg]
  · exact absurd hmult h1
  · refine ⟨1, ?_⟩
    rw [← hmsg]
    simp [sendMsg]

/-- **Every record an access reads back was written by something in the run**: the initial memory
    image, or the `setNew` half of another access at the same address. This is `openVmSends`
    (record matching) rephrased in the access index — the map the counting argument injects
    along. -/
theorem exists_producer [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (D : RunData P G a) {addr : List (Option (ZMod p))} {c : RunAcc P a} (hc : D.IsAcc addr c) :
    (∃ e ∈ a.hostAssignment (openVmMemInitChip P), e (D.recvMsg c) ≠ 0)
    ∨ ∃ c' : RunAcc P a, D.IsAcc addr c' ∧ D.sendMsg c' = D.recvMsg c := by
  classical
  have hm := D.recvMsg_busId hc
  have haddr := D.recvMsg_addr hc
  -- the record really is received somewhere in the run
  have hsends : OpenVmSends P a D.iR (D.recvMsg c) := by
    match c, hc with
    | .inl ⟨x, j⟩, hc =>
      exact openVmHost_recv_has_sender P hGuests hsat D.iR D.hiR hm
        (recvCount_ne_zero_of_index (gA := a.guestAssignments) x.1
          (asg := (a.guestAssignments x.1).get x.2) (List.get_mem _ _) (i := j) rfl hc.2.2.1)
    | .inr (i, k), hc =>
      by_cases hk : k = 0
      · refine openVmHost_inputTouch_has_sender P hGuests hsat D.iR D.hiR hm
          (i := i) (e := ⟨1, -1, [1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList
            ++ [(D.iR i).ptrTime]⟩) (by simp [InputRead.interactions]) ?_
        simp only [recvMsg, if_pos hk]
      · refine openVmHost_inputTouch_has_sender P hGuests hsat D.iR D.hiR hm
          (i := i) (e := ⟨1, -1, [2, (D.iR i).ptr] ++ (D.iR i).oldWord.toList
            ++ [(D.iR i).wordTime]⟩) (by simp [InputRead.interactions]) ?_
        simp only [recvMsg, if_neg hk]
  rcases hsends with hg | hi | hin
  · -- a guest instance wrote it
    right
    obtain ⟨t', asg', hasg', hsend⟩ := hg
    obtain ⟨jx', hjx'⟩ := List.get_of_mem hasg'
    subst hjx'
    obtain ⟨j', hmsg', hmult'⟩ := exists_send_index hsend
    set x' : GuestInst P a := ⟨t', jx'⟩ with hx'
    have hbus' : ((G.get x'.1).busInteractions.get j').busId = openVmMemBusId := by
      have h := congrArg Prod.fst hmsg'
      rw [hm] at h
      exact h
    obtain ⟨hinv, -, hbusp⟩ := (D.L x').memPartner_invol j' hbus'
    obtain ⟨hmp, hap⟩ := (D.L x').memPartner_mult j' hbus'
    have hmultp : (G.get x'.1).multAt ((a.guestAssignments x'.1).get x'.2)
        ((D.L x').memPartner j') = -1 := by rw [hmp, hmult']
    have hstp : (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).isStateful
        ((G.get x'.1).busInteractions.get ((D.L x').memPartner j')).busId = true := by
      rw [hbusp]; rfl
    have hne0 : (G.get x'.1).multAt ((a.guestAssignments x'.1).get x'.2)
        ((D.L x').memPartner j') ≠ 0 := by
      rw [hmultp]
      exact neg_ne_zero.mpr one_ne_zero
    refine ⟨.inl ⟨x', (D.L x').memPartner j'⟩, ⟨⟨hstp, hne0⟩, hbusp, hmultp, ?_⟩, ?_⟩
    · rw [← hap, hmsg', haddr]
    · show (G.get x'.1).msgAt ((a.guestAssignments x'.1).get x'.2)
        ((D.L x').memPartner ((D.L x').memPartner j')) = _
      rw [hinv, hmsg']
  · exact Or.inl hi
  · -- an input-chip instance wrote it
    right
    obtain ⟨i', e, he, hmsg', hmult'⟩ := hin
    obtain ⟨k', hk'⟩ := input_send_slot P D i' hm he hmsg' hmult'
    refine ⟨.inr (i', k'), ?_, hk'⟩
    show openVmMemAddress (D.recvMsg (.inr (i', k'))) = addr
    rw [D.input_addr_eq i' k', hk', haddr]

/-- An input-chip access really does receive the record it names. -/
theorem input_recvCountOf_ne_zero (D : RunData P G a)
    (i : Fin (a.hostAssignment (openVmInputChip P)).length) (k : Fin 2) :
    recvCountOf ((D.iR i).interactions P.ptrReg 0 1) (D.recvMsg (.inr (i, k))) ≠ 0 := by
  intro hz
  by_cases hk : k = 0
  · have hmem : (⟨1, -1, [1, (P.ptrReg : ZMod p)] ++ (D.iR i).ptrLimbs.toList
        ++ [(D.iR i).ptrTime]⟩ : BusInteraction (ZMod p))
        ∈ (D.iR i).interactions P.ptrReg 0 1 := by simp [InputRead.interactions]
    refine absurd ?_ (List.countP_eq_zero.mp hz _ hmem)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by simp only [recvMsg, if_pos hk], trivial⟩
  · have hmem : (⟨1, -1, [2, (D.iR i).ptr] ++ (D.iR i).oldWord.toList
        ++ [(D.iR i).wordTime]⟩ : BusInteraction (ZMod p))
        ∈ (D.iR i).interactions P.ptrReg 0 1 := by simp [InputRead.interactions]
    refine absurd ?_ (List.countP_eq_zero.mp hz _ hmem)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by simp only [recvMsg, if_neg hk], trivial⟩

/-- The slot-`0` address space each input access names: `1` for the register peek, `2` for the
    hinted word. -/
theorem input_recvMsg_slot0 (D : RunData P G a)
    (i : Fin (a.hostAssignment (openVmInputChip P)).length) (k : Fin 2) :
    (D.recvMsg (.inr (i, k))).2[0]? = some (if k = 0 then (1 : ZMod p) else 2) := by
  have hlenP : (D.iR i).ptrLimbs.toList.length = 4 := by simp
  have hlenW : (D.iR i).oldWord.toList.length = 4 := by simp
  by_cases hk : k = 0
  · rw [if_pos hk]
    simp only [recvMsg, if_pos hk]
    rfl
  · rw [if_neg hk]
    simp only [recvMsg, if_neg hk]
    rfl

/-- **Distinct accesses read back distinct records.** Receive-uniqueness
    (`runRecvCount_le_one`) says a record is read at most once in the whole run, so the access is
    determined by what it reads — which is what makes the producer map injective. -/
theorem acc_inj [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (D : RunData P G a) {addr : List (Option (ZMod p))} {c c' : RunAcc P a}
    (hc : D.IsAcc addr c) (hc' : D.IsAcc addr c') (heq : D.recvMsg c = D.recvMsg c') : c = c' := by
  classical
  have hm := D.recvMsg_busId hc
  have hle : runRecvCount P a D.iR (D.recvMsg c) ≤ 1 :=
    runRecvCount_le_one P hGuests hsat D.iR D.hiR D.gP D.iP D.gg D.ii D.gi hm
  rw [runRecvCount] at hle
  match c, hc, c', hc', heq with
  | .inl ⟨x, j⟩, hc, .inl ⟨x', j'⟩, hc', heq =>
    have hgle : (∑ y : GuestInst P a, (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2)
        (D.recvMsg (.inl ⟨x, j⟩))) ≤ 1 := by rw [← recvCount_eq_sigma]; omega
    have hg1 : (G.get x.1).recvAt ((a.guestAssignments x.1).get x.2)
        (D.recvMsg (.inl ⟨x, j⟩)) ≠ 0 := countP_ne_zero_of_index rfl hc.2.2.1
    have hg2 : (G.get x'.1).recvAt ((a.guestAssignments x'.1).get x'.2)
        (D.recvMsg (.inl ⟨x, j⟩)) ≠ 0 := by
      rw [heq]; exact countP_ne_zero_of_index rfl hc'.2.2.1
    have hxx : x = x' := eq_of_sum_le_one hgle hg1 hg2
    subst hxx
    have hone : (G.get x.1).recvAt ((a.guestAssignments x.1).get x.2)
        (D.recvMsg (.inl ⟨x, j⟩)) ≤ 1 :=
      le_trans (Finset.single_le_sum (f := fun y : GuestInst P a =>
        (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2) (D.recvMsg (.inl ⟨x, j⟩)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)) hgle
    rw [recvIdx_unique hone rfl hc.2.2.1 heq.symm hc'.2.2.1]
  | .inl ⟨x, j⟩, hc, .inr (i', k'), hc', heq =>
    exfalso
    have hg1 : (G.get x.1).recvAt ((a.guestAssignments x.1).get x.2)
        (D.recvMsg (.inl ⟨x, j⟩)) ≠ 0 := countP_ne_zero_of_index rfl hc.2.2.1
    have hg1' : a.guestAssignments.recvCount (D.recvMsg (.inl ⟨x, j⟩)) ≠ 0 := by
      rw [recvCount_eq_sigma]
      refine fun hz => hg1 (Nat.eq_zero_of_le_zero ?_)
      calc (G.get x.1).recvAt ((a.guestAssignments x.1).get x.2) (D.recvMsg (.inl ⟨x, j⟩))
          ≤ ∑ y : GuestInst P a, (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2)
            (D.recvMsg (.inl ⟨x, j⟩)) :=
            Finset.single_le_sum (f := fun y : GuestInst P a =>
              (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2) (D.recvMsg (.inl ⟨x, j⟩)))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
        _ = 0 := hz
    have hi1 : recvCountOf ((D.iR i').interactions P.ptrReg 0 1)
        (D.recvMsg (.inl ⟨x, j⟩)) ≠ 0 := by
      rw [heq]; exact D.input_recvCountOf_ne_zero i' k'
    have hi1' : (∑ i, recvCountOf ((D.iR i).interactions P.ptrReg 0 1)
        (D.recvMsg (.inl ⟨x, j⟩))) ≠ 0 := by
      refine fun hz => hi1 (Nat.eq_zero_of_le_zero ?_)
      calc recvCountOf ((D.iR i').interactions P.ptrReg 0 1) (D.recvMsg (.inl ⟨x, j⟩))
          ≤ ∑ i, recvCountOf ((D.iR i).interactions P.ptrReg 0 1) (D.recvMsg (.inl ⟨x, j⟩)) :=
            Finset.single_le_sum (f := fun i0 =>
              recvCountOf ((D.iR i0).interactions P.ptrReg 0 1) (D.recvMsg (.inl ⟨x, j⟩)))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i')
        _ = 0 := hz
    omega
  | .inr (i, k), hc, .inl ⟨x', j'⟩, hc', heq =>
    exfalso
    have hg1 : (G.get x'.1).recvAt ((a.guestAssignments x'.1).get x'.2)
        (D.recvMsg (.inr (i, k))) ≠ 0 := by
      rw [heq]; exact countP_ne_zero_of_index rfl hc'.2.2.1
    have hg1' : a.guestAssignments.recvCount (D.recvMsg (.inr (i, k))) ≠ 0 := by
      rw [recvCount_eq_sigma]
      refine fun hz => hg1 (Nat.eq_zero_of_le_zero ?_)
      calc (G.get x'.1).recvAt ((a.guestAssignments x'.1).get x'.2) (D.recvMsg (.inr (i, k)))
          ≤ ∑ y : GuestInst P a, (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2)
            (D.recvMsg (.inr (i, k))) :=
            Finset.single_le_sum (f := fun y : GuestInst P a =>
              (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2) (D.recvMsg (.inr (i, k))))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ x')
        _ = 0 := hz
    have hi1 : recvCountOf ((D.iR i).interactions P.ptrReg 0 1)
        (D.recvMsg (.inr (i, k))) ≠ 0 := D.input_recvCountOf_ne_zero i k
    have hi1' : (∑ i0, recvCountOf ((D.iR i0).interactions P.ptrReg 0 1)
        (D.recvMsg (.inr (i, k)))) ≠ 0 := by
      refine fun hz => hi1 (Nat.eq_zero_of_le_zero ?_)
      calc recvCountOf ((D.iR i).interactions P.ptrReg 0 1) (D.recvMsg (.inr (i, k)))
          ≤ ∑ i0, recvCountOf ((D.iR i0).interactions P.ptrReg 0 1)
            (D.recvMsg (.inr (i, k))) :=
            Finset.single_le_sum (f := fun i0 =>
              recvCountOf ((D.iR i0).interactions P.ptrReg 0 1) (D.recvMsg (.inr (i, k))))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = 0 := hz
    omega
  | .inr (i, k), hc, .inr (i', k'), hc', heq =>
    have hile : (∑ i0, recvCountOf ((D.iR i0).interactions P.ptrReg 0 1)
        (D.recvMsg (.inr (i, k)))) ≤ 1 := by omega
    have hii : i = i' := by
      refine eq_of_sum_le_one hile (D.input_recvCountOf_ne_zero i k) ?_
      rw [heq]; exact D.input_recvCountOf_ne_zero i' k'
    subst hii
    have hval : (if k = 0 then (1 : ZMod p) else 2) = (if k' = 0 then (1 : ZMod p) else 2) := by
      have h : (D.recvMsg (Sum.inr (i, k))).2[0]? = (D.recvMsg (Sum.inr (i, k'))).2[0]? :=
        congrArg (fun q : BusMessage p => q.2[0]?) heq
      rw [D.input_recvMsg_slot0 i k, D.input_recvMsg_slot0 i k'] at h
      exact Option.some_inj.mp h
    have hiff : (k = 0) ↔ (k' = 0) := by
      constructor
      · intro h0
        by_contra h0'
        rw [if_pos h0, if_neg h0'] at hval
        exact absurd (by linear_combination -hval : (1 : ZMod p) = 0) one_ne_zero
      · intro h0
        by_contra h0'
        rw [if_neg h0', if_pos h0] at hval
        exact absurd (by linear_combination hval : (1 : ZMod p) = 0) one_ne_zero
    have hkk : k = k' := by
      by_cases h0 : k = 0
      · exact h0.trans (hiff.mp h0).symm
      · have h0' : ¬ k' = 0 := fun hcc => h0 (hiff.mpr hcc)
        have hkv : k.val ≠ 0 := fun hcc => h0 (Fin.ext (by simpa using hcc))
        have hkv' : k'.val ≠ 0 := fun hcc => h0' (Fin.ext (by simpa using hcc))
        exact Fin.ext (by have := k.isLt; have := k'.isLt; omega)
    rw [hkk]

/-- **At most one access at an address reaches back across any given instant.**

    This is the counting identity `X(τ) + fin(τ) = init(τ) ≤ 1`, run as an injection. Write `A` for
    the accesses at `addr` whose *receive* precedes `τ` and `B` for those whose *send* does; since
    every access has `t_prev < t` (`recvT_lt_sendT`), `B ⊆ A`. Sending each `c ∈ A` to the producer
    of the record it reads (`exists_producer`) lands in `B ⊎ {the initial image}` — the producer's
    send happens exactly when `c`'s receive does — and is injective, because a record is read back
    at most once in a run (`acc_inj`) and the initial image holds one record per address. So
    `A.card ≤ B.card + 1`, and `A \ B` — the accesses crossing `τ` — has at most one element. -/
theorem crossing_le_one [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (D : RunData P G a) (addr : List (Option (ZMod p))) (τ : ℤ) :
    (Finset.univ.filter
      (fun c : RunAcc P a => D.IsAcc addr c ∧ D.recvT c < τ ∧ τ ≤ D.sendT c)).card ≤ 1 := by
  classical
  set A : Finset (RunAcc P a) :=
    Finset.univ.filter (fun c => D.IsAcc addr c ∧ D.recvT c < τ) with hA
  set B : Finset (RunAcc P a) :=
    Finset.univ.filter (fun c => D.IsAcc addr c ∧ D.sendT c < τ) with hB
  have hBA : B ⊆ A := by
    intro c hcB
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hcB
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcB.1, lt_trans (D.recvT_lt_sendT hcB.1) hcB.2⟩
  -- the producer of each access's record, as a function
  have hex : ∀ c : RunAcc P a, ∃ y : RunAcc P a ⊕ Unit,
      (D.IsAcc addr c ∧ D.recvT c < τ) →
        ((∀ c', y = .inl c' → c' ∈ B ∧ D.sendMsg c' = D.recvMsg c) ∧
         (y = .inr () → ∃ e ∈ a.hostAssignment (openVmMemInitChip P), e (D.recvMsg c) ≠ 0)) := by
    intro c
    by_cases hcond : D.IsAcc addr c ∧ D.recvT c < τ
    · rcases exists_producer P hGuests hsat D hcond.1 with hinit | ⟨c', hc', hsm⟩
      · exact ⟨.inr (), fun _ => ⟨by rintro c'' ⟨⟩, fun _ => hinit⟩⟩
      · refine ⟨.inl c', fun _ => ⟨?_, by rintro ⟨⟩⟩⟩
        rintro c'' hcc
        have hc'' : c' = c'' := by injection hcc
        subst hc''
        refine ⟨?_, hsm⟩
        simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hc', ?_⟩
        have hsr := D.sendT_range hc'
        have hrr := D.recvT_range hcond.1
        have hbpos : (0 : ℤ) ≤ (openVmTimestampBound : ℤ) := Int.natCast_nonneg _
        have hts : D.sendT c' = D.recvT c := by
          refine intCast_inj_window P (by omega) hsr.2 hrr.1 hrr.2 ?_
          rw [← D.sendMsg_ts hc', ← D.recvMsg_ts hcond.1, hsm]
        rw [hts]
        exact hcond.2
    · exact ⟨.inr (), fun h => absurd h hcond⟩
  choose σ hσ using hex
  have hmaps : ∀ c ∈ A, σ c ∈ (B.image Sum.inl ∪ {Sum.inr ()} :
      Finset (RunAcc P a ⊕ Unit)) := by
    intro c hcA
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hcA
    match hy : σ c with
    | .inl c' =>
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c', ?_, rfl⟩)
      exact ((hσ c hcA).1 c' hy).1
    | .inr () => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hinj : Set.InjOn σ ↑A := by
    intro c₁ h₁ c₂ h₂ hσeq
    simp only [hA, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at h₁ h₂
    have hmsg : D.recvMsg c₁ = D.recvMsg c₂ := by
      match hy : σ c₁ with
      | .inl c' =>
        have e1 := ((hσ c₁ h₁).1 c' hy).2
        have e2 := ((hσ c₂ h₂).1 c' (hσeq ▸ hy)).2
        rw [← e1, ← e2]
      | .inr () =>
        obtain ⟨e₁, he₁, hne₁⟩ := (hσ c₁ h₁).2 hy
        obtain ⟨e₂, he₂, hne₂⟩ := (hσ c₂ h₂).2 (hσeq ▸ hy)
        have hlen : (a.hostAssignment (openVmMemInitChip P)).length ≤ 1 :=
          hsat.satisfiesHost.withinBound (openVmMemInitChip P)
        have hee : e₁ = e₂ := by
          match hc : a.hostAssignment (openVmMemInitChip P), hlen with
          | [], _ => exact absurd (hc ▸ he₁) (by simp)
          | [e], _ =>
            rw [hc] at he₁ he₂
            rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂]
        subst hee
        obtain ⟨-, hinjInit, -⟩ :=
          hsat.satisfiesHost.producible (openVmMemInitChip P) e₁ he₁
        have hlist := (D.recvMsg_addr h₁.1).trans (D.recvMsg_addr h₂.1).symm
        simp only [openVmMemAddress, List.cons.injEq, and_true] at hlist
        exact hinjInit _ _ hne₁ hne₂ hlist.1 hlist.2
    exact acc_inj P hGuests hsat D h₁.1 h₂.1 hmsg
  have hcard : A.card ≤ B.card + 1 := by
    refine le_trans (Finset.card_le_card_of_injOn σ hmaps hinj) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    simp only [Finset.card_singleton]
    exact Nat.add_le_add_right Finset.card_image_le 1
  have hsdiff : (A \ B).card = A.card - B.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBA]
  have hfilter : Finset.univ.filter
      (fun c : RunAcc P a => D.IsAcc addr c ∧ D.recvT c < τ ∧ τ ≤ D.sendT c) = A \ B := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hA, hB]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun hcc => absurd hcc.2 (by omega)⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra hcc
      exact h3 ⟨h1, by omega⟩
  rw [hfilter, hsdiff]
  omega

/-- **A receive that reaches only inside its own instance's window is matched by that instance's
    own send.** No other producer writes in this window — guest and input instances have disjoint
    windows (`RunData.gg`, `gi`) and the initial image writes at `0` — so record matching hands the
    record straight back. -/
theorem inWindow_sender_is_own [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (D : RunData P G a) {addr : List (Option (ZMod p))} {x₀ : GuestInst P a}
    {j : Fin (G.get x₀.1).busInteractions.length}
    (hj : D.IsAcc addr (.inl ⟨x₀, j⟩)) (hoff : 0 ≤ (D.L x₀).tOffset j) :
    (G.get x₀.1).sendAt ((a.guestAssignments x₀.1).get x₀.2)
      ((G.get x₀.1).msgAt ((a.guestAssignments x₀.1).get x₀.2) j) ≠ 0 := by
  classical
  obtain ⟨hact, hbus, hmult, haddr⟩ := hj
  have hjW : (D.L x₀).tOffset j < ((D.L x₀).tWindow : ℤ) :=
    lt_trans ((D.L x₀).memPartner_time j hbus hmult)
      ((D.L x₀).sendInWindow _ (D.partner_memSend hbus hmult)).2
  have hcAcc : D.IsAcc addr (.inl ⟨x₀, j⟩) := ⟨hact, hbus, hmult, haddr⟩
  have hrr := D.recvT_range hcAcc
  have hbpos : (0 : ℤ) ≤ (openVmTimestampBound : ℤ) := Int.natCast_nonneg _
  have hrT : D.recvT (.inl ⟨x₀, j⟩) = ((1 + D.Tg x₀ : ℕ) : ℤ) + (D.L x₀).tOffset j := rfl
  rcases exists_producer P hGuests hsat D hcAcc with hinit | ⟨c', hc', hsm⟩
  · -- the initial image writes at timestamp `0`, before every window
    exfalso
    obtain ⟨e, he, hne⟩ := hinit
    have h0 := openVmHost_initSend_ts (hsat.satisfiesHost.producible (openVmMemInitChip P) e he) hne
    have heq : ((0 : ℤ) : ZMod p) = ((D.recvT (.inl ⟨x₀, j⟩) : ℤ) : ZMod p) := by
      rw [← D.recvMsg_ts hcAcc]
      simpa using h0.1.symm
    have := intCast_inj_window P (by omega) (by
      norm_num [openVmTimestampBound, openVmTimestampBits]) hrr.1 hrr.2 heq
    omega
  · -- otherwise the producer is an access, and its window must be ours
    have hsr := D.sendT_range hc'
    have hts : D.sendT c' = D.recvT (.inl ⟨x₀, j⟩) := by
      refine intCast_inj_window P (by omega) hsr.2 hrr.1 hrr.2 ?_
      rw [← D.sendMsg_ts hc', ← D.recvMsg_ts hcAcc, hsm]
    match c', hc', hsm, hts with
    | .inl ⟨x', j'⟩, hc', hsm, hts =>
      obtain ⟨hact', hbus', hmult', -⟩ := hc'
      obtain ⟨h0', h1'⟩ := (D.L x').sendInWindow _ (D.partner_memSend hbus' hmult')
      have hsT : D.sendT (.inl ⟨x', j'⟩)
          = ((1 + D.Tg x' : ℕ) : ℤ) + (D.L x').tOffset ((D.L x').memPartner j') := rfl
      have hxx : x' = x₀ := by
        by_contra hne
        rcases D.gg x' x₀ hne with h | h <;> [skip; skip] <;>
          · rw [hsT, hrT] at hts
            push_cast at hts
            omega
      subst hxx
      exact sendAt_ne_zero_of_index (i := (D.L x').memPartner j') hsm
        (D.partner_memSend hbus' hmult').1.2
    | .inr (i, k), hc', hsm, hts =>
      exfalso
      have hsT : D.sendT (.inr (i, k))
          = ((1 + D.Ti i : ℕ) : ℤ) + (if k = 0 then 1 else 2) := rfl
      have hstep : inputStepWindow = 3 := rfl
      have hk : (if k = 0 then (1 : ℤ) else 2) = 1 ∨ (if k = 0 then (1 : ℤ) else 2) = 2 := by
        by_cases hq : k = 0
        · left; rw [if_pos hq]
        · right; rw [if_neg hq]
      rcases D.gi x₀ i with h | h <;>
        · rw [hsT, hrT] at hts
          push_cast at hts
          rcases hk with hk1 | hk1 <;> rw [hk1] at hts <;> omega

/-- **The memory bus's order-free discipline, for one realized guest instance.**

    At each address, the records entering the instance from outside are exactly its memory
    receives whose record predates its own window: everything it reads from inside the window it
    wrote itself (`inWindow_sender_is_own`), and receive-uniqueness makes each record count once.
    `crossing_le_one` bounds the rest by one. -/
theorem openVm_admissibleMem [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a)
    (D : RunData P G a) (x₀ : GuestInst P a) :
    admissibleMemoryBusM ⟨[0, 1], .receiveThenSend⟩
      (↑(admissibleAt (G.get x₀.1) ((a.guestAssignments x₀.1).get x₀.2) openVmMemBusId) :
        Multiset (BusInteraction (ZMod p))) := by
  classical
  intro addr
  have hτ : ∀ j : Fin (G.get x₀.1).busInteractions.length,
      D.recvT (.inl ⟨x₀, j⟩) = ((1 + D.Tg x₀ : ℕ) : ℤ) + (D.L x₀).tOffset j := fun _ => rfl
  have hσ : ∀ j : Fin (G.get x₀.1).busInteractions.length,
      D.sendT (.inl ⟨x₀, j⟩) = ((1 + D.Tg x₀ : ℕ) : ℤ)
        + (D.L x₀).tOffset ((D.L x₀).memPartner j) := fun _ => rfl
  have hmem : ∀ j : Fin (G.get x₀.1).busInteractions.length,
      D.IsAcc addr (.inl ⟨x₀, j⟩) → (D.L x₀).tOffset j < 0 →
      (Sum.inl ⟨x₀, j⟩ : RunAcc P a) ∈ Finset.univ.filter
        (fun c : RunAcc P a => D.IsAcc addr c ∧ D.recvT c < ((1 + D.Tg x₀ : ℕ) : ℤ)
          ∧ ((1 + D.Tg x₀ : ℕ) : ℤ) ≤ D.sendT c) := by
    intro j hj hneg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hj, by rw [hτ]; omega, ?_⟩
    have := ((D.L x₀).sendInWindow _ (D.partner_memSend hj.2.1 hj.2.2.1)).1
    rw [hσ]
    omega
  -- one distinguished payload: the record every crossing receive brings in
  obtain ⟨A, hA⟩ : ∃ A : List (ZMod p), ∀ j : Fin (G.get x₀.1).busInteractions.length,
      D.IsAcc addr (.inl ⟨x₀, j⟩) → (D.L x₀).tOffset j < 0 →
        ((G.get x₀.1).msgAt ((a.guestAssignments x₀.1).get x₀.2) j).2 = A := by
    by_cases hcross : ∃ j : Fin (G.get x₀.1).busInteractions.length,
        D.IsAcc addr (.inl ⟨x₀, j⟩) ∧ (D.L x₀).tOffset j < 0
    · obtain ⟨j₀, h1, h2⟩ := hcross
      refine ⟨((G.get x₀.1).msgAt ((a.guestAssignments x₀.1).get x₀.2) j₀).2,
        fun j hj hneg => ?_⟩
      have heq := Finset.card_le_one.mp
        (crossing_le_one P hGuests hsat D addr ((1 + D.Tg x₀ : ℕ) : ℤ))
        _ (hmem j hj hneg) _ (hmem j₀ h1 h2)
      simp only [Sum.inl.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at heq
      rw [heq]
    · exact ⟨[], fun j hj hneg => absurd ⟨j, hj, hneg⟩ hcross⟩
  refine card_excessAt_le_one_of_counts (A := A) (fun Q => ?_)
  by_cases haddrQ : [Q[0]?, Q[1]?] = addr
  · -- the address condition is implied, so the counts are the instance's own
    have hrw : ∀ v : ZMod p, v ≠ 0 →
        (admissibleAt (G.get x₀.1) ((a.guestAssignments x₀.1).get x₀.2)
          openVmMemBusId).countP (fun e =>
            decide (e.multiplicity = v ∧
              (⟨[0, 1], .receiveThenSend⟩ : MemoryBusShape).address e = addr)
            && decide (Q = e.payload))
          = ((G.get x₀.1).multsAt ((a.guestAssignments x₀.1).get x₀.2)
              ((openVmMemBusId, Q) : BusMessage p)).countP (fun z => decide (z = v)) := by
      intro v hv
      rw [← countP_admissibleAt (c := G.get x₀.1)
        (asg := (a.guestAssignments x₀.1).get x₀.2) (b := openVmMemBusId) (Q := Q) hv rfl]
      refine List.countP_congr (fun e _ => ?_)
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hvv, -⟩, hq⟩
        exact ⟨hvv, hq⟩
      · rintro ⟨hvv, hq⟩
        refine ⟨⟨hvv, ?_⟩, hq⟩
        show [e.payload[0]?, e.payload[1]?] = addr
        rw [← hq]
        exact haddrQ
    rw [show ((⟨[0, 1], .receiveThenSend⟩ : MemoryBusShape).setNewMult : ZMod p) = 1 from rfl,
      hrw 1 one_ne_zero, hrw (-1) (fun h => one_ne_zero (neg_eq_zero.mp h))]
    show (G.get x₀.1).recvAt _ _ ≤ (G.get x₀.1).sendAt _ _ + _
    -- receive-uniqueness bounds the left side by one
    have hm1 : ((openVmMemBusId, Q) : BusMessage p).1 = openVmMemBusId := rfl
    have hrun := runRecvCount_le_one P hGuests hsat D.iR D.hiR D.gP D.iP D.gg D.ii D.gi hm1
    rw [runRecvCount] at hrun
    have hrle : (G.get x₀.1).recvAt ((a.guestAssignments x₀.1).get x₀.2)
        ((openVmMemBusId, Q) : BusMessage p) ≤ 1 := by
      refine le_trans (Finset.single_le_sum (f := fun y : GuestInst P a =>
        (G.get y.1).recvAt ((a.guestAssignments y.1).get y.2) ((openVmMemBusId, Q) : BusMessage p))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ x₀)) ?_
      rw [← recvCount_eq_sigma]
      omega
    by_cases hz : (G.get x₀.1).recvAt ((a.guestAssignments x₀.1).get x₀.2)
        ((openVmMemBusId, Q) : BusMessage p) = 0
    · omega
    obtain ⟨j, hmsg, hmult⟩ := exists_index_of_countP hz
    have hbusj : ((G.get x₀.1).busInteractions.get j).busId = openVmMemBusId :=
      congrArg Prod.fst hmsg
    have hstj : (openVmGuestRules defaultBusMap openVmMemBusId (p := p)).isStateful
        ((G.get x₀.1).busInteractions.get j).busId = true := by rw [hbusj]; rfl
    have hjAcc : D.IsAcc addr (.inl ⟨x₀, j⟩) := by
      refine ⟨⟨hstj, by rw [hmult]; exact neg_ne_zero.mpr one_ne_zero⟩, hbusj, hmult, ?_⟩
      rw [hmsg]
      exact haddrQ
    by_cases hneg : (D.L x₀).tOffset j < 0
    · have hqa := hA j hjAcc hneg
      rw [hmsg] at hqa
      rw [if_pos (hqa : Q = A)]
      omega
    · have hsend := inWindow_sender_is_own P hGuests hsat D hjAcc (by omega)
      rw [hmsg] at hsend
      omega
  · -- no interaction can sit at `addr` with payload `Q`
    have hz : ∀ v : ZMod p, (admissibleAt (G.get x₀.1) ((a.guestAssignments x₀.1).get x₀.2)
        openVmMemBusId).countP (fun e =>
          decide (e.multiplicity = v ∧
            (⟨[0, 1], .receiveThenSend⟩ : MemoryBusShape).address e = addr)
          && decide (Q = e.payload)) = 0 := by
      intro v
      refine List.countP_eq_zero.mpr (fun e _ hc => ?_)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine haddrQ ?_
      rw [hc.2]
      exact hc.1.2
    rw [hz, hz]
    omega

end RunData

open RunData

--------- `Host.forcesAdmissible`, discharged ---------

/-- **`openVmHost` only ever realizes admissible guest assignments** — with no hypotheses left.

    The last undischarged assumption of the VM-level *completeness* theorem, and the counterpart of
    `openVmHost_ordersRanks` on the soundness side. Its four conjuncts:

    * `admissibleMemoryBusM` on the execution bridge — local to the step
      (`openVm_admissibleBridge`);
    * `admissibleMemoryBusM` on the memory bus — the run's per-address access counting
      (`openVm_admissibleMem`), resting on send- and receive-uniqueness and window disjointness;
    * `tsBounded` — `openVmHost_recordGood` and `openVmHost_bridgeGood`;
    * `entryKeyed` — vacuous at `entryPc = none`;
    * `x0ReturnsZero` — `openVmHost_recordGood` again. -/
theorem openVmHost_forcesAdmissible [Fact p.Prime] (P : OpenVmParams p) :
    (openVmHost P).forcesAdmissible (openVmBusSemanticsOF p defaultBusMap none) := by
  intro G hlegal a hsat t asg hasg
  have h0 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h1 : (1 : ZMod p) ≠ -1 := fun h => openVm_negOne_ne_one P h.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  -- The order-free memory discipline, one declared memory-shaped bus at a time.
  · intro busId shape hshape
    rcases memShapeOf_default hshape with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · -- The memory bus: the run's per-address access counting (`openVm_admissibleMem`).
      subst hb
      subst hs
      obtain ⟨jx, hjx⟩ := List.get_of_mem hasg
      subst hjx
      exact (openVmHost_runData P hlegal hsat).elim
        (fun D => openVm_admissibleMem P hlegal hsat D ⟨t, jx⟩)
    · -- The execution bridge: local to the step (`openVm_admissibleBridge`).
      subst hb
      subst hs
      refine ((hlegal (G.get t) (List.get_mem G t)).stepLayout asg
        (hsat.satisfiesGuest t asg hasg)
        (satisfiesStateless_of_sinks (openVmHost_legalGuest_unpack P)
          (openVmHost_sinksAreTables P) hlegal hsat t asg hasg)).elim (fun L => ?_)
      refine openVm_admissibleBridge L h0 h1 ?_
        (fun Q => openVmHost_pmAt P hlegal hsat rfl t asg hasg)
      have := (hlegal (G.get t) (List.get_mem G t)).size
      have := openVmHost_maxInteractions_lt P hsat t hasg
      omega
  -- TS_BOUND: a bridge state by `openVmHost_bridgeGood`, a memory record by
  -- `openVmHost_recordGood`.
  · intro busId tsField htf msg hmsg
    obtain ⟨hmem, hbid⟩ := List.mem_filter.mp hmsg
    obtain ⟨i, hact, hieq⟩ := openVm_mem_admissible_msgs hmem
    have hbus : ((G.get t).busInteractions.get i).busId = busId := by
      rw [show ((G.get t).busInteractions.get i).busId = msg.busId from by rw [← hieq]; rfl]
      exact of_decide_eq_true hbid
    have hmsgAt : (G.get t).msgAt asg i = (msg.busId, msg.payload) := by
      rw [Circuit.msgAt, hieq]
    rcases memTsFieldOf_default htf with ⟨hb, ht⟩ | ⟨hb, ht⟩
    · subst ht
      have hgood := (openVmHost_recordGood P hlegal hsat t hasg i hact (hb ▸ hbus)).1
      rw [hmsgAt] at hgood
      have hts : openVmTimestamp openVmMemBusId ((msg.busId, msg.payload) : BusMessage p)
          = msg.payload[6]?.getD 0 := by
        simp only [openVmTimestamp]
        rw [if_pos (show msg.busId = openVmMemBusId from hb ▸ (of_decide_eq_true hbid))]
      rw [hts] at hgood
      exact hgood
    · subst ht
      have hgood := openVmHost_bridgeGood P hlegal hsat t hasg i hact (hb ▸ hbus)
      rw [hmsgAt] at hgood
      have hb0 : msg.busId = openVmExecBusId := hb ▸ (of_decide_eq_true hbid)
      have hts : openVmTimestamp openVmMemBusId ((msg.busId, msg.payload) : BusMessage p)
          = msg.payload[1]?.getD 0 := by
        simp only [openVmTimestamp]
        rw [if_neg (by rw [hb0]; decide), if_pos hb0]
      rw [hts] at hgood
      exact hgood
  -- ENTRY_KEY: vacuous, since no entry pc is supplied.
  · intro busId slot key shape _ hk
    exact absurd hk (by simp [memEntryKeyOf])
  -- `x0ReturnsZero`, the second half of `openVmHost_recordGood`.
  · intro msg hmsg hmem2
    obtain ⟨i, hact, hieq⟩ := openVm_mem_admissible_msgs hmsg
    have hbus : ((G.get t).busInteractions.get i).busId = openVmMemBusId := by
      rw [show ((G.get t).busInteractions.get i).busId = msg.busId from by rw [← hieq]; rfl]
      exact defaultBusMap_mem_unique _ hmem2
    have hgood := (openVmHost_recordGood P hlegal hsat t hasg i hact hbus).2
    rw [show (G.get t).msgAt asg i = (msg.busId, msg.payload) from by
      rw [Circuit.msgAt, hieq]] at hgood
    exact hgood

end ApcOptimizer.OpenVM
