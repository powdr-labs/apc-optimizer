import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

/-! # The host's signed contribution at a memory message

    `Implementation/Forces.lean`'s record-matching step needs to rule out "nobody sent this record,
    yet the balance still works". The contrapositive of `recvCount_eq_zero_of_no_send` alone is too
    weak: it yields *either* a guest send *or* a nonzero host net, and `memoryFinalizeHostChip` is
    routinely nonzero at a memory message while only ever *receiving*.

    So this file computes the **sign**. `openVmHost_memNet_or_sender` says that at a memory
    message, either the initial image or an input-chip instance actually *sends* it, or the whole
    host's net there is `-(F)` for an honest natural `F` bounded by the configuration. Feeding that
    into bus balance leaves `guestRecv + F ≡ 0` with `guestRecv + F < p`
    (`OpenVmParams.budgetOk`), so the receive count is zero.

    The per-chip facts are one `HostChip.canProduce` each — see `VmSpec/OpenVm.lean`:

    * the four lookup chips pin `message.1` to their own bus id, so they contribute `0` on memory;
    * `memoryInitHostChip` contributes `0` or `1`, so `0` once it is known not to send;
    * `memoryFinalizeHostChip` contributes `0` or `-1`, and runs at most once;
    * `connectorHostChip` is `busStateOf` of two execution-bridge interactions, so `0` on memory;
    * `inputHostChip` is `busStateOf` of six interactions, of which only the two memory sends can
      be positive. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

--------- `busStateOf`, one interaction at a time ---------

theorem busStateOf_nil (m : BusMessage p) : busStateOf ([] : List (BusInteraction (ZMod p))) m = 0 :=
  rfl

theorem busStateOf_cons (a : BusInteraction (ZMod p)) (l : List (BusInteraction (ZMod p)))
    (m : BusMessage p) :
    busStateOf (a :: l) m
      = (if (a.busId, a.payload) = m then a.multiplicity else 0) + busStateOf l m := by
  by_cases h : (a.busId, a.payload) = m <;> simp [busStateOf, h]

/-- How many of a list's interactions carry `m` at all. -/
def touchCount (l : List (BusInteraction (ZMod p))) (m : BusMessage p) : ℕ :=
  l.countP (fun e => decide ((e.busId, e.payload) = m))

theorem touchCount_le (l : List (BusInteraction (ZMod p))) (m : BusMessage p) :
    touchCount l m ≤ l.length :=
  List.countP_le_length

/-- Nothing in the list carries `m` when the count is zero. -/
theorem not_mem_of_touchCount_zero {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : touchCount l m = 0) : ∀ e ∈ l, (e.busId, e.payload) ≠ m := by
  intro e he heq
  exact absurd (decide_eq_true heq) (List.countP_eq_zero.mp h e he)

/-- **A list that never sends `m` contributes exactly minus its touch count there.** The exact
    count, not just a bound: a caller that finds the host's whole net at `m` to be zero needs to
    conclude that no host interaction touched `m` at all, which is what closes record matching for
    the receives the host itself makes. -/
theorem busStateOf_eq_neg_touchCount {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : ∀ e ∈ l, (e.busId, e.payload) = m → e.multiplicity = -1) :
    busStateOf l m = -((touchCount l m : ℕ) : ZMod p) := by
  induction l with
  | nil => simp [busStateOf_nil, touchCount]
  | cons a t ih =>
    have iht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    rw [busStateOf_cons, touchCount, List.countP_cons]
    by_cases ha : (a.busId, a.payload) = m
    · rw [if_pos ha, h a (by simp) ha, iht, if_pos (decide_eq_true ha)]
      show _ = -(((touchCount t m + 1 : ℕ)) : ZMod p)
      push_cast
      ring
    · rw [if_neg ha, iht, if_neg (by simpa using ha), zero_add]
      rfl

/-- A finite sum of non-positive honest counts is minus the sum of the counts. -/
theorem sum_neg_nat {ι : Type} [Fintype ι] {f : ι → ZMod p} {g : ι → ℕ}
    (h : ∀ i, f i = -((g i : ℕ) : ZMod p)) :
    (∑ i, f i) = -(((∑ i, g i : ℕ)) : ZMod p) := by
  rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => h i)

--------- The `InputRead` witness on the memory bus ---------

/-- The two memory *sends* an input-chip instance makes: the pointer-register write-back at
    `base + 1` and the hinted word at `base + 2` (`InputRead.interactions`). Everything else it
    does is a receive or sits on the execution bridge. -/
theorem inputRead_no_send_of {r : InputRead p} {ptrReg : Nat} {m : BusMessage p}
    (h1 : ((1 : Nat), ([1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])) ≠ m)
    (h2 : ((1 : Nat), [2, r.ptr, r.byte, 0, 0, 0, r.base + 2]) ≠ m)
    (h3 : (((0 : Nat)), [r.pcTo, r.base + (inputStepWindow : ZMod p)]) ≠ m) :
    ∀ e ∈ r.interactions ptrReg 0 1, (e.busId, e.payload) = m → e.multiplicity = -1 := by
  intro e he heq
  rw [InputRead.interactions] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd heq h3
  · rfl
  · exact absurd heq h1
  · rfl
  · exact absurd heq h2

--------- The whole host at a memory message ---------

/-- **At a memory message the host either sends it, or is non-positive there and its net names
    exactly the receives it makes.**

    The two possible host senders are named explicitly: `memoryInitHostChip`'s single instance
    (whose whole contribution is `+1` where it is nonzero) and an input-chip instance's own two
    memory sends. Everything else on the host side can only receive, so failing both leaves the
    host's net an honest count with a negative sign — the shape bus balance needs.

    The third disjunct splits that count into memory finalization's and the input chip's, each with
    its own "zero means untouched" clause. A caller that finds the whole balance to vanish then
    learns not just that the guests do not receive `m` but that *nothing* does, which is what
    record matching needs for the host's own receives.

    `iR` is passed in rather than chosen here so the caller can reuse the same witness family it
    got from `openVmHost_bridge_isolated`, and so name an input-chip sender's own bridge arc. -/
theorem openVmHost_memNet_or_sender (P : OpenVmParams p)
    {hA : HostAssignment p (openVmHost P)} (hlegal : hA.satisfies)
    (iR : Fin (hA (openVmInputChip P)).length → InputRead p)
    (hiR : ∀ i, (hA (openVmInputChip P)).get i = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {m : BusMessage p} (hm : m.1 = openVmMemBusId) :
    (∃ e ∈ hA (openVmMemInitChip P), e m ≠ 0)
    ∨ (∃ i : Fin (hA (openVmInputChip P)).length,
        ∃ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) = m ∧ e.multiplicity = 1)
    ∨ (∃ kf ki : ℕ, kf ≤ 1 ∧ ki ≤ 6 * P.maxInputInstances ∧
        hA.busEffect m = -((kf + ki : ℕ) : ZMod p) ∧
        (kf = 0 → ∀ e ∈ hA (openVmMemFinalizeChip P), e m = 0) ∧
        (ki = 0 → ∀ i : Fin (hA (openVmInputChip P)).length,
          ∀ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) ≠ m)) := by
  classical
  by_cases hinit : ∃ e ∈ hA (openVmMemInitChip P), e m ≠ 0
  · exact Or.inl hinit
  refine Or.inr ?_
  by_cases hin : ∃ i : Fin (hA (openVmInputChip P)).length,
      ∃ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) = m ∧ e.multiplicity = 1
  · exact Or.inl hin
  refine Or.inr ?_
  have hinit' : ∀ e ∈ hA (openVmMemInitChip P), e m = 0 := by
    intro e he
    by_contra hc
    exact hinit ⟨e, he, hc⟩
  have hin' : ∀ (i : Fin (hA (openVmInputChip P)).length) (e : BusInteraction (ZMod p)),
      e ∈ (iR i).interactions P.ptrReg 0 1 → (e.busId, e.payload) = m → e.multiplicity ≠ 1 := by
    intro i e he heq hc
    exact hin ⟨i, e, he, heq, hc⟩
  -- Every chip other than memory-finalize and the input chip is silent at `m`.
  have hzero : ∀ t : Fin (openVmHost P).chips.length,
      (t : ℕ) ≠ 5 → (t : ℕ) ≠ 6 → ((hA t).map (fun effect => effect m)).sum = 0 := by
    intro t ht5 ht6
    refine List.sum_eq_zero (fun v hv => ?_)
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    have hleg := hlegal.producible t e he
    by_contra hne
    fin_cases t
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact absurd (hleg m hne).1 (by rw [hm]; decide)
    · exact hne (hinit' e he)
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
  -- Memory finalization runs at most once, and only ever receives.
  obtain ⟨kf, hkfle, hkfeq, hkfzero⟩ : ∃ kf : ℕ, kf ≤ 1 ∧
      ((hA (openVmMemFinalizeChip P)).map (fun effect => effect m)).sum = -(kf : ZMod p) ∧
      (kf = 0 → ∀ e ∈ hA (openVmMemFinalizeChip P), e m = 0) := by
    have hlen : (hA (openVmMemFinalizeChip P)).length ≤ 1 :=
      hlegal.withinBound (openVmMemFinalizeChip P)
    match hc : hA (openVmMemFinalizeChip P), hlen with
    | [], _ => exact ⟨0, by omega, by simp, fun _ e he => by simp at he⟩
    | [e], _ =>
      have hleg := hlegal.producible (openVmMemFinalizeChip P) e
        (by rw [hc]; exact List.mem_singleton_self e)
      by_cases hne : e m = 0
      · refine ⟨0, by omega, by simp [hne], fun _ e' he' => ?_⟩
        rw [List.mem_singleton.mp he']
        exact hne
      · exact ⟨1, le_rfl, by simp [(hleg m hne).2.1], fun h => absurd h (by omega)⟩
  -- Each input-chip instance contributes at most six receives and no send.
  have hgeq : ∀ i : Fin (hA (openVmInputChip P)).length,
      (hA (openVmInputChip P)).get i m
        = -((touchCount ((iR i).interactions P.ptrReg 0 1) m : ℕ) : ZMod p) := by
    intro i
    rw [hiR i]
    refine busStateOf_eq_neg_touchCount (fun e he heq => ?_)
    have hne1 := hin' i e he heq
    have hpol : e.multiplicity = 1 ∨ e.multiplicity = -1 := by
      rw [InputRead.interactions] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rcases hpol with h | h
    · exact absurd h hne1
    · exact h
  have hgle : ∀ i : Fin (hA (openVmInputChip P)).length,
      touchCount ((iR i).interactions P.ptrReg 0 1) m ≤ 6 := fun i => by
    simpa [InputRead.interactions] using touchCount_le ((iR i).interactions P.ptrReg 0 1) m
  have hkieq : ((hA (openVmInputChip P)).map (fun effect => effect m)).sum
      = -(((∑ i, touchCount ((iR i).interactions P.ptrReg 0 1) m : ℕ)) : ZMod p) := by
    rw [list_map_sum_eq_sum_fin]
    exact sum_neg_nat hgeq
  have hkile : (∑ i, touchCount ((iR i).interactions P.ptrReg 0 1) m) ≤ 6 * P.maxInputInstances := by
    have hb : (hA (openVmInputChip P)).length ≤ P.maxInputInstances :=
      hlegal.withinBound (openVmInputChip P)
    calc (∑ i, touchCount ((iR i).interactions P.ptrReg 0 1) m)
        ≤ ∑ _i : Fin (hA (openVmInputChip P)).length, 6 :=
          Finset.sum_le_sum (fun i _ => hgle i)
      _ = (hA (openVmInputChip P)).length * 6 := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      _ ≤ 6 * P.maxInputInstances := by omega
  have hkizero : (∑ i, touchCount ((iR i).interactions P.ptrReg 0 1) m) = 0 →
      ∀ i : Fin (hA (openVmInputChip P)).length,
        ∀ e ∈ (iR i).interactions P.ptrReg 0 1, (e.busId, e.payload) ≠ m := by
    intro hz i
    have hle : touchCount ((iR i).interactions P.ptrReg 0 1) m
        ≤ ∑ j, touchCount ((iR j).interactions P.ptrReg 0 1) m :=
      Finset.single_le_sum (f := fun j => touchCount ((iR j).interactions P.ptrReg 0 1) m)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact not_mem_of_touchCount_zero (by omega)
  have hfj : openVmMemFinalizeChip P ≠ openVmInputChip P := by
    intro h
    have : (5 : ℕ) = 6 := congrArg Fin.val h
    omega
  have hnet : hA.busEffect m
      = ∑ t : Fin (openVmHost P).chips.length, ((hA t).map (fun effect => effect m)).sum := rfl
  have hsum : (∑ t : Fin (openVmHost P).chips.length, ((hA t).map (fun effect => effect m)).sum)
      = ∑ t ∈ ({openVmMemFinalizeChip P, openVmInputChip P} :
          Finset (Fin (openVmHost P).chips.length)),
          ((hA t).map (fun effect => effect m)).sum := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro t _ ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact hzero t (fun h => ht.1 (Fin.ext h)) (fun h => ht.2 (Fin.ext h))
  refine ⟨kf, ∑ i, touchCount ((iR i).interactions P.ptrReg 0 1) m,
    hkfle, hkile, ?_, hkfzero, hkizero⟩
  rw [hnet, hsum, Finset.sum_pair hfj, hkfeq, hkieq]
  push_cast
  ring

end ApcOptimizer.OpenVM
