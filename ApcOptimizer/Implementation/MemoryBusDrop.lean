import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # Dropping matched send/receive pairs preserves the memory discipline

The `MemoryBus`-level machinery behind the pair-cancellation pass (`OptimizerPasses/BusPairCancel`):
a matched send/receive pair contributes `0` to every net multiplicity, so both can be dropped, and
`admissibleMemoryBusM_dropPair` shows the order-free discipline survives that drop. It is what the
`admissible_dropPair` field of `BusFacts` rests on. -/

variable {p : ℕ}

/-- The `setNew` multiplicity is nonzero whenever `1 ≠ 0` (it is `±1`). -/
theorem MemoryBusShape.setNewMult_ne_zero (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0) :
    (shape.setNewMult : ZMod p) ≠ 0 := by
  unfold MemoryBusShape.setNewMult
  split
  · exact hp1
  · exact neg_ne_zero.mpr hp1

/-- Equal payloads project to equal addresses. -/
theorem MemoryBusShape.address_congr (shape : MemoryBusShape)
    {m m' : BusInteraction (ZMod p)} (h : m.payload = m'.payload) :
    shape.address m = shape.address m' := by
  simp only [MemoryBusShape.address, h]

/-- The multiset view of an `A ++ S :: B ++ R :: C` split: the pair sits on top. -/
theorem coe_split_pair {α : Type*} (A B C : List α) (S R : α) :
    (↑(A ++ S :: B ++ R :: C) : Multiset α) = S ::ₘ R ::ₘ ↑(A ++ B ++ C) := by
  have hperm : (A ++ S :: B ++ R :: C).Perm (S :: R :: (A ++ B ++ C)) := by
    have h1 : A ++ S :: B ++ R :: C = A ++ S :: (B ++ R :: C) := by
      simp only [List.cons_append, List.append_assoc]
    have h2 : (A ++ (B ++ R :: C)).Perm (R :: (A ++ B ++ C)) := by
      rw [← List.append_assoc]
      exact List.perm_middle
    rw [h1]
    exact List.perm_middle.trans (h2.cons S)
  rw [Multiset.coe_eq_coe.mpr hperm]
  rfl

/-- Dropping an equal-payload `setNew`/`getPrevious` pair leaves every per-address excess
    unchanged: at the pair's (shared, by payload equality) address, `S` and `R` add the same
    payload count to both fibers — whatever `setNewMult` is, including
    `setNewMult = -setNewMult`. -/
theorem excessAt_dropPair (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    {S R : BusInteraction (ZMod p)} {M : Multiset (BusInteraction (ZMod p))}
    (hS : S.multiplicity = shape.setNewMult) (hR : R.multiplicity = -shape.setNewMult)
    (hpay : S.payload = R.payload) :
    excessAt shape addr M = excessAt shape addr (S ::ₘ R ::ₘ M) := by
  have haddrSR : shape.address S = shape.address R := shape.address_congr hpay
  show (recvsAt shape addr M).map BusInteraction.payload
          - (sendsAt shape addr M).map BusInteraction.payload
        = (recvsAt shape addr (S ::ₘ R ::ₘ M)).map BusInteraction.payload
          - (sendsAt shape addr (S ::ₘ R ::ₘ M)).map BusInteraction.payload
  by_cases haddr : shape.address S = addr
  · have haddrR : shape.address R = addr := haddrSR.symm.trans haddr
    by_cases he : (shape.setNewMult : ZMod p) = -shape.setNewMult
    · -- `p ∣ 2`: each of `S`, `R` lands in *both* fibers; two equal-head cancellations per side.
      have h1 : recvsAt shape addr (S ::ₘ R ::ₘ M) = S ::ₘ R ::ₘ recvsAt shape addr M := by
        unfold recvsAt
        rw [Multiset.filter_cons_of_pos _ ⟨hS.trans he, haddr⟩,
          Multiset.filter_cons_of_pos _ ⟨hR, haddrR⟩]
      have h2 : sendsAt shape addr (S ::ₘ R ::ₘ M) = S ::ₘ R ::ₘ sendsAt shape addr M := by
        unfold sendsAt
        rw [Multiset.filter_cons_of_pos _ ⟨hS, haddr⟩,
          Multiset.filter_cons_of_pos _ ⟨hR.trans he.symm, haddrR⟩]
      rw [h1, h2, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons,
        hpay, Multiset.sub_cons, Multiset.erase_cons_head, Multiset.sub_cons,
        Multiset.erase_cons_head]
    · -- generic field: `R` joins the receive fiber, `S` the send fiber; equal heads cancel.
      have h1 : recvsAt shape addr (S ::ₘ R ::ₘ M) = R ::ₘ recvsAt shape addr M := by
        unfold recvsAt
        rw [Multiset.filter_cons_of_neg _ (fun h => he (hS.symm.trans h.1)),
          Multiset.filter_cons_of_pos _ ⟨hR, haddrR⟩]
      have h2 : sendsAt shape addr (S ::ₘ R ::ₘ M) = S ::ₘ sendsAt shape addr M := by
        unfold sendsAt
        rw [Multiset.filter_cons_of_pos _ ⟨hS, haddr⟩,
          Multiset.filter_cons_of_neg _ (fun h => he (hR.symm.trans h.1).symm)]
      rw [h1, h2, Multiset.map_cons, Multiset.map_cons, hpay, Multiset.sub_cons,
        Multiset.erase_cons_head]
  · -- `S`, `R` sit at another address: both fibers at `addr` are unchanged.
    have haddrR : ¬ shape.address R = addr := fun h => haddr (haddrSR.trans h)
    have h1 : recvsAt shape addr (S ::ₘ R ::ₘ M) = recvsAt shape addr M := by
      unfold recvsAt
      rw [Multiset.filter_cons_of_neg _ (fun h => haddr h.2),
        Multiset.filter_cons_of_neg _ (fun h => haddrR h.2)]
    have h2 : sendsAt shape addr (S ::ₘ R ::ₘ M) = sendsAt shape addr M := by
      unfold sendsAt
      rw [Multiset.filter_cons_of_neg _ (fun h => haddr h.2),
        Multiset.filter_cons_of_neg _ (fun h => haddrR h.2)]
    rw [h1, h2]

/-- Dropping an equal-payload `setNew`/`getPrevious` pair preserves the order-free discipline
    (`excessAt_dropPair`: every per-address excess is unchanged). -/
theorem admissibleMemoryBusM_dropPair (shape : MemoryBusShape)
    {S R : BusInteraction (ZMod p)} {M : Multiset (BusInteraction (ZMod p))}
    (hS : S.multiplicity = shape.setNewMult) (hR : R.multiplicity = -shape.setNewMult)
    (hpay : S.payload = R.payload)
    (hadm : admissibleMemoryBusM shape (S ::ₘ R ::ₘ M)) :
    admissibleMemoryBusM shape M := by
  intro addr
  rw [excessAt_dropPair shape addr hS hR hpay]
  exact hadm addr

/-- The entry designation survives the same drop (`excessAt_dropPair`). -/
theorem entryKeyed_dropPair (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    {S R : BusInteraction (ZMod p)} {M : Multiset (BusInteraction (ZMod p))}
    (hS : S.multiplicity = shape.setNewMult) (hR : R.multiplicity = -shape.setNewMult)
    (hpay : S.payload = R.payload)
    (hkey : entryKeyed shape slot key (S ::ₘ R ::ₘ M)) :
    entryKeyed shape slot key M := by
  intro addr P hP
  rw [excessAt_dropPair shape addr hS hR hpay] at hP
  exact hkey addr P hP
