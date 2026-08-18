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

/-- An `A ++ S :: B ++ R :: C` split reordered so the pair sits on top. -/
theorem perm_split_pair {α : Type*} (A B C : List α) (S R : α) :
    (A ++ S :: B ++ R :: C).Perm (S :: R :: (A ++ B ++ C)) := by
  have h1 : A ++ S :: B ++ R :: C = A ++ S :: (B ++ R :: C) := by
    simp only [List.cons_append, List.append_assoc]
  have h2 : (A ++ (B ++ R :: C)).Perm (R :: (A ++ B ++ C)) := by
    rw [← List.append_assoc]
    exact List.perm_middle
  rw [h1]
  exact List.perm_middle.trans (h2.cons S)

/-- A same-bus, equal-payload `setNew`/`getPrevious` pair is one message key carrying
    `setNewMult + -setNewMult`, so it contributes nothing to any net multiplicity. -/
theorem busState_dropPair (shape : MemoryBusShape)
    {S R : BusInteraction (ZMod p)} {M : List (BusInteraction (ZMod p))}
    (hbus : S.busId = R.busId) (hS : S.multiplicity = shape.setNewMult)
    (hR : R.multiplicity = -shape.setNewMult) (hpay : S.payload = R.payload) :
    busState (S :: R :: M) = busState M := by
  funext key
  unfold busState
  rw [List.filter_cons, List.filter_cons]
  by_cases h : (S.busId, S.payload) = key
  · have h' : (R.busId, R.payload) = key := by rw [← hbus, ← hpay]; exact h
    simp [h, h', hS, hR, ← add_assoc]
  · have h' : ¬((R.busId, R.payload) = key) := by rw [← hbus, ← hpay]; exact h
    simp [h, h']

/-- Dropping a same-bus, equal-payload `setNew`/`getPrevious` pair preserves the discipline: the net
    state is unchanged (`busState_dropPair`) and both side conditions only get easier. -/
theorem admissibleMemoryBusM_dropPair (shape : MemoryBusShape)
    {S R : BusInteraction (ZMod p)} {M : List (BusInteraction (ZMod p))}
    (hbus : S.busId = R.busId) (hS : S.multiplicity = shape.setNewMult)
    (hR : R.multiplicity = -shape.setNewMult) (hpay : S.payload = R.payload)
    (hadm : admissibleMemoryBusM shape (S :: R :: M)) :
    admissibleMemoryBusM shape M := by
  obtain ⟨hmult, hlen, hstate⟩ := hadm
  simp only [List.length_cons] at hlen
  refine ⟨fun m hm => hmult m (by simp [hm]), by omega, fun addr => ?_⟩
  -- The pair shares an address, so the address filter keeps or drops both.
  have hfilter : busState ((S :: R :: M).filter (fun m => shape.address m = addr))
      = busState (M.filter (fun m => shape.address m = addr)) := by
    have haddrSR : shape.address S = shape.address R := shape.address_congr hpay
    by_cases haddr : shape.address S = addr
    · have haddrR : shape.address R = addr := haddrSR.symm.trans haddr
      rw [List.filter_cons_of_pos (by simpa using haddr),
        List.filter_cons_of_pos (by simpa using haddrR)]
      exact busState_dropPair shape hbus hS hR hpay
    · have haddrR : ¬ shape.address R = addr := fun h => haddr (haddrSR.trans h)
      rw [List.filter_cons_of_neg (by simpa using haddr),
        List.filter_cons_of_neg (by simpa using haddrR)]
  rw [← hfilter]
  exact hstate addr

/-- The entry designation survives the same drop: the pair leaves every net multiplicity
    unchanged (`busState_dropPair`), so it leaves the entering records unchanged. -/
theorem entryKeyed_dropPair (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    {S R : BusInteraction (ZMod p)} {M : List (BusInteraction (ZMod p))}
    (hbus : S.busId = R.busId) (hS : S.multiplicity = shape.setNewMult)
    (hR : R.multiplicity = -shape.setNewMult) (hpay : S.payload = R.payload)
    (hkey : entryKeyed shape slot key (S :: R :: M)) :
    entryKeyed shape slot key M := by
  intro busId payload hstate
  exact hkey busId payload (by rw [busState_dropPair shape hbus hS hR hpay]; exact hstate)
