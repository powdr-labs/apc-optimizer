import ApcOptimizer.VmSpec.Implementation.OrderFreeRealizes

set_option autoImplicit false

/-! # Counting the records that enter a block from outside

    `admissibleMemoryBusM` bounds `Multiset.card (excessAt shape addr M)` — the payloads the
    receives at one address hold in excess of the sends there. This file turns that multiset
    statement into a *counting* one on the underlying list (`card_excessAt_le_one_of_counts`), and
    discharges the execution-bridge instance of it.

    The bridge is the easy half and it is entirely local: `StepLayout` already pins a step's whole
    bridge traffic — `-1` at `(pcFrom, tStart)`, `+1` at `(pcTo, tStart + tWindow)`, nothing
    anywhere else — so the one record entering the bridge's single global cell is the one the step
    receives. The memory bus is the half that needs the run. -/

namespace ApcOptimizer.OpenVM

open ApcOptimizer.OpenVM.OrderFree

variable {p : ℕ}

--------- From a multiset excess to a list count ---------

/-- **`excessAt` as a count.** If at every payload the receives at `addr` are outnumbered by the
    sends there, except for a single distinguished payload `A` where they may lead by one, then at
    most one record enters at `addr`. -/
theorem card_excessAt_le_one_of_counts {l : List (BusInteraction (ZMod p))}
    {shape : MemoryBusShape} {addr : List (Option (ZMod p))} {A : List (ZMod p)}
    (h : ∀ Q : List (ZMod p),
      (l.countP (fun m => decide (m.multiplicity = -shape.setNewMult ∧ shape.address m = addr)
        && decide (Q = m.payload)))
      ≤ (l.countP (fun m => decide (m.multiplicity = shape.setNewMult ∧ shape.address m = addr)
        && decide (Q = m.payload))) + (if Q = A then 1 else 0)) :
    Multiset.card (excessAt shape addr (↑l : Multiset (BusInteraction (ZMod p)))) ≤ 1 := by
  classical
  refine le_trans (Multiset.card_le_card ?_) (le_of_eq (Multiset.card_singleton A))
  refine Multiset.le_iff_count.mpr (fun Q => ?_)
  rw [excessAt, Multiset.count_sub, Multiset.count_map, Multiset.count_map,
    recvsAt, sendsAt, Multiset.filter_filter, Multiset.filter_filter]
  have hcount : ∀ (q : BusInteraction (ZMod p) → Prop) [DecidablePred q],
      Multiset.card (Multiset.filter q (↑l : Multiset (BusInteraction (ZMod p))))
        = l.countP (fun m => decide (q m)) := by
    intro q _
    rw [show Multiset.filter q (↑l : Multiset (BusInteraction (ZMod p)))
      = (↑(l.filter (fun m => decide (q m))) : Multiset (BusInteraction (ZMod p))) from rfl,
      Multiset.coe_card, ← List.countP_eq_length_filter]
  rw [hcount, hcount]
  have hA : Multiset.count Q ({A} : Multiset (List (ZMod p))) = if Q = A then 1 else 0 := by
    by_cases hq : Q = A <;> simp [hq]
  rw [hA]
  have e1 : (l.countP fun m => decide (Q = m.payload ∧
        m.multiplicity = -shape.setNewMult ∧ shape.address m = addr))
      = l.countP (fun m => decide (m.multiplicity = -shape.setNewMult ∧ shape.address m = addr)
        && decide (Q = m.payload)) :=
    List.countP_congr (fun m _ => by simp [and_comm])
  have e2 : (l.countP fun m => decide (Q = m.payload ∧
        m.multiplicity = shape.setNewMult ∧ shape.address m = addr))
      = l.countP (fun m => decide (m.multiplicity = shape.setNewMult ∧ shape.address m = addr)
        && decide (Q = m.payload)) :=
    List.countP_congr (fun m _ => by simp [and_comm])
  rw [e1, e2]
  have := h Q
  omega

end ApcOptimizer.OpenVM
