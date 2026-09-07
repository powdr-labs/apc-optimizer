import ApcOptimizer.VmSpec.Audit.AdmissibleGap
set_option autoImplicit false
set_option maxRecDepth 8000
namespace ApcOptimizer.OpenVM.BridgeOffsetGap
open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.AdmissibleGap

/-- A chip with an extra execution-bridge pair at a deeply negative offset. The pair carries the
    *same* message with opposite multiplicities, so its net is zero. -/
def wrapChip : Circuit babyBear where
  algebraicConstraints := []
  busInteractions :=
    [ kc 0 (-1) [0, 1]
    , kc 0 1 [1, 4]
    , kc 0 (-1) [5, 1476395011]
    , kc 0 1 [5, 1476395011] ]

/-- The extra pair's timestamp really is out of range: its `.val` exceeds `2 ^ 29`. -/
theorem wrapChip_ts_big : ¬ ((1476395011 : ZMod babyBear).val < 2 ^ 29) := by decide

/-- And `1476395011 = 1 + (-536870911 : ℤ)`, i.e. offset `-(2^29 - 1)`, inside `tOffsetMatch`. -/
theorem wrapChip_offset :
    (1476395011 : ZMod babyBear) = 1 + (((-536870911 : ℤ)) : ZMod babyBear) := by decide

/-- **The crux: `bridgeNoOther` is satisfied.** -/
theorem wrapChip_bridgeNoOther (asg : ChipAssignment babyBear) :
    ∀ m : BusMessage babyBear, m.1 = rr.execBusId →
      m ≠ (rr.execBusId, [0, 1]) → m ≠ (rr.execBusId, [1, 1 + ((3 : ℕ) : ZMod babyBear)]) →
        wrapChip.allEffects asg m = 0 := by
  rintro ⟨b, pl⟩ hb h1 h2
  simp only at hb
  subst hb
  simp only [Prod.mk.injEq, true_and, ne_eq] at h1 h2
  have h2' : ¬ pl = [(1 : ZMod babyBear), 4] := fun h => h2 (by rw [h]; decide)
  have e1 : ¬ (([0, 1] : List (ZMod babyBear)) = pl) := fun h => h1 h.symm
  have e2 : ¬ (([1, 4] : List (ZMod babyBear)) = pl) := fun h => h2' h.symm
  by_cases e3 : ([(5 : ZMod babyBear), 1476395011] : List (ZMod babyBear)) = pl
  · rw [← e3]
    simp only [Circuit.allEffects, wrapChip, kc, List.map_cons, List.map_nil,
      BusInteraction.eval, Expression.eval, List.filter_cons, List.filter_nil,
      decide_eq_true_eq, Prod.mk.injEq]
    decide
  · simp [Circuit.allEffects, wrapChip, kc, BusInteraction.eval, Expression.eval,
      show rr.execBusId = 0 from rfl, e1, e2, e3]

/-- `wrapChip` has no memory interactions at all, so every memory clause is vacuous. -/
theorem wrapChip_no_mem (_asg : ChipAssignment babyBear)
    (i : Fin wrapChip.busInteractions.length) :
    (wrapChip.busInteractions.get i).busId ≠ rr.memBusId := by
  fin_cases i <;> decide

def wrapOffs : List ℤ := [0, 3, -536870911, -536870911]

/-! **`wrapChip` satisfied every clause of the *original* `StepLayout`.** `wrapChipLayout` and
    `wrapChip_hasStepLayout` stood here, building one at `tStart = 1`, `tWindow = 3` and
    `wrapOffs`: `bridgeRecv`/`bridgeSend` hold by `rfl`, `bridgeNoOther` is
    `wrapChip_bridgeNoOther` — the extra pair nets to zero — every offset is inside
    `tOffsetMatch`'s range, and `wrapChip_no_mem` makes every memory clause vacuous. Nothing in
    that version of `Legal.lean` rejected a chip whose bridge interactions have wrapped
    timestamps.

    They are retracted: `StepLayout` now carries `negOffsetOnlyMemRecv`, and that clause fails at
    exactly the wrapped pair (`wrapChip_fails_negOffset`), so no layout exists any more. -/

/-- **…and `negOffsetOnlyMemRecv` is what rejects it.** Interactions `2` and `3` sit at offset
    `-(2^29 - 1)` while being on the execution bus, so the clause fails at exactly the place the
    wrapped timestamp lives. -/
theorem wrapChip_fails_negOffset (_asg : ChipAssignment babyBear) :
    ¬ ((wrapChip.busInteractions.get ⟨2, by decide⟩).busId = rr.memBusId ∧
        wrapChip.multAt _asg ⟨2, by decide⟩ = -1) := by
  rintro ⟨hb, -⟩
  exact absurd hb (by decide)

end ApcOptimizer.OpenVM.BridgeOffsetGap
