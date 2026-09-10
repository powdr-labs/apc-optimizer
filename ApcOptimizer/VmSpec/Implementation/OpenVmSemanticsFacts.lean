import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! Facts about `OpenVmSemantics.lean`'s bus map and bus semantics that `VmSpec/OpenVm.lean` needs
    in order to instantiate `GuestBusRules`. Kept out of `OpenVmSemantics.lean` itself so that the
    audited file stays definitions only. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- `1` is `defaultBusMap`'s only memory bus id — what `openVmGuestRules`'s `memPayloadOnly` field
    rests on. -/
theorem defaultBusMap_mem_unique : ∀ b : Nat, defaultBusMap b = some .memory → b = 1 := by
  intro b hb
  match b with
  | 0 => simp [defaultBusMap] at hb
  | 1 => rfl
  | 2 => simp [defaultBusMap] at hb
  | 3 => simp [defaultBusMap] at hb
  | 4 => simp [defaultBusMap] at hb
  | 5 => simp [defaultBusMap] at hb
  | 6 => simp [defaultBusMap] at hb
  | 7 => simp [defaultBusMap] at hb
  | (n + 8) => simp [defaultBusMap] at hb

/-- **Off the memory bus, `openVmBusSemantics` always has *some* multiplicity maintaining the
    invariants** — `1`, on the execution bridge, is enough (`maintainsInvariants`'s stateful arms
    ask nothing else there). What `BusSemantics.toGuestRules`'s `memPayloadOnly` field rests on
    for the OpenVM instantiation, `variable {p}` so it discharges the `autoParam` default at any
    `busMap`/`memBusId` (not just `defaultBusMap`/`openVmMemBusId`). -/
theorem maintainsInvariants_off_mem {busMap : BusMap} {memBusId : Nat}
    (hmem : ∀ b, busMap b = some .memory → b = memBusId) (m : BusMessage p)
    (hst : (openVmBusSemantics p busMap).isStateful m.1 = true) (hne : m.1 ≠ memBusId) :
    ∃ mult : ZMod p, (openVmBusSemantics p busMap).maintainsInvariants ⟨m.1, mult, m.2⟩ := by
  simp only [openVmBusSemantics] at hst ⊢
  cases hbm : busMap m.1 with
  | none => rw [hbm] at hst; exact absurd hst (by decide)
  | some t =>
    cases t with
    | memory => exact absurd (hmem m.1 hbm) hne
    | executionBridge => exact ⟨1, by simp [maintainsInvariants, hbm]⟩
    | pcLookup => rw [hbm] at hst; simp [OpenVmBusType.isStateful] at hst
    | variableRangeChecker => rw [hbm] at hst; simp [OpenVmBusType.isStateful] at hst
    | bitwiseLookup => rw [hbm] at hst; simp [OpenVmBusType.isStateful] at hst
    | tupleRangeChecker _ _ => rw [hbm] at hst; simp [OpenVmBusType.isStateful] at hst

end ApcOptimizer.OpenVM
