import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

/-! # Forced cascade matching for an order-free memory-bus discipline

Core combinatorics for an order-free (multiset-level) alternative to the positional
`admissibleMemoryBus` (`ApcOptimizer/MemoryBus.lean`): one evaluated-address group has `k`
accesses, access `i` receiving a record at `prevTs i` and sending its own at `sendTs i`. Given
strictly increasing send timestamps, the per-access LessThan bound `prevTs i < sendTs i`, and an
injective timestamp-keyed matching with at most one entry receive (the shape multiset bus balance
plus window atomicity provide), the matching is *forced* to be the consecutive cascade — receive
`i` reads send `i - 1` — so every interior receive copies the previous send's payload. Nothing
here depends on the order in which the interactions are listed. -/

/-- A matching on `Fin k` that only ever points strictly below the current index, never repeats a
    target, and has at most one unmatched index is forced to be `i ↦ i - 1` (with `0` the unique
    unmatched index). -/
theorem matching_below_forced {k : ℕ} (μ : Fin k → Option (Fin k))
    (hfeas : ∀ i j, μ i = some j → j < i)
    (hinj : ∀ i i' j, μ i = some j → μ i' = some j → i = i')
    (hnone : ∀ i i', μ i = none → μ i' = none → i = i') :
    ∀ i : Fin k,
      μ i = if 0 < i.val then
          some ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
        else none := by
  have H : ∀ n, ∀ i : Fin k, i.val ≤ n →
      μ i = if 0 < i.val then
          some ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
        else none := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have h0 : i.val = 0 := Nat.le_zero.mp hi
      rw [if_neg (by omega)]
      cases hμ : μ i with
      | none => rfl
      | some j =>
        have hj := hfeas i j hμ
        rw [Fin.lt_def] at hj
        exact absurd hj (by omega)
    | succ n ihn =>
      intro i hi
      rcases Nat.lt_or_ge i.val (n + 1) with h | h
      · exact ihn i (Nat.lt_succ_iff.mp h)
      have hval : i.val = n + 1 := Nat.le_antisymm hi h
      have hik : i.val < k := i.isLt
      rw [if_pos (by omega)]
      cases hμ : μ i with
      | none =>
        -- index 0 is unmatched too (nothing lies below it), contradicting uniqueness
        have hk : 0 < k := i.pos
        have h0 : μ ⟨0, hk⟩ = none := by
          have h00 := ihn ⟨0, hk⟩ (Nat.zero_le n)
          rwa [if_neg (Nat.lt_irrefl 0)] at h00
        have hi0 : i = ⟨0, hk⟩ := hnone i ⟨0, hk⟩ hμ h0
        have : i.val = 0 := by rw [hi0]
        exact absurd this (by omega)
      | some j =>
        have hj : j.val < i.val := by
          have hj' := hfeas i j hμ
          rwa [Fin.lt_def] at hj'
        rcases Nat.lt_or_ge j.val n with hjn | hjn
        · -- j sits below i - 1, but then index j + 1 already maps to j
          have hi' : j.val + 1 < k := by omega
          have hIH := ihn ⟨j.val + 1, hi'⟩ (show j.val + 1 ≤ n by omega)
          rw [if_pos (Nat.succ_pos j.val)] at hIH
          have hj' : μ ⟨j.val + 1, hi'⟩ = some j := by
            rw [hIH]
            exact congrArg some (Fin.ext (show j.val + 1 - 1 = j.val by omega))
          have heq := hinj i ⟨j.val + 1, hi'⟩ j hμ hj'
          have hv : i.val = j.val + 1 := by rw [heq]
          exact absurd hv (by omega)
        · -- j.val = i.val - 1
          exact congrArg some (Fin.ext (show j.val = i.val - 1 by omega))
  exact fun i => H i.val i le_rfl

/-- Timestamp-keyed form: strictly increasing send timestamps, the LessThan bound
    `prevTs i < sendTs i`, and a matching that equates `prevTs` with the matched send's
    timestamp force the consecutive cascade. -/
theorem cascade_forced {k : ℕ} {T : Type*} [LinearOrder T]
    (sendTs prevTs : Fin k → T) (hmono : StrictMono sendTs)
    (hlt : ∀ i, prevTs i < sendTs i)
    (μ : Fin k → Option (Fin k))
    (hts : ∀ i j, μ i = some j → prevTs i = sendTs j)
    (hinj : ∀ i i' j, μ i = some j → μ i' = some j → i = i')
    (hnone : ∀ i i', μ i = none → μ i' = none → i = i') :
    ∀ i : Fin k,
      μ i = if 0 < i.val then
          some ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
        else none :=
  matching_below_forced μ
    (fun i j hij => by
      have h := hlt i
      rw [hts i j hij] at h
      exact hmono.lt_iff_lt.mp h)
    hinj hnone
