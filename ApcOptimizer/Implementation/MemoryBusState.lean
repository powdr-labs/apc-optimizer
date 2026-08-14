import ApcOptimizer.MemoryBus
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Consequences of the memory-bus relies

Everything derived from the audited definitions in `ApcOptimizer/MemoryBus.lean`.

`excessBounded` is the count-based form the passes consume; the audited rely is stated on the
field-valued `busState` instead. On a single bus, and with every multiplicity `±setNewMult`,
`busState` at a message is `(sends - receives) * setNewMult` (`busState_eq_counts`), and the rely's
length bound keeps both counts below `p`, so the field equation pins the counts down — no count can
wrap. `excessBounded_of_admissibleMemoryBusM` is the bridge; it is applied once per VM, in
`BusFacts.admissible_sound`.

The order-freeness section carries the auditor-facing sanity theorems: each rely is invariant under
reordering the interaction list, which is what "order-free" means. -/

variable {p : ℕ}

/-! ## The count-based form -/

/-- The count-based consequence of the discipline, and the form the passes consume: at every
    evaluated address, the receives' payload multiset exceeds the sends' by at most one element — the
    entry receive. Derived from the audited rely by `excessBounded_of_admissibleMemoryBusM`, so a
    pass never has to establish it. -/
def excessBounded (shape : MemoryBusShape) (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)), Multiset.card (excessAt shape addr M) ≤ 1

/-! ## Order-freeness -/

/-- The net bus state does not depend on the order of the interaction list. -/
theorem busState_perm {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    busState L = busState L' := by
  funext message
  exact ((h.filter _).map _).sum_eq

/-- The discipline is invariant under reordering the interaction list. -/
theorem admissibleMemoryBusM_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    admissibleMemoryBusM shape L ↔ admissibleMemoryBusM shape L' := by
  have hstate : ∀ addr : List (Option (ZMod p)),
      busState (L.filter (fun m => shape.address m = addr))
        = busState (L'.filter (fun m => shape.address m = addr)) :=
    fun _ => busState_perm (h.filter _)
  unfold admissibleMemoryBusM
  simp only [hstate, h.length_eq]
  exact and_congr (forall_congr' fun _ => imp_congr h.mem_iff Iff.rfl) Iff.rfl

/-- The count-based bound is invariant under reordering the interaction list. -/
theorem excessBounded_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    excessBounded shape (L : Multiset (BusInteraction (ZMod p))) ↔
      excessBounded shape (L' : Multiset (BusInteraction (ZMod p))) := by
  rw [Multiset.coe_eq_coe.mpr h]

/-- The entry designation is invariant under reordering the interaction list. -/
theorem entryKeyed_perm (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    entryKeyed shape slot key (L : Multiset (BusInteraction (ZMod p))) ↔
      entryKeyed shape slot key (L' : Multiset (BusInteraction (ZMod p))) := by
  rw [Multiset.coe_eq_coe.mpr h]

/-- The timestamp bound is invariant under reordering the interaction list. -/
theorem tsBounded_perm (tsField bound : Nat) {L L' : List (BusInteraction (ZMod p))}
    (h : L.Perm L') : tsBounded tsField bound L ↔ tsBounded tsField bound L' :=
  forall_congr' fun _ => imp_congr h.mem_iff Iff.rfl

/-! ## From the net bus state to payload counts -/

/-- The receives of exactly `payload` in `M`, counted. -/
private def recvCount (shape : MemoryBusShape) (M : List (BusInteraction (ZMod p)))
    (payload : List (ZMod p)) : Nat :=
  M.countP fun m => decide (m.multiplicity = -shape.setNewMult ∧ m.payload = payload)

/-- The sends of exactly `payload` in `M`, counted. -/
private def sendCount (shape : MemoryBusShape) (M : List (BusInteraction (ZMod p)))
    (payload : List (ZMod p)) : Nat :=
  M.countP fun m => decide (m.multiplicity = shape.setNewMult ∧ m.payload = payload)

private theorem busState_cons (m : BusInteraction (ZMod p)) (M : List (BusInteraction (ZMod p)))
    (key : BusMessage p) :
    busState (m :: M) key =
      (if (m.busId, m.payload) = key then m.multiplicity else 0) + busState M key := by
  unfold busState
  rw [List.filter_cons]
  by_cases h : (m.busId, m.payload) = key <;> simp [h]

/-- On a single bus, with multiplicities `±setNewMult`, the net state at a message is the count
    difference. Needs `setNewMult ≠ -setNewMult`, else a send would also count as a receive. -/
private theorem busState_eq_counts (shape : MemoryBusShape) {b : Nat} (P : List (ZMod p))
    (hne : (shape.setNewMult : ZMod p) ≠ -shape.setNewMult)
    (M : List (BusInteraction (ZMod p))) (hbus : ∀ m ∈ M, m.busId = b)
    (hmult : ∀ m ∈ M, m.multiplicity = shape.setNewMult ∨ m.multiplicity = -shape.setNewMult) :
    busState M (b, P) =
      ((sendCount shape M P : ZMod p) - (recvCount shape M P : ZMod p)) * shape.setNewMult := by
  induction M with
  | nil => simp [busState, recvCount, sendCount]
  | cons m M ih =>
    have hmem : ∀ x ∈ M, x ∈ m :: M := fun x hx => List.mem_cons_of_mem m hx
    rw [busState_cons, ih (fun x hx => hbus x (hmem x hx)) (fun x hx => hmult x (hmem x hx))]
    have hb : m.busId = b := hbus m List.mem_cons_self
    by_cases hP : m.payload = P
    · have hkey : ((m.busId, m.payload) = (b, P)) := by rw [hb, hP]
      rcases hmult m List.mem_cons_self with hm | hm
      · have hs : sendCount shape (m :: M) P = sendCount shape M P + 1 := by
          unfold sendCount; rw [List.countP_cons]; simp [hm, hP]
        have hr : recvCount shape (m :: M) P = recvCount shape M P := by
          unfold recvCount; rw [List.countP_cons]; simp [hm, hP, hne]
        rw [hs, hr, if_pos hkey, hm]
        push_cast
        ring
      · have hs : sendCount shape (m :: M) P = sendCount shape M P := by
          unfold sendCount; rw [List.countP_cons]; simp [hm, hP, Ne.symm hne]
        have hr : recvCount shape (m :: M) P = recvCount shape M P + 1 := by
          unfold recvCount; rw [List.countP_cons]; simp [hm, hP]
        rw [hs, hr, if_pos hkey, hm]
        push_cast
        ring
    · have hkey : ¬((m.busId, m.payload) = (b, P)) := fun h => hP (Prod.ext_iff.mp h).2
      have hs : sendCount shape (m :: M) P = sendCount shape M P := by
        unfold sendCount; rw [List.countP_cons]; simp [hP]
      have hr : recvCount shape (m :: M) P = recvCount shape M P := by
        unfold recvCount; rw [List.countP_cons]; simp [hP]
      rw [hs, hr, if_neg hkey, zero_add]

/-! ## The payload counts of `excessAt` -/

private theorem count_payloads_filter (shape : MemoryBusShape)
    (M : List (BusInteraction (ZMod p))) (P : List (ZMod p)) (mult : ZMod p) :
    Multiset.count P
        (((M : Multiset (BusInteraction (ZMod p))).filter
          (fun m => m.multiplicity = mult ∧ shape.address m = shape.addressOf P)).map
            BusInteraction.payload) =
      M.countP (fun m => decide (m.multiplicity = mult ∧ m.payload = P)) := by
  rw [Multiset.count_map, Multiset.filter_filter, ← Multiset.countP_eq_card_filter,
    Multiset.coe_countP]
  refine List.countP_congr fun m _ => ?_
  by_cases hp : m.payload = P
  · subst hp; simp [MemoryBusShape.address]
  · simp [hp, Ne.symm hp]

private theorem count_excessAt (shape : MemoryBusShape) (M : List (BusInteraction (ZMod p)))
    (P : List (ZMod p)) :
    Multiset.count P (excessAt shape (shape.addressOf P) (M : Multiset _)) =
      recvCount shape M P - sendCount shape M P := by
  rw [excessAt, Multiset.count_sub, recvsAt, sendsAt, count_payloads_filter,
    count_payloads_filter, recvCount, sendCount]

/-- Only payloads living at `addr` can be in excess there. -/
private theorem address_of_mem_excessAt (shape : MemoryBusShape)
    {M : Multiset (BusInteraction (ZMod p))} {addr : List (Option (ZMod p))}
    {P : List (ZMod p)} (h : P ∈ excessAt shape addr M) : shape.addressOf P = addr := by
  obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le (Multiset.sub_le_self _ _) h)
  exact (Multiset.of_mem_filter hm).2

/-- Restricting to one address does not change the state at a payload sitting *at* that address:
    the address is a projection of the payload, so no message carrying that payload is filtered
    out. -/
private theorem busState_filter_address (shape : MemoryBusShape) {b : Nat}
    (M : List (BusInteraction (ZMod p))) {P : List (ZMod p)} {addr : List (Option (ZMod p))}
    (hP : shape.addressOf P = addr) :
    busState (M.filter (fun m => shape.address m = addr)) (b, P) = busState M (b, P) := by
  unfold busState
  rw [List.filter_filter]
  refine congrArg _ (congrArg _ (List.filter_congr fun m _ => ?_))
  by_cases hkey : (m.busId, m.payload) = ((b, P) : BusMessage p)
  · have hpay : m.payload = P := (Prod.ext_iff.mp hkey).2
    simp [MemoryBusShape.address, hpay, hP]
  · simp [hkey]

private theorem natCast_inj_of_lt {a c : ℕ} (ha : a < p) (hc : c < p)
    (h : (a : ZMod p) = (c : ZMod p)) : a = c := by
  haveI : NeZero p := ⟨by omega⟩
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hc] at hval

/-! ## The bridge -/

/-- The audited state-based rely gives the count-based bound the passes consume. `M` is one bus's
    active messages, as `BusFacts.admissible_sound` presents them. -/
theorem excessBounded_of_admissibleMemoryBusM (shape : MemoryBusShape) {b : Nat}
    {M : List (BusInteraction (ZMod p))} (hbus : ∀ m ∈ M, m.busId = b)
    (h : admissibleMemoryBusM shape M) :
    excessBounded shape (M : Multiset (BusInteraction (ZMod p))) := by
  obtain ⟨hmult, hlen, hstate⟩ := h
  rcases Nat.lt_or_ge p 3 with hp | hp
  · -- Such a field has no room for two messages, so nothing is in excess.
    have hM : M = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro addr
    simp [hM, excessAt, recvsAt, sendsAt]
  -- `setNewMult` is `±1`: a unit, and distinct from its negation once `3 ≤ p`.
  have hsq : (shape.setNewMult : ZMod p) * shape.setNewMult = 1 := by
    unfold MemoryBusShape.setNewMult
    cases shape.direction
    · exact one_mul 1
    · rw [neg_mul_neg, one_mul]
  have hne : (shape.setNewMult : ZMod p) ≠ -shape.setNewMult := by
    have h1 : (1 : ZMod p) ≠ -1 := by
      intro heq
      have hsum : (1 : ZMod p) + 1 = 0 := eq_neg_iff_add_eq_zero.mp heq
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; rw [← hsum]; ring
      exact absurd (Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h2)) (by omega)
    unfold MemoryBusShape.setNewMult
    cases shape.direction
    · simpa using h1
    · simpa using h1.symm
  have hrle : ∀ P, recvCount shape M P ≤ M.length := fun _ => List.countP_le_length
  have hsle : ∀ P, sendCount shape M P ≤ M.length := fun _ => List.countP_le_length
  -- Each of the three states a message can carry reads back as a count equation.
  have hcounts : ∀ P : List (ZMod p),
      (busState M (b, P) = 0 → sendCount shape M P = recvCount shape M P) ∧
      (busState M (b, P) = -shape.setNewMult →
        recvCount shape M P = sendCount shape M P + 1) ∧
      (busState M (b, P) = shape.setNewMult →
        sendCount shape M P = recvCount shape M P + 1) := by
    intro P
    have hrP := hrle P
    have hsP := hsle P
    -- Cancel the unit `setNewMult`, leaving the count difference.
    have hmul : ∀ X : ZMod p, busState M (b, P) = X →
        (sendCount shape M P : ZMod p) - (recvCount shape M P : ZMod p) = X * shape.setNewMult := by
      intro X hX
      rw [← hX, busState_eq_counts shape P hne M hbus hmult, mul_assoc, hsq, mul_one]
    refine ⟨fun h0 => ?_, fun hentry => ?_, fun hexit => ?_⟩
    · have hd := hmul 0 h0
      rw [zero_mul] at hd
      exact natCast_inj_of_lt (p := p) (a := sendCount shape M P) (c := recvCount shape M P)
        (by omega) (by omega) (sub_eq_zero.mp hd)
    · have hd := hmul _ hentry
      rw [neg_mul, hsq] at hd
      refine (natCast_inj_of_lt (p := p) (a := sendCount shape M P + 1)
        (c := recvCount shape M P) (by omega) (by omega) ?_).symm
      rw [show ((sendCount shape M P + 1 : ℕ) : ZMod p)
        = (sendCount shape M P : ZMod p) + 1 by push_cast; ring, sub_eq_iff_eq_add.mp hd]
      ring
    · have hd := hmul _ hexit
      rw [hsq] at hd
      refine natCast_inj_of_lt (p := p) (a := sendCount shape M P)
        (c := recvCount shape M P + 1) (by omega) (by omega) ?_
      rw [show ((recvCount shape M P + 1 : ℕ) : ZMod p)
        = (recvCount shape M P : ZMod p) + 1 by push_cast; ring, sub_eq_iff_eq_add.mp hd]
      ring
  intro addr
  -- A payload in excess at `addr` is the entry record's, so there is one of them, once.
  have key : ∀ P Q : List (ZMod p), shape.addressOf P = addr → shape.addressOf Q = addr →
      sendCount shape M P < recvCount shape M P → sendCount shape M Q < recvCount shape M Q →
      recvCount shape M P = sendCount shape M P + 1 ∧ P = Q := by
    intro P Q hP hQ hltP hltQ
    rcases hstate addr with hzero | ⟨entry, exitRecord, hex⟩
    · have := (hcounts P).1 (by
        rw [← busState_filter_address shape M hP, hzero])
      omega
    have entry_of : ∀ R : List (ZMod p), shape.addressOf R = addr →
        sendCount shape M R < recvCount shape M R →
        ((b, R) : BusMessage p) = entry ∧ recvCount shape M R = sendCount shape M R + 1 := by
      intro R hR hltR
      have hstateR : busState M (b, R) =
          if ((b, R) : BusMessage p) = entry then -shape.setNewMult
          else if ((b, R) : BusMessage p) = exitRecord then shape.setNewMult else 0 := by
        rw [← busState_filter_address shape M hR, hex]
      by_cases he : ((b, R) : BusMessage p) = entry
      · rw [if_pos he] at hstateR
        exact ⟨he, (hcounts R).2.1 hstateR⟩
      rw [if_neg he] at hstateR
      by_cases hx : ((b, R) : BusMessage p) = exitRecord
      · rw [if_pos hx] at hstateR
        have := (hcounts R).2.2 hstateR
        omega
      · rw [if_neg hx] at hstateR
        have := (hcounts R).1 hstateR
        omega
    obtain ⟨hPe, hPone⟩ := entry_of P hP hltP
    obtain ⟨hQe, -⟩ := entry_of Q hQ hltQ
    exact ⟨hPone, by simpa using hPe.trans hQe.symm⟩
  have hcount : ∀ P, Multiset.count P (excessAt shape addr (M : Multiset _)) ≤ 1 := by
    intro P
    by_cases hmem : P ∈ excessAt shape addr (M : Multiset _)
    · have haddr := address_of_mem_excessAt shape hmem
      have hc := count_excessAt shape M P
      rw [haddr] at hc
      have hpos := Multiset.count_pos.mpr hmem
      have hlt : sendCount shape M P < recvCount shape M P := by omega
      have := (key P P haddr haddr hlt hlt).1
      omega
    · simp [Multiset.count_eq_zero.mpr hmem]
  rcases Multiset.empty_or_exists_mem (excessAt shape addr (M : Multiset _)) with hemp | ⟨P, hP⟩
  · simp [hemp]
  have hPaddr := address_of_mem_excessAt shape hP
  have hPlt : sendCount shape M P < recvCount shape M P := by
    have hc := count_excessAt shape M P
    rw [hPaddr] at hc
    have := Multiset.count_pos.mpr hP
    omega
  -- Every payload in excess is the entry record's, so the excess is `{P}` at most.
  have hall : ∀ Q ∈ excessAt shape addr (M : Multiset _), Q = P := by
    intro Q hQ
    have hQaddr := address_of_mem_excessAt shape hQ
    have hQlt : sendCount shape M Q < recvCount shape M Q := by
      have hc := count_excessAt shape M Q
      rw [hQaddr] at hc
      have := Multiset.count_pos.mpr hQ
      omega
    exact (key Q P hQaddr hPaddr hQlt hPlt).2
  have hcard : Multiset.card (excessAt shape addr (M : Multiset _))
      = Multiset.count P (excessAt shape addr (M : Multiset _)) := by
    rw [Multiset.eq_replicate_card.mpr hall]
    simp
  rw [hcard]
  exact hcount P
