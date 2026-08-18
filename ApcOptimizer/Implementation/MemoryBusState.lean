import ApcOptimizer.MemoryBus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Consequences of the memory-bus relies

The audited discipline (`admissibleMemoryBusM`, `ApcOptimizer/MemoryBus.lean`) constrains the
field-valued net bus state; the passes consume two derived forms. `excessBounded` is the count
form, recovered by `excessBounded_of_admissibleMemoryBusM`: the state determines the counts
because the rely also fixes every multiplicity to `±setNewMult` and keeps the message count below
`p`. `admissibleMemoryBus` is the *positional* form the sweep passes consume — not assumed by any
VM rely, but derived on a certified canonical access order
(`interleaveAccesses_admissibleMemoryBus_of_M`, `Implementation/MemoryBusMultiset.lean`). The
`_perm` theorems record that each rely assumes nothing about the interaction list's order. -/

variable {p : ℕ}

/-- Count form of the discipline: at every evaluated address, the receives' payload multiset
    exceeds the sends' by at most one element — the entry receive. -/
def excessBounded (shape : MemoryBusShape) (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)), Multiset.card (excessAt shape addr M) ≤ 1

/-! ## The positional form -/

/-- The positional discipline the pass proofs consume — for an *ordered* list of one bus's
    messages: after a `setNew` to a given address (multiplicity `shape.setNewMult`), the next
    `getPrevious` from the same address (multiplicity `-shape.setNewMult`) observes the same
    payload, with no intervening active messages to the same address. -/
def admissibleMemoryBus (shape : MemoryBusShape) (L : List (BusInteraction (ZMod p))) : Prop :=
  ∀ (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
    L = pre ++ S :: mid ++ R :: post →
    S.multiplicity = shape.setNewMult → R.multiplicity = -shape.setNewMult →
    shape.address S = shape.address R →
    (∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
    S.payload = R.payload

/-- The count form is invariant under reordering the interaction list. -/
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

/-- The net bus state is invariant under reordering the interaction list. -/
theorem busState_perm {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    busState L = busState L' :=
  funext fun _ => ((h.filter _).map _).sum_eq

/-- The state discipline is invariant under reordering the interaction list. -/
theorem admissibleMemoryBusM_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    admissibleMemoryBusM shape L ↔ admissibleMemoryBusM shape L' := by
  unfold admissibleMemoryBusM
  refine and_congr (forall_congr' fun m => imp_congr h.mem_iff Iff.rfl)
    (and_congr (by rw [h.length_eq]) (forall_congr' fun addr => ?_))
  rw [busState_perm (h.filter _)]

/-- The whole per-bus rely is invariant under reordering the interaction list. -/
theorem MemoryBusShape.rely_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    shape.rely L ↔ shape.rely L' := by
  unfold MemoryBusShape.rely
  refine and_congr (admissibleMemoryBusM_perm shape h)
    (and_congr (forall_congr' fun slot => forall_congr' fun bound => imp_congr Iff.rfl ?_)
      (forall_congr' fun slot => forall_congr' fun key => imp_congr Iff.rfl ?_))
  · exact tsBounded_perm slot bound h
  · exact entryKeyed_perm shape slot key h

/-- One cons step of the net bus state. -/
theorem busState_cons (m : BusInteraction (ZMod p)) (T : List (BusInteraction (ZMod p)))
    (key : BusMessage p) :
    busState (m :: T) key
      = (if (m.busId, m.payload) = key then m.multiplicity else 0) + busState T key := by
  unfold busState
  rw [List.filter_cons]
  by_cases h : (m.busId, m.payload) = key
  · simp [h]
  · simp [h]

/-- The net state at key `(b, P)` counts the address group's sends and receives carrying payload
    `P`: it is their difference, scaled by `setNewMult`. -/
private theorem busState_count (shape : MemoryBusShape) (b : Nat)
    (addr : List (Option (ZMod p))) (P : List (ZMod p))
    (hne : (shape.setNewMult : ZMod p) ≠ -shape.setNewMult)
    (L : List (BusInteraction (ZMod p))) :
    (∀ m ∈ L, m.busId = b) →
    (∀ m ∈ L, m.multiplicity = shape.setNewMult ∨ m.multiplicity = -shape.setNewMult) →
    busState (L.filter (fun m => shape.address m = addr)) (b, P)
      = (Multiset.count P (Multiset.map BusInteraction.payload
            (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) : ZMod p)
          * shape.setNewMult
        - (Multiset.count P (Multiset.map BusInteraction.payload
            (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) : ZMod p)
          * shape.setNewMult := by
  induction L with
  | nil => intro _ _; simp [busState, sendsAt, recvsAt]
  | cons m T ih =>
    intro hbus hmults
    have ihT := ih (fun x hx => hbus x (List.mem_cons_of_mem _ hx))
      (fun x hx => hmults x (List.mem_cons_of_mem _ hx))
    have hbusm : m.busId = b := hbus m List.mem_cons_self
    unfold sendsAt recvsAt at ihT ⊢
    rw [← Multiset.cons_coe]
    by_cases haddr : shape.address m = addr
    · rw [List.filter_cons_of_pos (by simpa using haddr), busState_cons]
      rcases hmults m List.mem_cons_self with hmult | hmult
      · -- `m` is a send: the receive fiber requires `setNewMult = -setNewMult`, excluded
        rw [Multiset.filter_cons_of_pos _ ⟨hmult, haddr⟩,
          Multiset.filter_cons_of_neg _ (fun hc => hne (hmult.symm.trans hc.1)),
          Multiset.map_cons, Multiset.count_cons]
        by_cases hpay : m.payload = P
        · rw [if_pos (by rw [hbusm, hpay]), if_pos hpay.symm, hmult, ihT]
          push_cast
          ring
        · rw [if_neg (fun hc => hpay (congrArg Prod.snd hc)), if_neg (fun hc => hpay hc.symm),
            ihT, zero_add, add_zero]
      · -- `m` is a receive: the send fiber requires `-setNewMult = setNewMult`, excluded
        rw [Multiset.filter_cons_of_neg _ (fun hc => hne (hmult.symm.trans hc.1).symm),
          Multiset.filter_cons_of_pos _ ⟨hmult, haddr⟩,
          Multiset.map_cons, Multiset.count_cons]
        by_cases hpay : m.payload = P
        · rw [if_pos (by rw [hbusm, hpay]), if_pos hpay.symm, hmult, ihT]
          push_cast
          ring
        · rw [if_neg (fun hc => hpay (congrArg Prod.snd hc)), if_neg (fun hc => hpay hc.symm),
            ihT, zero_add, add_zero]
    · rw [List.filter_cons_of_neg (by simpa using haddr),
        Multiset.filter_cons_of_neg _ (fun hc => haddr hc.2),
        Multiset.filter_cons_of_neg _ (fun hc => haddr hc.2)]
      exact ihT

/-- The count form follows from the state form on a single bus's messages: with every
    multiplicity `±setNewMult` and fewer than `p` messages, the field-valued net state
    determines the counts. -/
theorem excessBounded_of_admissibleMemoryBusM (shape : MemoryBusShape) {b : Nat}
    {L : List (BusInteraction (ZMod p))} (hbus : ∀ m ∈ L, m.busId = b)
    (h : admissibleMemoryBusM shape L) :
    excessBounded shape (↑L : Multiset (BusInteraction (ZMod p))) := by
  obtain ⟨hmults, hlen, hstate⟩ := h
  by_cases hL : L = []
  · subst hL
    intro addr
    simp [excessAt, recvsAt, sendsAt]
  · -- a nonempty list forces `p > 2`, so `setNewMult ≠ -setNewMult` and counts embed into `ZMod p`
    have hp3 : 2 < p := by
      have := List.length_pos_iff.mpr hL
      omega
    haveI : NeZero p := ⟨by omega⟩
    have hss : shape.setNewMult * shape.setNewMult = (1 : ZMod p) := by
      cases h : shape.direction <;> simp [MemoryBusShape.setNewMult, h]
    have hne : (shape.setNewMult : ZMod p) ≠ -shape.setNewMult := by
      intro he
      have h20 : ((2 : ℕ) : ZMod p) = 0 := by
        have h2 := congrArg (· * shape.setNewMult) (eq_neg_iff_add_eq_zero.mp he)
        simp only [add_mul, zero_mul, hss] at h2
        push_cast
        linear_combination h2
      have := Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h20)
      omega
    have cancel : ∀ {x y : ZMod p},
        x * shape.setNewMult = y * shape.setNewMult → x = y := by
      intro x y hxy
      calc x = x * shape.setNewMult * shape.setNewMult := by rw [mul_assoc, hss, mul_one]
      _ = y * shape.setNewMult * shape.setNewMult := by rw [hxy]
      _ = y := by rw [mul_assoc, hss, mul_one]
    have cast_eq : ∀ {a c : ℕ}, a < p → c < p → ((a : ZMod p) = (c : ZMod p)) → a = c := by
      intro a c ha hc hac
      have := congrArg ZMod.val hac
      rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hc] at this
    intro addr
    have count_le : ∀ (P : List (ZMod p)) (M : Multiset (BusInteraction (ZMod p))),
        M ≤ (↑L : Multiset (BusInteraction (ZMod p))) →
        Multiset.count P (Multiset.map BusInteraction.payload M) ≤ L.length := by
      intro P M hM
      calc Multiset.count P (Multiset.map BusInteraction.payload M)
          ≤ Multiset.card (Multiset.map BusInteraction.payload M) := Multiset.count_le_card _ _
      _ = Multiset.card M := Multiset.card_map _ _
      _ ≤ Multiset.card (↑L : Multiset (BusInteraction (ZMod p))) := Multiset.card_le_card hM
      _ = L.length := Multiset.coe_card _
    have sends_le : sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))) ≤ ↑L :=
      Multiset.filter_le _ _
    have recvs_le : recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))) ≤ ↑L :=
      Multiset.filter_le _ _
    obtain hz | ⟨entry, exitR, hex⟩ := hstate addr
    · -- balanced: receive and send counts agree at every payload, so the excess is empty
      have hcount : ∀ P : List (ZMod p),
          Multiset.count P (Multiset.map BusInteraction.payload
            (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p)))))
          = Multiset.count P (Multiset.map BusInteraction.payload
            (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) := by
        intro P
        have h0 := congrFun hz (b, P)
        rw [busState_count shape b addr P hne L hbus hmults] at h0
        simp only [sub_eq_zero] at h0
        exact (cast_eq (by have := count_le P _ sends_le; omega) (by have := count_le P _ recvs_le; omega) (cancel h0)).symm
      have : excessAt shape addr (↑L : Multiset (BusInteraction (ZMod p))) = 0 := by
        unfold excessAt
        exact tsub_eq_zero_of_le (Multiset.le_iff_count.mpr fun P => (hcount P).le)
      rw [this]
      simp
    · -- one enters, one exits: the excess is at most the entry's payload
      have hsub : excessAt shape addr (↑L : Multiset (BusInteraction (ZMod p)))
          ≤ ({entry.2} : Multiset (List (ZMod p))) := by
        unfold excessAt
        rw [Multiset.sub_le_iff_le_add]
        refine Multiset.le_iff_count.mpr fun P => ?_
        rw [Multiset.count_add]
        have hP := congrFun hex (b, P)
        rw [busState_count shape b addr P hne L hbus hmults] at hP
        by_cases hPe : ((b, P) : BusMessage p) = entry
        · -- the entry payload: one more receive than send, matched by the singleton
          rw [if_pos hPe] at hP
          have hPeq : P = entry.2 := by rw [← hPe]
          have hcast : (Multiset.count P (Multiset.map BusInteraction.payload
                (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) : ZMod p)
              = ((Multiset.count P (Multiset.map BusInteraction.payload
                (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) + 1 : ℕ) : ZMod p) := by
            push_cast
            exact cancel (by linear_combination -hP)
          have hcnt := cast_eq (by have := count_le P _ recvs_le; omega)
            (by have := count_le P _ sends_le; omega) hcast
          rw [Multiset.count_singleton, if_pos hPeq]
          omega
        · rw [if_neg hPe] at hP
          by_cases hPx : ((b, P) : BusMessage p) = exitR
          · -- the exit payload: one more send than receive
            rw [if_pos hPx] at hP
            have hcast : (Multiset.count P (Multiset.map BusInteraction.payload
                  (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) : ZMod p)
                = ((Multiset.count P (Multiset.map BusInteraction.payload
                  (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) + 1 : ℕ) : ZMod p) := by
              push_cast
              exact cancel (by linear_combination hP)
            have hcnt := cast_eq (by have := count_le P _ sends_le; omega)
              (by have := count_le P _ recvs_le; omega) hcast
            omega
          · -- any other payload balances
            rw [if_neg hPx] at hP
            simp only [sub_eq_zero] at hP
            have hcnt := cast_eq (by have := count_le P _ sends_le; omega) (by have := count_le P _ recvs_le; omega) (cancel hP)
            omega
      calc Multiset.card (excessAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))
          ≤ Multiset.card ({entry.2} : Multiset (List (ZMod p))) := Multiset.card_le_card hsub
      _ = 1 := Multiset.card_singleton _
