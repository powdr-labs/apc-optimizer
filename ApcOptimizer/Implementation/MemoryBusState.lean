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

/-- The `getPrevious` messages of `M` at evaluated address `addr`. -/
def recvsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = -shape.setNewMult ∧ shape.address m = addr)

/-- The `setNew` messages of `M` at evaluated address `addr`. -/
def sendsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = shape.setNewMult ∧ shape.address m = addr)

/-- The payloads the receives at `addr` hold in excess of the sends: what enters the block from
    outside there. The discipline bounds its cardinality by one. -/
def excessAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (List (ZMod p)) :=
  (recvsAt shape addr M).map BusInteraction.payload
    - (sendsAt shape addr M).map BusInteraction.payload

/-- Count form of ENTRY_KEY (`entryKeyed`, `ApcOptimizer/MemoryBus.lean`), recovered by
    `excessKeyed_of_entryKeyed`: every payload the receives at an address hold in excess of the
    sends carries the key. -/
def excessKeyed (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ (addr : List (Option (ZMod p))) (P : List (ZMod p)),
    P ∈ excessAt shape addr M → P[slot]? = some key

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

/-- The timestamp bound is invariant under reordering the interaction list. -/
theorem tsBounded_perm (tsField bound : Nat) {L L' : List (BusInteraction (ZMod p))}
    (h : L.Perm L') : tsBounded tsField bound L ↔ tsBounded tsField bound L' :=
  forall_congr' fun _ => imp_congr h.mem_iff Iff.rfl

/-- The net bus state is invariant under reordering the interaction list. -/
theorem busState_perm {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    busState L = busState L' :=
  funext fun _ => ((h.filter _).map _).sum_eq

/-- The entry designation is invariant under reordering the interaction list. -/
theorem entryKeyed_perm (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    entryKeyed shape slot key L ↔ entryKeyed shape slot key L' := by
  unfold entryKeyed
  rw [busState_perm h]

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

/-- `setNewMult` is its own inverse. -/
private theorem setNewMult_mul_self (shape : MemoryBusShape) :
    (shape.setNewMult * shape.setNewMult : ZMod p) = 1 := by
  cases h : shape.direction <;> simp [MemoryBusShape.setNewMult, h]

/-- Above characteristic 2 a send is not a receive — what lets counts embed into the field. -/
private theorem setNewMult_ne_neg (shape : MemoryBusShape) (hp3 : 2 < p) :
    (shape.setNewMult : ZMod p) ≠ -shape.setNewMult := by
  haveI : NeZero p := ⟨by omega⟩
  intro he
  have h20 : ((2 : ℕ) : ZMod p) = 0 := by
    have h2 := congrArg (· * shape.setNewMult) (eq_neg_iff_add_eq_zero.mp he)
    simp only [add_mul, zero_mul, setNewMult_mul_self] at h2
    push_cast
    linear_combination h2
  have := Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h20)
  omega

/-- The payload counts an address group's net state pins down: with fewer than `p` messages on the
    bus, a state of `(i - j) • setNewMult` at `(b, P)` forces `sends + j = recvs + i`. The three
    cases of `admissibleMemoryBusM` are `(i, j) = (0, 0)`, `(1, 0)` (the exit record) and `(0, 1)`
    (the entry record). -/
private theorem counts_of_busState (shape : MemoryBusShape) {b : Nat}
    {L : List (BusInteraction (ZMod p))} (hbus : ∀ m ∈ L, m.busId = b)
    (hmults : ∀ m ∈ L, m.multiplicity = shape.setNewMult ∨ m.multiplicity = -shape.setNewMult)
    (hlen : L.length + 1 < p) (hp3 : 2 < p)
    {addr : List (Option (ZMod p))} {P : List (ZMod p)} {i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 1)
    (hstate : busState (L.filter (fun m => shape.address m = addr)) (b, P)
      = ((i : ZMod p) - (j : ZMod p)) * shape.setNewMult) :
    Multiset.count P (Multiset.map BusInteraction.payload
          (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) + j
      = Multiset.count P (Multiset.map BusInteraction.payload
          (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) + i := by
  haveI : NeZero p := ⟨by omega⟩
  rw [busState_count shape b addr P (setNewMult_ne_neg shape hp3) L hbus hmults] at hstate
  set S := Multiset.count P (Multiset.map BusInteraction.payload
    (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p)))))
  set R := Multiset.count P (Multiset.map BusInteraction.payload
    (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p)))))
  have count_le : ∀ M : Multiset (BusInteraction (ZMod p)),
      M ≤ (↑L : Multiset (BusInteraction (ZMod p))) →
      Multiset.count P (Multiset.map BusInteraction.payload M) ≤ L.length := by
    intro M hM
    calc Multiset.count P (Multiset.map BusInteraction.payload M)
        ≤ Multiset.card (Multiset.map BusInteraction.payload M) := Multiset.count_le_card _ _
    _ = Multiset.card M := Multiset.card_map _ _
    _ ≤ Multiset.card (↑L : Multiset (BusInteraction (ZMod p))) := Multiset.card_le_card hM
    _ = L.length := Multiset.coe_card _
  have hSle : S ≤ L.length := count_le _ (Multiset.filter_le _ _)
  have hRle : R ≤ L.length := count_le _ (Multiset.filter_le _ _)
  -- cancel `setNewMult`, then read the equation back in `ℕ`: both sides are below `p`
  have hfield : ((S + j : ℕ) : ZMod p) = ((R + i : ℕ) : ZMod p) := by
    have h := congrArg (· * shape.setNewMult) hstate
    simp only [sub_mul, mul_assoc, setNewMult_mul_self, mul_one] at h
    push_cast
    linear_combination h
  have hval := congrArg ZMod.val hfield
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval

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
  have hp3 : 2 < p := by
    have := List.length_pos_iff.mpr hL
    omega
  intro addr
  obtain hz | ⟨entry, exitR, hex⟩ := hstate addr
  · -- balanced: receive and send counts agree at every payload, so the excess is empty
    have hempty : excessAt shape addr (↑L : Multiset (BusInteraction (ZMod p))) = 0 := by
      unfold excessAt
      refine tsub_eq_zero_of_le (Multiset.le_iff_count.mpr fun P => ?_)
      have := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 0) (j := 0) (by omega) (by omega)
        (by simpa using congrFun hz (b, P))
      omega
    rw [hempty]
    simp
  · -- one enters, one exits: the excess is at most the entry record's payload
    have hsub : excessAt shape addr (↑L : Multiset (BusInteraction (ZMod p)))
        ≤ ({entry.2} : Multiset (List (ZMod p))) := by
      unfold excessAt
      rw [Multiset.sub_le_iff_le_add]
      refine Multiset.le_iff_count.mpr fun P => ?_
      rw [Multiset.count_add]
      have hP := congrFun hex (b, P)
      by_cases hPe : ((b, P) : BusMessage p) = entry
      · have hcnt := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 0) (j := 1)
          (by omega) (by omega) (by rw [hP, if_pos hPe]; push_cast; ring)
        rw [Multiset.count_singleton, if_pos (show P = entry.2 from by rw [← hPe])]
        omega
      · rw [if_neg hPe] at hP
        by_cases hPx : ((b, P) : BusMessage p) = exitR
        · have hcnt := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 1) (j := 0)
            (by omega) (by omega) (by rw [hP, if_pos hPx]; push_cast; ring)
          omega
        · have hcnt := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 0) (j := 0)
            (by omega) (by omega) (by rw [hP, if_neg hPx]; push_cast; ring)
          omega
    calc Multiset.card (excessAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))
        ≤ Multiset.card ({entry.2} : Multiset (List (ZMod p))) := Multiset.card_le_card hsub
    _ = 1 := Multiset.card_singleton _

/-- Filtering by an address keeps every message carrying a payload with that address, so the net
    state at such a message is unchanged. -/
private theorem busState_filter_addr (shape : MemoryBusShape) (b : Nat) (P : List (ZMod p))
    (L : List (BusInteraction (ZMod p))) :
    busState (L.filter (fun m => shape.address m = shape.addressOf P)) (b, P)
      = busState L (b, P) := by
  unfold busState
  rw [List.filter_filter]
  congr 2
  refine List.filter_congr fun m _ => ?_
  by_cases h : (m.busId, m.payload) = ((b, P) : BusMessage p)
  · have haddr : shape.address m = shape.addressOf P := by
      unfold MemoryBusShape.address
      rw [show m.payload = P from by simpa using congrArg Prod.snd h]
    simp [h, haddr]
  · simp [h]

/-- The count form of ENTRY_KEY: a payload the receives at an address hold in excess of the sends is
    an unmatched receive — the discipline leaves no other state value for it — so `entryKeyed`
    keys it. -/
theorem excessKeyed_of_entryKeyed (shape : MemoryBusShape) {b slot : Nat} {key : ZMod p}
    {L : List (BusInteraction (ZMod p))} (hbus : ∀ m ∈ L, m.busId = b)
    (hadm : admissibleMemoryBusM shape L) (hkey : entryKeyed shape slot key L) :
    excessKeyed shape slot key (↑L : Multiset (BusInteraction (ZMod p))) := by
  obtain ⟨hmults, hlen, hstate⟩ := hadm
  intro addr P hP
  have hlt : Multiset.count P (Multiset.map BusInteraction.payload
        (sendsAt shape addr (↑L : Multiset (BusInteraction (ZMod p)))))
      < Multiset.count P (Multiset.map BusInteraction.payload
        (recvsAt shape addr (↑L : Multiset (BusInteraction (ZMod p))))) := by
    have hpos := Multiset.count_pos.mpr hP
    rw [excessAt, Multiset.count_sub] at hpos
    omega
  -- a receive carries `P` at `addr`, so `addr` is `P`'s address and `L` is nonempty
  obtain ⟨R, hR, hRp⟩ :=
    Multiset.mem_map.mp (Multiset.count_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
  obtain ⟨hRmem, -, hRaddr⟩ := Multiset.mem_filter.mp hR
  have haddr : shape.addressOf P = addr := by
    rw [← hRp]
    exact hRaddr
  have hp3 : 2 < p := by
    have : 0 < L.length :=
      List.length_pos_iff.mpr (fun hnil => by rw [hnil] at hRmem; simp at hRmem)
    omega
  subst haddr
  obtain hz | ⟨entry, exitR, hex⟩ := hstate (shape.addressOf P)
  · have := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 0) (j := 0) (by omega) (by omega)
      (by simpa using congrFun hz (b, P))
    omega
  · have hP' := congrFun hex (b, P)
    by_cases hPe : ((b, P) : BusMessage p) = entry
    · rw [if_pos hPe] at hP'
      exact hkey b P (by rw [← busState_filter_addr shape b P L]; exact hP')
    · rw [if_neg hPe] at hP'
      by_cases hPx : ((b, P) : BusMessage p) = exitR
      · have := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 1) (j := 0)
          (by omega) (by omega) (by rw [hP', if_pos hPx]; push_cast; ring)
        omega
      · have := counts_of_busState shape hbus hmults hlen hp3 (P := P) (i := 0) (j := 0)
          (by omega) (by omega) (by rw [hP', if_neg hPx]; push_cast; ring)
        omega
