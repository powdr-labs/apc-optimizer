import ApcOptimizer.Implementation.BusFacts
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Implementation.MemoryBusDrop

set_option autoImplicit false

/-!
# Proven bus facts for the OpenVM semantics

The `BusFacts` instance for `openVmBusSemantics` (see `ApcOptimizer/Implementation/BusFacts.lean`
for the design). Every claim is proven against the audited `accepts`/`maintainsInvariants`, so none
needs auditing. Parameterized by the bus map (defaulting to `defaultBusMap`).
-/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}


/-! ## Deciding the semantics

The audited `accepts`/`maintainsInvariants` are `Prop`s, so a pass cannot evaluate them. `violates`
and `breaksInvariant` below are the `Bool` decision procedures the pipeline actually runs, each
proven equivalent to its audited counterpart (`violates_eq_false_iff`,
`breaksInvariant_eq_false_iff`); the helper lemmas in this file are stated over them and bridged at
the `BusFacts` interface. -/

private def isByteB (x : ZMod p) : Bool := decide (x.val < 256)

private theorem isByteB_iff (x : ZMod p) : isByteB x = true ↔ isByte x := by
  simp [isByteB, isByte]

private def isByteCheckedB (f : MemoryPayload p) : Bool :=
  f.addressSpace.val == 1 || f.addressSpace.val == 2

private theorem isByteCheckedB_iff (f : MemoryPayload p) :
    isByteCheckedB f = true ↔ f.isByteChecked := by
  simp [isByteCheckedB, MemoryPayload.isByteChecked]

/-- Bool decision procedure for `accepts` (`violates_eq_false_iff`). -/
private def violates (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Bool :=
  match busMap msg.busId, msg.payload with
  | some .pcLookup, args => !decide (args.length = 9)
  | some .bitwiseLookup, [x, y, z, op] =>
    match op.val with
    | 0 => !(isByteB x && isByteB y && decide (z.val = 0))
    | 1 => !(isByteB x && isByteB y && decide (z.val = Nat.xor x.val y.val))
    | _ => true
  | some .variableRangeChecker, [x, bits] =>
    !(decide (bits.val ≤ 17) && decide (x.val < 2 ^ bits.val))
  | some (.tupleRangeChecker s1 s2), [x, y] =>
    !(decide (x.val < s1) && decide (y.val < s2))
  | some .bitwiseLookup, _ => true
  | some .variableRangeChecker, _ => true
  | some (.tupleRangeChecker _ _), _ => true
  | some .executionBridge, _ => false
  | some .memory, payload =>
    match memoryPayload? payload with
    | some f => decide (msg.multiplicity = -1) && isByteCheckedB f && !(f.data.all isByteB)
    | none => false
  | none, _ => true

/-- Bool decision procedure for `maintainsInvariants` (`breaksInvariant_eq_false_iff`). -/
private def breaksInvariant (busMap : BusMap)
    (msg : BusInteraction (ZMod p)) : Bool :=
  match busMap msg.busId with
  | some .pcLookup | some .variableRangeChecker | some .bitwiseLookup
  | some (.tupleRangeChecker _ _) =>
    !decide (msg.multiplicity = 1)
  | some .executionBridge =>
    !decide (msg.multiplicity = 1 ∨ msg.multiplicity = -1)
  | some .memory =>
    !decide (msg.multiplicity = 1 ∨ msg.multiplicity = -1) ||
    (match memoryPayload? msg.payload with
      | some f => bif isByteCheckedB f then !(f.data.all isByteB) else false
      | none => false)
  | none => true

private theorem all_isByteB_iff (v : Vector (ZMod p) 4) :
    v.all isByteB = true ↔ ∀ d ∈ v, isByte d := by
  rw [Vector.all_eq_true_iff_forall_mem]
  simp only [isByteB_iff]

private theorem forall_isByteB_iff (v : Vector (ZMod p) 4) :
    (∀ (i : Nat) (h : i < 4), isByteB v[i] = true) ↔ ∀ d ∈ v, isByte d :=
  Vector.all_eq_true.symm.trans (all_isByteB_iff v)

private theorem violates_eq_false_iff (busMap : BusMap)
    (m : BusInteraction (ZMod p)) : violates busMap m = false ↔ accepts busMap m := by
  obtain ⟨bid, mult, payload⟩ := m
  unfold violates accepts
  cases hb : busMap bid with
  | none => simp
  | some t =>
    cases t with
    | executionBridge => simp
    | pcLookup => simp
    | variableRangeChecker =>
        rcases payload with _ | ⟨x, _ | ⟨b, _ | ⟨w, rest⟩⟩⟩ <;> simp
    | tupleRangeChecker s1 s2 =>
        rcases payload with _ | ⟨x, _ | ⟨y, _ | ⟨w, rest⟩⟩⟩ <;> simp
    | bitwiseLookup =>
        rcases payload with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨op, _ | ⟨w, rest⟩⟩⟩⟩⟩ <;> try simp
        rcases op.val with _ | _ | n <;> simp [isByteB_iff, and_assoc]
    | memory =>
        cases hp : memoryPayload? payload with
        | none => simp [hp]
        | some f =>
            simp [hp, isByteCheckedB_iff, forall_isByteB_iff, imp_iff_not_or, or_assoc]

private theorem breaksInvariant_eq_false_iff (busMap : BusMap)
    (m : BusInteraction (ZMod p)) :
    breaksInvariant busMap m = false ↔ maintainsInvariants busMap m := by
  obtain ⟨bid, mult, payload⟩ := m
  unfold breaksInvariant maintainsInvariants
  cases hb : busMap bid with
  | none => simp
  | some t =>
    cases t with
    | pcLookup => simp
    | variableRangeChecker => simp
    | bitwiseLookup => simp
    | tupleRangeChecker s1 s2 => simp
    | executionBridge => simp [or_iff_not_imp_left]
    | memory =>
        cases hp : memoryPayload? payload with
        | none => simp [or_iff_not_imp_left]
        | some f =>
            cases hc : isByteCheckedB f with
            | false =>
                have hnc : ¬ f.isByteChecked := fun h => by
                  simp [(isByteCheckedB_iff f).mpr h] at hc
                simp [hc, hnc, or_iff_not_imp_left]
            | true =>
                simp [hc, (isByteCheckedB_iff f).mp hc, forall_isByteB_iff,
                  or_iff_not_imp_left]


/-- The `BusFacts` interface speaks the audited `accepts`; the lemmas here speak `violates`. Marked
`@[simp]` so field proofs translate without restating each one. -/
@[simp] private theorem openVm_accepts_iff (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) :
    (openVmBusSemantics p busMap entryPc).accepts m ↔ violates busMap m = false :=
  (violates_eq_false_iff busMap m).symm

@[simp] private theorem openVm_maintains_iff (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) :
    (openVmBusSemantics p busMap entryPc).maintainsInvariants m ↔ breaksInvariant busMap m = false :=
  (breaksInvariant_eq_false_iff busMap m).symm


private def slotBoundImpl (busMap : BusMap) (busId : Nat) (mult : ZMod p)
    (pattern : List (Option (ZMod p))) (slot : Nat) : Option Nat :=
  match busMap busId, pattern, slot with
  | some .bitwiseLookup, [_, _, _, some op], 0 => if op.val ≤ 1 then some 256 else none
  | some .bitwiseLookup, [_, _, _, some op], 1 => if op.val ≤ 1 then some 256 else none
  -- Slot 2 is the bitwise result `z`: op 0 forces `z = 0`, op 1 forces `z = x ^ y` with byte
  -- operands, so `z` is a byte either way (op ≥ 2 violates).
  | some .bitwiseLookup, [_, _, _, some op], 2 => if op.val ≤ 1 then some 256 else none
  | some .variableRangeChecker, [_, some bits], 0 =>
      if bits.val ≤ 17 then some (2 ^ bits.val) else none
  | some (.tupleRangeChecker s1 _), [_, _], 0 => some s1
  | some (.tupleRangeChecker _ s2), [_, _], 1 => some s2
  -- Data limbs (slots 2–5) of a memory receive (multiplicity -1) from address space 1/2 are
  -- bytes; payload is `(addressSpace, pointer, data×4, timestamp)`.
  | some .memory, [some as, _, _, _, _, _, _], 2 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | some .memory, [some as, _, _, _, _, _, _], 3 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | some .memory, [some as, _, _, _, _, _, _], 4 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | some .memory, [some as, _, _, _, _, _, _], 5 =>
      if mult = -1 ∧ (as.val = 1 ∨ as.val = 2) then some 256 else none
  | _, _, _ => none

private def slotFunImpl (busMap : BusMap) (busId : Nat)
    (pattern : List (Option (ZMod p))) (outSlot : Nat) :
    Option (List (ZMod p) → ZMod p) :=
  match busMap busId, pattern, outSlot with
  | some .bitwiseLookup, [_, _, _, some op], 2 =>
      if op.val = 1 then
        some (fun payload =>
          match payload with
          | [x, y, _, _] => ((Nat.xor x.val y.val : Nat) : ZMod p)
          | _ => 0)
      else none
  | _, _, _ => none

private def neverViolatesImpl (busMap : BusMap) (busId : Nat) : Bool :=
  match busMap busId with
  | some .executionBridge => true
  -- Memory and pcLookup are not listed: memory's `violates` rejects non-byte receives from
  -- address spaces 1/2 (see `recvByteSlots`), and pcLookup rejects payloads of length ≠ 9.
  | _ => false

/-- The PC lookup is checked for arity only, so a 9-field message never violates. -/
private def neverViolatesArityImpl (busMap : BusMap) (busId : Nat)
    (arity : Nat) : Bool :=
  match busMap busId with
  | some .pcLookup => arity == 9
  | _ => false

/-- Byte-slot obligation for a memory-style pair cancellation, conditioned on the receive's
    constant pattern (bound `256`, OpenVM limbs are bytes). A memory `getPrevious` whose
    address-space slot (slot 0) is a constant ∉ {1,2} carries no obligation (`some ([], 256)`),
    since `violates` only rejects non-byte data on address spaces 1/2; otherwise slots 2–5 must be
    bytes. The execution bridge never violates; other buses claim nothing. -/
private def recvByteSlotsImpl (busMap : BusMap) (busId : Nat)
    (pattern : List (Option (ZMod p))) : Option (List Nat × Nat) :=
  match busMap busId with
  | some .memory =>
    match pattern[0]? with
    | some (some as) => some ((if as.val = 1 ∨ as.val = 2 then [2, 3, 4, 5] else []), 256)
    | _ => some ([2, 3, 4, 5], 256)
  | some .executionBridge => some ([], 256)
  | _ => none

/-- OpenVM bitwise payload `[x, y, z, op]` decodes to logical `(op, x, y, z)`. -/
def bitwiseDecode {α : Type} : List α → Option (α × α × α × α)
  | [x, y, z, op] => some (op, x, y, z)
  | _ => none

theorem bitwiseDecode_some {α : Type} {pl : List α} {a b c d : α} :
    bitwiseDecode pl = some (a, b, c, d) ↔ pl = [b, c, d, a] := by
  constructor
  · intro h
    rcases pl with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | ⟨e, tl⟩⟩⟩⟩⟩ <;> simp_all [bitwiseDecode]
  · intro h; subst h; rfl

theorem bitwiseDecode_map {α β : Type} (f : α → β) (pl : List α) :
    bitwiseDecode (pl.map f)
      = (bitwiseDecode pl).map (fun t => (f t.1, f t.2.1, f t.2.2.1, f t.2.2.2)) := by
  rcases pl with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | ⟨e, tl⟩⟩⟩⟩⟩ <;> rfl

theorem bitwiseDecode_mem {α : Type} (pl : List α) (op o1 o2 r : α)
    (h : bitwiseDecode pl = some (op, o1, o2, r)) : o1 ∈ pl ∧ o2 ∈ pl ∧ r ∈ pl := by
  rw [bitwiseDecode_some] at h; subst h; simp

/-- Emit an OpenVM bitwise payload `[operand₁, operand₂, result, op]`, inverting `bitwiseDecode`. -/
def bitwiseEncode {α : Type} (op o1 o2 r : α) : List α := [o1, o2, r, op]

theorem bitwiseDecode_encode {α : Type} (op o1 o2 r : α) :
    bitwiseDecode (bitwiseEncode op o1 o2 r) = some (op, o1, o2, r) := rfl

theorem bitwiseDecode_eq_encode {α : Type} (pl : List α) (op o1 o2 r : α)
    (h : bitwiseDecode pl = some (op, o1, o2, r)) : pl = bitwiseEncode op o1 o2 r := by
  rw [bitwiseDecode_some] at h; exact h

theorem bitwiseEncode_map {α β : Type} (f : α → β) (op o1 o2 r : α) :
    (bitwiseEncode op o1 o2 r).map f = bitwiseEncode (f op) (f o1) (f o2) (f r) := rfl

theorem bitwiseEncode_mem {α : Type} (op o1 o2 r x : α)
    (h : x ∈ bitwiseEncode op o1 o2 r) : x = op ∨ x = o1 ∨ x = o2 ∨ x = r := by
  simp only [bitwiseEncode, List.mem_cons, List.not_mem_nil, or_false] at h; tauto

/-- The fixed-zero cell of the OpenVM memory bus: `x0` = address `(as, ptr) = (1, 0)`, data limbs
    at slots `2..5`; `none` for non-memory buses. -/
private def zeroCellImpl (busMap : BusMap) (busId : Nat) :
    Option (List (Nat × ZMod p) × List Nat) :=
  match busMap busId with
  | some .memory => some ([(0, 1), (1, 0)], [2, 3, 4, 5])
  | _ => none

private theorem payload_four {payload : List (ZMod p)} {p0 p1 p2 p3 : Option (ZMod p)}
    (h : Matches payload [p0, p1, p2, p3]) :
    ∃ a b c d, payload = [a, b, c, d] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

private theorem payload_two {payload : List (ZMod p)} {p0 p1 : Option (ZMod p)}
    (h : Matches payload [p0, p1]) :
    ∃ a b, payload = [a, b] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a, b], _ => exact ⟨a, b, rfl⟩

private theorem payload_seven {payload : List (ZMod p)}
    {p0 p1 p2 p3 p4 p5 p6 : Option (ZMod p)}
    (h : Matches payload [p0, p1, p2, p3, p4, p5, p6]) :
    ∃ a0 a1 d0 d1 d2 d3 t, payload = [a0, a1, d0, d1, d2, d3, t] := by
  obtain ⟨hlen, _⟩ := h
  match payload, hlen with
  | [a0, a1, d0, d1, d2, d3, t], _ => exact ⟨a0, a1, d0, d1, d2, d3, t, rfl⟩

/-- An execution-bridge message never violates. -/
private theorem execBridge_ok (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .executionBridge) :
    (openVmBusSemantics p busMap entryPc).accepts m := by
  rw [openVm_accepts_iff]
  unfold violates
  rw [hbus]

/-- A PC lookup with the expected nine fields never violates (`violates` checks its arity only). -/
private theorem pcLookup_ok (busMap : BusMap)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .pcLookup)
    (harity : m.payload.length = 9) :
    violates busMap m = false := by
  unfold violates
  rw [hbus]
  simp [harity]

/-- The data limbs of an accepted (non-violating) memory *receive* from address space 1 or 2
    are bytes. -/
private theorem memory_recv_bytes (busMap : BusMap)
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = -1)
    (a0 a1 d0 d1 d2 d3 t : ZMod p) (hpay : m.payload = [a0, a1, d0, d1, d2, d3, t])
    (has : a0.val = 1 ∨ a0.val = 2)
    (hok : violates busMap m = false) :
    d0.val < 256 ∧ d1.val < 256 ∧ d2.val < 256 ∧ d3.val < 256 := by
  unfold violates at hok
  rw [hbus, hpay, hm] at hok
  have has' : (a0.val == 1 || a0.val == 2) = true := by
    rcases has with h | h <;> simp [h]
  simp only [memoryPayload?, isByteCheckedB, decide_true, has', Bool.true_and,
    Bool.not_eq_false', Vector.all_eq_true, isByteB, decide_eq_true_eq] at hok
  exact ⟨hok 0 (by omega), hok 1 (by omega), hok 2 (by omega), hok 3 (by omega)⟩

/-- A memory message that is not a receive (multiplicity ≠ -1) never violates. -/
private theorem memory_nonRecv_ok (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity ≠ -1) : (openVmBusSemantics p busMap entryPc).accepts m := by
  rw [openVm_accepts_iff]
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩ <;>
    simp [memoryPayload?, hm]

/-- A memory *send* (multiplicity 1) never violates: either the characteristic is > 2 and a
    send is not a receive, or `p ∣ 2` and every value is trivially a byte. -/
private theorem memory_send_ok [NeZero p] (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = 1) : (openVmBusSemantics p busMap entryPc).accepts m := by
  rw [openVm_accepts_iff]
  by_cases hc : (1 : ZMod p) = -1
  · -- `p ∣ 2`: every value is `< 2 ≤ 256`, so the byte test never fails.
    have hadd : (1 : ZMod p) + 1 = 0 := (congrArg (· + 1) hc).trans (neg_add_cancel 1)
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat, ← one_add_one_eq_two]
      exact hadd
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
    have hbyte : ∀ d : ZMod p, d.val < 256 :=
      fun d => lt_of_lt_of_le (ZMod.val_lt d)
        (le_trans (Nat.le_of_dvd (by decide) hp2) (by decide))
    obtain ⟨bid, mult, payload⟩ := m
    simp only at hbus
    unfold violates
    rw [hbus]
    rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩ <;>
      simp [memoryPayload?, isByteCheckedB, isByteB, hbyte]
  · exact (openVm_accepts_iff busMap m).mp
      (memory_nonRecv_ok busMap (entryPc := entryPc) m hbus (by rw [hm]; exact hc))

/-- A memory *receive* (multiplicity -1) with byte data limbs (payload slots 2–5, where
    present) never violates. -/
private theorem memory_recv_ok (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (hm : m.multiplicity = -1)
    (hslots : ∀ slot ∈ [2, 3, 4, 5], ∀ x : ZMod p, m.payload[slot]? = some x → x.val < 256) :
    (openVmBusSemantics p busMap entryPc).accepts m := by
  rw [openVm_accepts_iff]
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus hm hslots
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, rest⟩⟩⟩⟩⟩⟩ <;>
    try rfl
  have h0 : d0.val < 256 := hslots 2 (by simp) d0 rfl
  have h1 : d1.val < 256 := hslots 3 (by simp) d1 rfl
  have h2 : d2.val < 256 := hslots 4 (by simp) d2 rfl
  have h3 : d3.val < 256 := hslots 5 (by simp) d3 rfl
  simp [memoryPayload?, isByteCheckedB, isByteB, h0, h1, h2, h3]

/-- A memory message whose address-space slot (slot 0) is a constant ∉ {1, 2} never violates:
    `violates` only rejects non-byte data on address spaces 1 and 2. -/
private theorem memory_recv_nonByte_ok (busMap : BusMap) {entryPc : Option (ZMod p)}
    (m : BusInteraction (ZMod p)) (hbus : busMap m.busId = some .memory)
    (as : ZMod p) (hasval : ¬ (as.val = 1 ∨ as.val = 2)) (has : m.payload[0]? = some as) :
    (openVmBusSemantics p busMap entryPc).accepts m := by
  rw [openVm_accepts_iff]
  obtain ⟨bid, mult, payload⟩ := m
  simp only at hbus has
  unfold violates
  rw [hbus]
  rcases payload with _ | ⟨a0, _ | ⟨a1, _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩⟩⟩ <;>
    try rfl
  -- only the 6+-element case remains; `a0` is the address space, equal to `as`
  simp only [List.getElem?_cons_zero, Option.some.injEq] at has
  push Not at hasval
  obtain ⟨hne1, hne2⟩ := hasval
  have hmid : (a0.val == 1 || a0.val == 2) = false := by
    rw [has]
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨hne1, hne2⟩
  simp only [memoryPayload?, isByteCheckedB, hmid, Bool.and_false, Bool.false_and]

/-- A bus with a declared last-write-wins shape (memory or execution bridge) is stateful. -/
theorem openVm_isStateful_of_memShape {p : ℕ} (busMap : BusMap) {entryPc : Option (ZMod p)}
    (busId : Nat) (shape : MemoryBusShape) (h : memShapeOf busMap busId = some shape) :
    (openVmBusSemantics p busMap entryPc).isStateful busId = true := by
  show (match busMap busId with | some t => t.isStateful | none => false) = true
  unfold memShapeOf at h
  generalize busMap busId = o at h ⊢
  cases o with
  | none => simp at h
  | some t => cases t <;> simp_all [OpenVmBusType.isStateful]

/-- On a stateful bus, restricting the active stateful messages to the bus is the same as
    restricting the bus's messages to the active ones — the form every per-bus rely is stated in. -/
theorem openVm_filter_active_busId {p : ℕ} (busMap : Nat → Option OpenVmBusType)
    (entryPc : Option (ZMod p)) (msgs : List (BusInteraction (ZMod p))) (busId : Nat)
    (hstateful : (openVmBusSemantics p busMap entryPc).isStateful busId = true) :
    (msgs.filter (fun m => decide (m.multiplicity ≠ 0) &&
        (openVmBusSemantics p busMap entryPc).isStateful m.busId)).filter
        (fun m => m.busId = busId)
      = (msgs.filter (fun m => m.busId = busId)).filter
          (fun m => decide (m.multiplicity ≠ 0)) := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro m _
  by_cases hb : m.busId = busId
  · rw [hb, hstateful]; simp
  · simp [hb]

/-- A bus with a declared timestamp slot (memory or execution bridge) is stateful. -/
private theorem openVm_isStateful_of_memTsField {p : ℕ} (busMap : Nat → Option OpenVmBusType) {entryPc : Option (ZMod p)}
    (busId slot : Nat) (h : memTsFieldOf busMap busId = some slot) :
    (openVmBusSemantics p busMap entryPc).isStateful busId = true := by
  show (match busMap busId with | some t => t.isStateful | none => false) = true
  unfold memTsFieldOf at h
  generalize busMap busId = o at h ⊢
  cases o with
  | none => simp at h
  | some t => cases t <;> simp_all [OpenVmBusType.isStateful]

/-- Every OpenVM shape uses `direction := .receiveThenSend`, so `setNewMult` reduces to `1`. -/
private theorem memShapeOf_setNewMult_eq_one {p : ℕ} (busMap : BusMap)
    (busId : Nat) (shape : MemoryBusShape) (h : memShapeOf busMap busId = some shape) :
    (shape.setNewMult : ZMod p) = 1 := by
  unfold memShapeOf at h
  split at h
  · obtain rfl := Option.some.inj h; rfl
  · obtain rfl := Option.some.inj h; rfl
  · exact absurd h (by simp)

/-- The proven facts about `openVmBusSemantics`, for any bus map. -/
def openVmFacts (p : ℕ) [NeZero p]
    (busMap : BusMap := defaultBusMap)
    (entryPc : Option (ZMod p) := none) :
    BusFacts p (openVmBusSemantics p busMap entryPc) where
  acceptsDec m := !violates busMap m
  acceptsDec_iff m := by
    rw [Bool.not_eq_true']
    exact violates_eq_false_iff busMap m
  slotBound := slotBoundImpl busMap
  slotBound_sound := by
    intro m pattern slot bound x hfact hmatch hok hget
    have hok' : violates busMap m = false := (openVm_accepts_iff busMap m).mp hok
    unfold slotBoundImpl at hfact
    split at hfact
    · -- bitwise lookup, slot 0
      rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hx : a = x := by rw [hpay] at hget; simpa using hget
      subst hx hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0 <;>
        · simp only [h0] at hok'
          rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
          exact of_decide_eq_true hok'.1.1
    · -- bitwise lookup, slot 1
      rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hx : b = x := by rw [hpay] at hget; simpa using hget
      subst hx hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0 <;>
        · simp only [h0] at hok'
          rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
          exact of_decide_eq_true hok'.1.2
    · -- bitwise lookup, slot 2 (the XOR/AND result is a byte)
      rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hx : c = x := by rw [hpay] at hget; simpa using hget
      subst hx hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hop with h0 | h0
      · -- op = 0: `z = 0`
        simp only [h0] at hok'
        rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
        rw [of_decide_eq_true hok'.2]; decide
      · -- op = 1: `z = x ^ y` with byte operands
        simp only [h0] at hok'
        rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
        have hxa : a.val < 2 ^ 8 := of_decide_eq_true hok'.1.1
        have hxb : b.val < 2 ^ 8 := of_decide_eq_true hok'.1.2
        rw [of_decide_eq_true hok'.2]
        exact Nat.xor_lt_two_pow hxa hxb
    · -- variable range checker
      rename_i q0 bits hbus
      split_ifs at hfact with hbits
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, hpay⟩ := payload_two hmatch
      have hb : b = bits := by
        have h1 := hmatch.2 1 bits (by simp)
        rw [hpay] at h1; simpa using h1
      have hx : a = x := by rw [hpay] at hget; simpa using hget
      subst hx hb
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true] at hok'
      exact of_decide_eq_true hok'.2
    · -- tuple range checker, slot 0
      rename_i s1 s2 q0 q1 hbus
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, hpay⟩ := payload_two hmatch
      have hx : a = x := by rw [hpay] at hget; simpa using hget
      subst hx
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      simp only [] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true] at hok'
      exact of_decide_eq_true hok'.1
    · -- tuple range checker, slot 1
      rename_i s1 s2 q0 q1 hbus
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, hpay⟩ := payload_two hmatch
      have hx : b = x := by rw [hpay] at hget; simpa using hget
      subst hx
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      simp only [] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true] at hok'
      exact of_decide_eq_true hok'.2
    · -- memory receive, slot 2
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d0 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').1
    · -- memory receive, slot 3
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d1 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').2.1
    · -- memory receive, slot 4
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d2 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').2.2.1
    · -- memory receive, slot 5
      rename_i as q1 q2 q3 q4 q5 q6 hbus
      split_ifs at hfact with hcond
      obtain ⟨hmult, has⟩ := hcond
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a0, a1, d0, d1, d2, d3, t, hpay⟩ := payload_seven hmatch
      have ha0 : a0 = as := by
        have h0 := hmatch.2 0 as (by simp)
        rw [hpay] at h0; simpa using h0
      have hx : d3 = x := by rw [hpay] at hget; simpa using hget
      rw [← hx]
      exact (memory_recv_bytes busMap m hbus hmult a0 a1 d0 d1 d2 d3 t hpay
        (by rw [ha0]; exact has) hok').2.2.2
    · exact absurd hfact (by simp)
  slotFun := slotFunImpl busMap
  slotFun_sound := by
    intro m pattern outSlot f z hfact hmatch hok hget
    have hok' : violates busMap m = false := (openVm_accepts_iff busMap m).mp hok
    unfold slotFunImpl at hfact
    split at hfact
    · rename_i q0 q1 q2 op hbus
      split_ifs at hfact with hop
      simp only [Option.some.injEq] at hfact
      subst hfact
      obtain ⟨a, b, c, d, hpay⟩ := payload_four hmatch
      have hd : d = op := by
        have h3 := hmatch.2 3 op (by simp)
        rw [hpay] at h3; simpa using h3
      have hz : c = z := by rw [hpay] at hget; simpa using hget
      subst hz hd
      unfold violates at hok'
      rw [hbus, hpay] at hok'
      simp only [hop] at hok'
      rw [Bool.not_eq_false', Bool.and_eq_true, Bool.and_eq_true] at hok'
      have hxor : c.val = Nat.xor a.val b.val := of_decide_eq_true hok'.2
      rw [hpay]
      show c = ((Nat.xor a.val b.val : Nat) : ZMod p)
      rw [← hxor]
      exact (ZMod.natCast_rightInverse c).symm
    · exact absurd hfact (by simp)
  neverViolates := neverViolatesImpl busMap
  neverViolates_sound := by
    intro m h
    unfold neverViolatesImpl at h
    split at h
    · rename_i hbus; exact execBridge_ok busMap m hbus
    · exact absurd h (by simp)
  neverViolatesArity := neverViolatesArityImpl busMap
  neverViolatesArity_sound := by
    intro m h
    unfold neverViolatesArityImpl at h
    split at h
    · rename_i hbus
      exact (openVm_accepts_iff busMap m).mpr (pcLookup_ok busMap m hbus (by simpa using h))
    · exact absurd h (by simp)
  recvByteSlots := recvByteSlotsImpl busMap
  recvByteSlots_sound := by
    intro busId shape hmemshape pattern slots bound hfact m hbusId
    have hw : (shape.setNewMult : ZMod p) = 1 :=
      memShapeOf_setNewMult_eq_one busMap busId shape hmemshape
    simp only [hw]
    subst hbusId
    unfold recvByteSlotsImpl at hfact
    cases hbus : busMap m.busId with
    | none => rw [hbus] at hfact; simp at hfact
    | some bt =>
      cases bt with
      | executionBridge =>
        rw [hbus] at hfact
        simp only [Option.some.injEq, Prod.mk.injEq] at hfact
        obtain ⟨rfl, rfl⟩ := hfact
        exact ⟨fun _ => execBridge_ok busMap m hbus, fun _ _ _ => execBridge_ok busMap m hbus⟩
      | memory =>
        rw [hbus] at hfact
        cases hp0 : pattern[0]? with
        | none =>
          rw [hp0] at hfact
          simp only [Option.some.injEq, Prod.mk.injEq] at hfact
          obtain ⟨rfl, rfl⟩ := hfact
          exact ⟨fun hm => memory_send_ok busMap m hbus hm,
                 fun hm _ hbytes => memory_recv_ok busMap m hbus hm hbytes⟩
        | some oas =>
          cases oas with
          | none =>
            rw [hp0] at hfact
            simp only [Option.some.injEq, Prod.mk.injEq] at hfact
            obtain ⟨rfl, rfl⟩ := hfact
            exact ⟨fun hm => memory_send_ok busMap m hbus hm,
                   fun hm _ hbytes => memory_recv_ok busMap m hbus hm hbytes⟩
          | some as =>
            rw [hp0] at hfact
            simp only [Option.some.injEq, Prod.mk.injEq] at hfact
            obtain ⟨rfl, rfl⟩ := hfact
            refine ⟨fun hm => memory_send_ok busMap m hbus hm, fun hm hmatch hbytes => ?_⟩
            split_ifs at hbytes with hcase
            · exact memory_recv_ok busMap m hbus hm hbytes
            · exact memory_recv_nonByte_ok busMap m hbus as hcase (hmatch.2 0 as hp0)
      | pcLookup => rw [hbus] at hfact; simp at hfact
      | variableRangeChecker => rw [hbus] at hfact; simp at hfact
      | bitwiseLookup => rw [hbus] at hfact; simp at hfact
      | tupleRangeChecker s1 s2 => rw [hbus] at hfact; simp at hfact
  memShape := memShapeOf busMap
  memShape_stateful := fun busId shape hshape =>
    openVm_isStateful_of_memShape busMap busId shape hshape
  admissible_sound := by
    intro msgs hadm busId shape hshape
    have hstateful : (openVmBusSemantics p busMap entryPc).isStateful busId = true :=
      openVm_isStateful_of_memShape busMap busId shape hshape
    -- `openVmBusSemantics.admissible` is the per-bus `admissibleMemoryBusM` conjunction, `.1`
    have hd := hadm.1 busId shape hshape
    rwa [openVm_filter_active_busId busMap entryPc msgs busId hstateful] at hd
  memTsField busId := (memTsFieldOf busMap busId).map (fun slot => (slot, 2 ^ 29))
  memTsField_sound := by
    intro msgs hadm busId slot bound hfact m hm hmne
    rw [List.mem_filter] at hm
    obtain ⟨hmem, hbusEq⟩ := hm
    have hbusEq : m.busId = busId := by simpa using hbusEq
    cases hof : memTsFieldOf busMap busId with
    | none => rw [hof] at hfact; simp at hfact
    | some tsField =>
      rw [hof] at hfact
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hfact
      obtain ⟨rfl, rfl⟩ := hfact
      -- the declared bus is stateful, so `m` survives the active∧stateful filter and the
      -- TS_BOUND conjunct (`.2.1`) applies to it
      have hstateful : (openVmBusSemantics p busMap entryPc).isStateful m.busId = true := by
        rw [hbusEq]; exact openVm_isStateful_of_memTsField busMap busId _ hof
      have hmfilt : m ∈ msgs.filter (fun m => decide (m.multiplicity ≠ 0) &&
          (openVmBusSemantics p busMap entryPc).isStateful m.busId) := by
        rw [List.mem_filter]
        exact ⟨hmem, by rw [hstateful, decide_eq_true hmne]; rfl⟩
      refine hadm.2.1 busId _ hof m ?_
      rw [List.mem_filter]
      exact ⟨hmfilt, decide_eq_true hbusEq⟩
  memEntryKey := memEntryKeyOf busMap entryPc
  memEntryKey_sound := by
    intro msgs hadm busId slot key shape hshape hkey
    have hstateful : (openVmBusSemantics p busMap entryPc).isStateful busId = true :=
      openVm_isStateful_of_memShape busMap busId shape hshape
    -- `openVmBusSemantics.admissible`'s ENTRY_KEY conjunct is `.2.2.1`
    have hd := hadm.2.2.1 busId slot key shape hshape hkey
    rwa [openVm_filter_active_busId busMap entryPc msgs busId hstateful] at hd
  admissible_dropPair := by
    -- `openVmBusSemantics.admissible` is the per-declared-bus `admissibleMemoryBusM` conjunction
    -- (`.1`) together with the TS_BOUND clause (`.2.1`), the ENTRY_KEY clause (`.2.2.1`) and the
    -- `zeroRegisterReads` clause (`.2.2.2`).
    intro busId shape hshape A B C S R hSbus hRbus hSm hRm hpay hadm_full
    obtain ⟨hdisc, hts, hkey, hzero⟩ := hadm_full
    refine ⟨fun busId' shape' hshape' => ?_, fun busId' tsField htf => ?_,
      fun busId' slot key shape' hshape' hkeyf => ?_, ?_⟩
    · -- memory discipline conjunct
      by_cases hbb : busId' = busId
      · subst busId'
        obtain rfl : shape = shape' := Option.some.inj (hshape.symm.trans hshape')
        have hfull := hdisc busId shape hshape
        have hfiltFull : (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId)
            = A.filter (fun m => m.busId = busId) ++ S :: B.filter (fun m => m.busId = busId)
              ++ R :: C.filter (fun m => m.busId = busId) := by
          simp only [List.filter_append, List.filter_cons, hSbus, hRbus, decide_true, if_true]
        have hgoal : (A ++ B ++ C).filter (fun m => m.busId = busId)
            = A.filter (fun m => m.busId = busId) ++ B.filter (fun m => m.busId = busId)
              ++ C.filter (fun m => m.busId = busId) := by
          simp only [List.filter_append]
        rw [hfiltFull, coe_split_pair] at hfull
        rw [hgoal]
        exact admissibleMemoryBusM_dropPair shape hSm hRm hpay hfull
      · -- `busId' ≠ busId`: `S`, `R` are on `busId`, so they drop out and the filter is unchanged.
        have hne : busId ≠ busId' := fun h => hbb h.symm
        have heq : (A ++ B ++ C).filter (fun m => m.busId = busId')
            = (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId') := by
          simp only [List.filter_append, List.filter_cons, hSbus, hRbus,
            decide_eq_false hne, Bool.false_eq_true, if_false]
        rw [heq]
        exact hdisc busId' shape' hshape'
    · -- TS_BOUND conjunct: `A ++ B ++ C`'s members are all members of the full list.
      intro m hm
      refine hts busId' tsField htf m ?_
      rw [List.mem_filter] at hm ⊢
      refine ⟨?_, hm.2⟩
      have hmem := hm.1
      simp only [List.mem_append, List.mem_cons] at hmem ⊢
      tauto
    · -- ENTRY_KEY conjunct: same shape as the discipline conjunct (`entryKeyed_dropPair`).
      by_cases hbb : busId' = busId
      · subst busId'
        obtain rfl : shape = shape' := Option.some.inj (hshape.symm.trans hshape')
        have hfull := hkey busId slot key shape hshape hkeyf
        have hfiltFull : (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId)
            = A.filter (fun m => m.busId = busId) ++ S :: B.filter (fun m => m.busId = busId)
              ++ R :: C.filter (fun m => m.busId = busId) := by
          simp only [List.filter_append, List.filter_cons, hSbus, hRbus, decide_true, if_true]
        rw [hfiltFull, coe_split_pair] at hfull
        rw [show (A ++ B ++ C).filter (fun m => m.busId = busId)
            = A.filter (fun m => m.busId = busId) ++ B.filter (fun m => m.busId = busId)
              ++ C.filter (fun m => m.busId = busId) from by simp only [List.filter_append]]
        exact entryKeyed_dropPair shape slot key hSm hRm hpay hfull
      · have hne : busId ≠ busId' := fun h => hbb h.symm
        rw [show (A ++ B ++ C).filter (fun m => m.busId = busId')
            = (A ++ S :: B ++ R :: C).filter (fun m => m.busId = busId') from by
          simp only [List.filter_append, List.filter_cons, hSbus, hRbus,
            decide_eq_false hne, Bool.false_eq_true, if_false]]
        exact hkey busId' slot key shape' hshape' hkeyf
    · -- `zeroRegisterReads` conjunct: `A ++ B ++ C`'s members are all members of the full list.
      intro m hm hbus h0 h1
      have hmem : m ∈ A ++ S :: B ++ R :: C := by
        simp only [List.mem_append, List.mem_cons] at hm ⊢
        tauto
      exact hzero m hmem hbus h0 h1
  zeroRangeEq busId := match busMap busId with
    | some .variableRangeChecker => true
    | _ => false
  zeroRangeEq_sound := by
    intro busId h
    have hbus : busMap busId = some OpenVmBusType.variableRangeChecker := by
      revert h; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    refine ⟨?_, ?_⟩
    · show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · intro x
      -- variableRangeChecker `[x, 0]`: `!(0 ≤ 17 ∧ x.val < 2^0) = false ↔ x.val < 1 ↔ x = 0`.
      have hv0 : (0 : ZMod p).val = 0 := ZMod.val_zero
      rw [openVm_accepts_iff]
      show violates busMap { busId := busId, multiplicity := 1, payload := [x, 0] } = false ↔ x = 0
      unfold violates; rw [hbus]
      rw [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
        hv0, pow_zero, Nat.lt_one_iff, ZMod.val_eq_zero]
      exact ⟨fun h => h.2, fun h => ⟨Nat.zero_le 17, h⟩⟩
  varRangeBus busId := match busMap busId with
    | some .variableRangeChecker => true
    | _ => false
  varRangeBus_sound := by
    intro busId h
    have hbus : busMap busId = some OpenVmBusType.variableRangeChecker := by
      revert h; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    refine ⟨?_, ?_⟩
    · show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · intro x b mult
      rw [openVm_accepts_iff]
      show violates busMap { busId := busId, multiplicity := mult, payload := [x, b] }
          = false ↔ (b.val ≤ 17 ∧ x.val < 2 ^ b.val)
      unfold violates; rw [hbus]
      simp
  tupleRangeBus busId := match busMap busId with
    | some (.tupleRangeChecker s1 s2) => some (s1, s2)
    | _ => none
  tupleRangeBus_sound := by
    intro busId s1 s2 h
    have hbus : busMap busId = some (OpenVmBusType.tupleRangeChecker s1 s2) := by
      revert h; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp_all
    refine ⟨?_, ?_, ?_⟩
    · show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · intro x y
      rw [openVm_maintains_iff]
      show breaksInvariant busMap { busId := busId, multiplicity := 1, payload := [x, y] }
        = false
      unfold breaksInvariant; rw [hbus]; simp
    · intro x y mult
      rw [openVm_accepts_iff]
      show violates busMap { busId := busId, multiplicity := mult, payload := [x, y] }
          = false ↔ (x.val < s1 ∧ y.val < s2)
      unfold violates; rw [hbus]
      simp
  zeroCell := zeroCellImpl busMap
  zeroCell_sound := by
    intro msgs hadm busId addrReq dataSlots hfact m hm hbusId hmne haddr slot hslot v hget
    -- `zeroCell` is `some` only on memory buses; extract the fixed shape.
    unfold zeroCellImpl at hfact
    split at hfact
    · rename_i hbus
      simp only [Option.some.injEq, Prod.mk.injEq] at hfact
      obtain ⟨rfl, rfl⟩ := hfact
      -- `m` survives the active∧stateful filter, so the `zeroRegisterReads` clause applies to it.
      have hstateful : (openVmBusSemantics p busMap entryPc).isStateful m.busId = true := by
        show (match busMap m.busId with | some t => t.isStateful | none => false) = true
        rw [hbusId, hbus]; rfl
      have hmemBus : busMap m.busId = some .memory := by rw [hbusId]; exact hbus
      have hmfilt : m ∈ msgs.filter
          (fun m => decide (m.multiplicity ≠ 0) && (openVmBusSemantics p busMap entryPc).isStateful m.busId) := by
        rw [List.mem_filter]
        exact ⟨hm, by rw [hstateful, decide_eq_true hmne]; rfl⟩
      have h0 : m.payload[0]? = some 1 := haddr (0, 1) (by simp)
      have h1 : m.payload[1]? = some 0 := haddr (1, 0) (by simp)
      have hz := hadm.2.2.2 m hmfilt hmemBus h0 h1
      -- `slot ∈ [2,3,4,5]`; match it to the corresponding zero component and cancel with `hget`.
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
      rcases hslot with rfl | rfl | rfl | rfl
      · rw [hget] at hz; exact Option.some.inj hz.1
      · rw [hget] at hz; exact Option.some.inj hz.2.1
      · rw [hget] at hz; exact Option.some.inj hz.2.2.1
      · rw [hget] at hz; exact Option.some.inj hz.2.2.2
    · exact absurd hfact (by simp)
  byteXorSpec busId := match busMap busId with
    | some .bitwiseLookup =>
        some { bound := 256, xorOp := 1, pairOp := 0, decode := bitwiseDecode,
               encode := bitwiseEncode, decode_map := bitwiseDecode_map,
               decode_mem := bitwiseDecode_mem, decode_encode := bitwiseDecode_encode,
               decode_eq_encode := bitwiseDecode_eq_encode, encode_map := bitwiseEncode_map,
               encode_mem := bitwiseEncode_mem, pNeZero := inferInstance }
    | _ => none
  byteXorSpec_sound := by
    intro busId spec hspec
    have hbus : busMap busId = some .bitwiseLookup := by
      revert hspec; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    simp only [hbus] at hspec
    obtain rfl := (Option.some.inj hspec).symm
    have hv0 : (0 : ZMod p).val = 0 := ZMod.val_zero
    have h1le : (1 : ZMod p).val ≤ 1 := by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 p
    refine ⟨?_, ?_, ?_⟩
    · show (match busMap busId with | some t => t.isStateful | none => false) = false
      rw [hbus]; rfl
    · intro pl
      rw [openVm_maintains_iff]
      show breaksInvariant busMap { busId := busId, multiplicity := 1, payload := pl } = false
      unfold breaksInvariant; rw [hbus]; simp
    · intro pl op o1 o2 r mult hdec
      rw [bitwiseDecode_some] at hdec
      subst hdec
      refine ⟨fun hxor => ?_, fun hpair => ?_⟩
      · -- op = xorOp = 1
        have hop1 : op = 1 := hxor
        subst hop1
        rw [openVm_accepts_iff]
        show violates busMap { busId := busId, multiplicity := mult, payload := [o1, o2, r, 1] } = false
          ↔ o1.val < 256 ∧ o2.val < 256 ∧ r.val = Nat.xor o1.val o2.val
        unfold violates; rw [hbus]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1le with h1 | h1
        · have hp1 : p = 1 := Nat.dvd_one.mp (Nat.dvd_of_mod_eq_zero (by
            rwa [ZMod.val_one_eq_one_mod] at h1))
          subst hp1
          have ho1 : o1.val = 0 := Nat.lt_one_iff.1 (ZMod.val_lt o1)
          have ho2 : o2.val = 0 := Nat.lt_one_iff.1 (ZMod.val_lt o2)
          have hrr : r.val = 0 := Nat.lt_one_iff.1 (ZMod.val_lt r)
          simp [h1, isByteB, ho1, ho2, hrr]
        · simp [h1, isByteB, and_assoc]
      · -- op = pairOp = 0
        have hop0 : op = 0 := hpair
        subst hop0
        rw [openVm_accepts_iff]
        show violates busMap { busId := busId, multiplicity := mult, payload := [o1, o2, r, 0] } = false
          ↔ o1.val < 256 ∧ o2.val < 256 ∧ r = 0
        unfold violates; rw [hbus]
        simp [isByteB, ZMod.val_eq_zero, and_assoc]
  -- OpenVM's bitwise-lookup bus has no OR/AND op (XOR + range only), so `orOp`/`andOp` default to
  -- `none` and the boolean-op soundness is vacuous.
  byteBoolSound := by
    intro busId spec hspec
    have hbus : busMap busId = some .bitwiseLookup := by
      revert hspec; cases hb : busMap busId with
      | none => simp
      | some t => cases t <;> simp
    simp only [hbus] at hspec
    obtain rfl := (Option.some.inj hspec).symm
    intro pl op o1 o2 r mult hdec
    exact ⟨fun oop hor _ => absurd hor (by simp), fun aop hand _ => absurd hand (by simp)⟩
  -- OpenVM keeps `SubsumedRange` (its dedicated variable-range-checker bus); the layout-agnostic
  -- `rangeCheckAt` is only needed for SP1's op-6 byte-bus range check.
  rangeCheckAt _ _ := none
  rangeCheckAt_sound := by intro _ _ _ _ h; exact absurd h (by simp)

end ApcOptimizer.OpenVM
