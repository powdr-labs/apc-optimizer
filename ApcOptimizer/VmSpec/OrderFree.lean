import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! # The order-free memory-bus rely, VmSpec-local

    **Copied verbatim from `1arie1:exp/order-free-admissibility`** (`ApcOptimizer/MemoryBus.lean`
    and `ApcOptimizer/OpenVmSemantics.lean` on that branch). Nothing here is original; it lives
    under `VmSpec/` rather than in the audited surface so that the VM-level development can be
    stated against it while `ApcOptimizer/MemoryBus.lean`'s positional `admissibleMemoryBus` — and
    every optimizer pass proved against it — is left untouched.

    Why the VM level wants it: the positional discipline reads *list position* as time, and
    `Audit/AdmissibleGap.lean`'s `badChip2` is an ordinary memory write whose two halves are listed
    send-first. It violates `admissibleMemoryBus` while doing nothing wrong, so the positional
    relation is not a property any VM could force. `admissibleMemoryBusM` is invariant under
    reordering by construction (`admissibleMemoryBusM_perm`).

    Note this only replaces the `BusSemantics.admissible` *field*. `Circuit.admissible` and
    `Circuit.isCompleteReplacementOf` (`Spec.lean`) are unchanged, on that branch and here. -/

namespace ApcOptimizer.OpenVM.OrderFree

variable {p : ℕ}

--------- The multiset discipline (arie, `ApcOptimizer/MemoryBus.lean`) ---------

/-- The `getPrevious` messages of `M` at evaluated address `addr`. -/
def recvsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = -shape.setNewMult ∧ shape.address m = addr)

/-- The `setNew` messages of `M` at evaluated address `addr`. -/
def sendsAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (BusInteraction (ZMod p)) :=
  M.filter (fun m => m.multiplicity = shape.setNewMult ∧ shape.address m = addr)

/-- The payloads the receives at `addr` hold in excess of the sends: what enters the block from
    outside there. `admissibleMemoryBusM` bounds its cardinality by one. -/
def excessAt (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) : Multiset (List (ZMod p)) :=
  (recvsAt shape addr M).map BusInteraction.payload
    - (sendsAt shape addr M).map BusInteraction.payload

/-- Order-free memory-bus discipline: at every evaluated address, the receives' payload multiset
    exceeds the sends' payload multiset by at most one element — the entry receive. -/
def admissibleMemoryBusM (shape : MemoryBusShape)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ addr : List (Option (ZMod p)), Multiset.card (excessAt shape addr M) ≤ 1

/-- The discipline is invariant under reordering the interaction list. -/
theorem admissibleMemoryBusM_perm (shape : MemoryBusShape)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    admissibleMemoryBusM shape (L : Multiset (BusInteraction (ZMod p))) ↔
      admissibleMemoryBusM shape (L' : Multiset (BusInteraction (ZMod p))) := by
  rw [Multiset.coe_eq_coe.mpr h]

/-- ENTRY_KEY: every payload entering the block from outside carries `key` in slot `slot`.

    For a chain bus (an execution bridge), window atomicity already says *one* record enters; this
    says it is the block's entry record, identified by its key — the block is entered at its entry
    pc, which the optimizer is told. The designation cannot be recovered from the message multiset:
    a *rotation* of the block's records (entered at an interior instruction, wrapping through the
    exit) yields the same multiset with a different entry, so it takes an assumption to exclude. -/
def entryKeyed (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    (M : Multiset (BusInteraction (ZMod p))) : Prop :=
  ∀ (addr : List (Option (ZMod p))) (P : List (ZMod p)),
    P ∈ excessAt shape addr M → P[slot]? = some key

/-- The entry designation is invariant under reordering the interaction list. -/
theorem entryKeyed_perm (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    {L L' : List (BusInteraction (ZMod p))} (h : L.Perm L') :
    entryKeyed shape slot key (L : Multiset (BusInteraction (ZMod p))) ↔
      entryKeyed shape slot key (L' : Multiset (BusInteraction (ZMod p))) := by
  rw [Multiset.coe_eq_coe.mpr h]

/-- The `Nat` value of a message's declared timestamp slot (`0` if the payload is too short to
    have one). -/
def tsSlotVal (tsField : Nat) (m : BusInteraction (ZMod p)) : Nat :=
  ((m.payload[tsField]?).getD 0).val

/-- TS_BOUND: every message in `msgs` carries a timestamp-slot value below `bound`. Justified by
    the VM's global timestamp argument — e.g. OpenVM keeps all timestamps below `2^29` across the
    whole trace. Per-message, hence trivially preserved by dropping messages and invariant under
    reordering (`tsBounded_perm`). -/
def tsBounded (tsField bound : Nat) (msgs : List (BusInteraction (ZMod p))) : Prop :=
  ∀ m ∈ msgs, tsSlotVal tsField m < bound

/-- The timestamp bound is invariant under reordering the interaction list. -/
theorem tsBounded_perm (tsField bound : Nat) {L L' : List (BusInteraction (ZMod p))}
    (h : L.Perm L') : tsBounded tsField bound L ↔ tsBounded tsField bound L' :=
  forall_congr' fun _ => imp_congr h.mem_iff Iff.rfl

/-- The entering-record count at an address is bounded by the chip's total receive count on that
    bus — an address-independent bound, which is what makes `admissibleMemoryBusM` checkable on a
    concrete chip without case-splitting on the address. -/
theorem card_excessAt_le_recvs (shape : MemoryBusShape) (addr : List (Option (ZMod p)))
    (M : Multiset (BusInteraction (ZMod p))) :
    Multiset.card (excessAt shape addr M)
      ≤ Multiset.card (M.filter (fun m => m.multiplicity = -shape.setNewMult)) := by
  refine le_trans (Multiset.card_le_card (Multiset.sub_le_self _ _)) ?_
  rw [Multiset.card_map]
  exact Multiset.card_le_card
    (Multiset.monotone_filter_right M (fun a ha => ha.1))

--------- The OpenVM instance (arie, `ApcOptimizer/OpenVmSemantics.lean`) ---------

/-- The payload slot carrying the timestamp on a declared memory-shaped bus: slot 6 on the memory
    bus (`(address_space, pointer, data… (4 limbs), timestamp)`) and slot 1 on the execution
    bridge (`(pc, timestamp)`). -/
def memTsFieldOf (busMap : BusMap) (busId : Nat) : Option Nat :=
  match busMap busId with
  | some .memory => some 6
  | some .executionBridge => some 1
  | _ => none

/-- The entry-record designation on a chain-shaped bus (ENTRY_KEY): the execution bridge's record
    entering the block from outside carries the block's entry pc in payload slot `0`, since the
    block is entered at its first instruction. `none` — hence no assumption — where the optimizer
    was not told the block's entry pc, and on every other bus. -/
def memEntryKeyOf (busMap : BusMap) (entryPc : Option (ZMod p)) (busId : Nat) :
    Option (Nat × ZMod p) :=
  match busMap busId, entryPc with
  | some .executionBridge, some pc => some (0, pc)
  | _, _ => none

/-- The OpenVM bus semantics with the **order-free** `admissible` field. Identical to
    `openVmBusSemantics` in `isStateful`, `accepts` and `maintainsInvariants`; only the rely
    changes.

    Four conjuncts: the order-free memory discipline per declared bus; the timestamp bound
    (TS_BOUND — OpenVM's global timestamp argument keeps every timestamp below `2^29` across the
    whole trace); the entry-record designation on a chain bus (ENTRY_KEY, vacuous unless the
    block's entry pc was supplied); and the x0-returns-zero rely. -/
def openVmBusSemanticsOF (p : ℕ) (busMap : BusMap := defaultBusMap)
    (entryPc : Option (ZMod p) := none) : BusSemantics p where
  isStateful busId :=
    match busMap busId with
    | some t => t.isStateful
    | none => false
  accepts := ApcOptimizer.OpenVM.accepts busMap
  maintainsInvariants := ApcOptimizer.OpenVM.maintainsInvariants busMap
  admissible msgs :=
    (∀ (busId : Nat) (shape : MemoryBusShape), memShapeOf busMap busId = some shape →
      admissibleMemoryBusM shape
        (↑(msgs.filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p))))
    ∧ (∀ (busId tsField : Nat), memTsFieldOf busMap busId = some tsField →
        tsBounded tsField (2 ^ 29) (msgs.filter (fun m => m.busId = busId)))
    ∧ (∀ (busId slot : Nat) (key : ZMod p) (shape : MemoryBusShape),
        memShapeOf busMap busId = some shape →
        memEntryKeyOf busMap entryPc busId = some (slot, key) →
        entryKeyed shape slot key
          (↑(msgs.filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p))))
    ∧ x0ReturnsZero busMap msgs

/-- Auditor sanity: the whole OpenVM rely is order-free — invariant under reordering the
    interaction list. This is what the positional `admissibleMemoryBus` fails. -/
theorem openVmAdmissibleOF_perm (busMap : BusMap) (entryPc : Option (ZMod p))
    {msgs msgs' : List (BusInteraction (ZMod p))} (h : msgs.Perm msgs') :
    (openVmBusSemanticsOF p busMap entryPc).admissible msgs ↔
      (openVmBusSemanticsOF p busMap entryPc).admissible msgs' := by
  unfold openVmBusSemanticsOF x0ReturnsZero
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine forall_congr' fun busId => forall_congr' fun shape => imp_congr Iff.rfl ?_
    exact admissibleMemoryBusM_perm shape (h.filter _)
  · refine forall_congr' fun busId => forall_congr' fun tsField => imp_congr Iff.rfl ?_
    exact tsBounded_perm tsField (2 ^ 29) (h.filter _)
  · refine forall_congr' fun busId => forall_congr' fun slot => forall_congr' fun key =>
      forall_congr' fun shape => imp_congr Iff.rfl (imp_congr Iff.rfl ?_)
    exact entryKeyed_perm shape slot key (h.filter _)
  · exact forall_congr' fun m => imp_congr h.mem_iff Iff.rfl

end ApcOptimizer.OpenVM.OrderFree
