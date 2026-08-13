import ApcOptimizer.Spec

set_option autoImplicit false

/-! Helper definitions to encode the semantics of memory buses, used to implement
    `BusSemantics.admissible`. Memory buses are stateful: bus interactions come in
    `getPrevious`/`setNew` pairs — a `setNew` commits a cell's value, and the access reading it
    back issues a same-address `getPrevious` with the same payload (address, timestamp and
    value). Both memory reads and memory writes are such a `getPrevious`/`setNew` pair (a read
    additionally constrains the two values to agree).

    The primary discipline is the order-free `admissibleMemoryBusM`: a property of the *multiset*
    of evaluated messages, assuming nothing about the order of the interaction list
    (`admissibleMemoryBusM_perm`). Per evaluated address it asserts the multiset shadow of two
    system-level facts:

    1. **Bus balance** — a received record is a sent record: matched receives consume send
       payload tuples injectively (the defining property of the global bus argument, e.g. [1]).
    2. **Window atomicity** — per address, at most one record enters the block from outside (the
       entry receive); every other receive consumes an in-block send.

    Together: at every address, the receives' payload multiset exceeds the sends' by at most one
    element. Grouping is by *evaluated* address, so the statement is independent of how symbolic
    addresses alias.

    The positional `admissibleMemoryBus` remains temporarily: it additionally trusts that the
    interaction list is *ordered by time* and asserts payload copying between list-adjacent
    same-address pairs. It is recoverable from the order-free discipline as a theorem on the
    canonical access order (`Implementation/MemoryBusMultiset.lean`,
    `interleaveAccesses_admissibleMemoryBus_of_M`).

    A separate per-message rely, `tsBounded` (TS_BOUND), bounds the value of a declared timestamp
    payload slot; combined with the order-free discipline it lets a pass recover timestamp *order*
    from the bounded values without trusting the list order.

    A third rely, `entryKeyed` (ENTRY_KEY), *designates* the record entering the block from outside
    on a chain bus: it carries a known key (for an execution bridge, the block's entry pc). It
    strengthens window atomicity, which only counts the entering record without saying which one it
    is — see `entryKeyed` for why the multiset data alone cannot say.

    [1] https://link.springer.com/article/10.1007/BF01185212
-/

variable {p : ℕ}

/-- A memory access is a `getPrevious` (reading the cell's current value) followed by a `setNew`
    (committing its next value); the two carry opposite multiplicities. The variant is named for
    that order — `⟨getPrevious's operation⟩Then⟨setNew's operation⟩` — which fixes which is the
    *send* (multiplicity `1`) and which the *receive* (`-1`). -/
inductive MemoryBusDirection where
  /-- `getPrevious` receives (`-1`), `setNew` sends (`1`) — so `setNewMult = 1`. This is OpenVM's
      memory convention (send the new record, receive the previous), and every VM's execution
      bridge, which sends the next CPU state and receives the current one. -/
  | receiveThenSend
  /-- `getPrevious` sends (`1`), `setNew` receives (`-1`) — so `setNewMult = -1`. This is SP1's
      memory convention (it sends the previous record and receives the new one). -/
  | sendThenReceive
  deriving Repr, DecidableEq

/-- A description of a memory bus interaction. -/
structure MemoryBusShape where
  /-- Payload positions forming the access key (e.g. OpenVM's two-limb address).
      Can be empty for a single global cell. -/
  addressFields : List Nat
  /-- Which of the matched consecutive `setNew`/`getPrevious` pair is the send and which the
      receive (see `MemoryBusDirection`). -/
  direction : MemoryBusDirection

/-- The multiplicity a `setNew` carries on this bus (`1` for `receiveThenSend`, `-1` for
    `sendThenReceive`); the `getPrevious` reading it back carries the negation. -/
def MemoryBusShape.setNewMult (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => 1
  | .sendThenReceive => -1

/-- The address projection of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.address (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressFields.map (fun (slot : Nat) => m.payload[slot]?)

/-- Given an ordered list of memory bus interaction messages *on the same bus*, decide whether
    it follows the memory bus discipline: after a `setNew` to a given address (multiplicity
    `shape.setNewMult`), the next `getPrevious` from the same address (multiplicity
    `-shape.setNewMult`) observes the same payload, with no intervening active messages to the same
    address. -/
def admissibleMemoryBus (shape : MemoryBusShape) (L : List (BusInteraction (ZMod p))) : Prop :=
  ∀ (pre mid post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
    L = pre ++ S :: mid ++ R :: post →
    S.multiplicity = shape.setNewMult → R.multiplicity = -shape.setNewMult →
    shape.address S = shape.address R →
    (∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = shape.address S → False) →
    S.payload = R.payload

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
