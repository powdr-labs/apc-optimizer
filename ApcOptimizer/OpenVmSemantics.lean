import ApcOptimizer.Spec
import ApcOptimizer.MemoryBus

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- The OpenVM bus types that appear in the default bus map. -/
inductive OpenVmBusType where
  /-- An instruction should receive a `(pc, timestamp)` and send updated values to the bus. -/
  | executionBridge
  /-- To access a memory cell, instructions should:
      1. Receive a `(address_space, pointer, data... (4 bytes), prev_timestamp)` tuple
      2. Send a `(address_space, pointer, data... (4 bytes), current_timestamp)` tuple. -/
  | memory
  /-- Lookup to get the instruction flags from the current pc. Format: `(pc, flags...)` -/
  | pcLookup
  /-- Check that a value is in a certain range. Format: `(value, bits)` -/
  | variableRangeChecker
  /-- Check that a value is in a certain range. Format: `(x, y, z, op)` where `op` is either
      0 (range check) or 1 (xor). The bus checks that `x` and `y` are bytes, and either
      `op = 0 ∧ z = 0` (range check) or `op = 1 ∧ z = x ^ y` (xor). -/
  | bitwiseLookup
  /-- Check that a tuple of two values is in a certain range. Format: `(x, y)` where
      `x < size1` and `y < size2`. -/
  | tupleRangeChecker (size1 size2 : Nat)
  deriving Repr, DecidableEq

/-- A mapping from bus IDs to bus type. -/
abbrev BusMap := Nat → Option OpenVmBusType

/-- A concrete bus map as parsed from a powdr export's `bus_map.bus_ids` field:
    an association list bus id ↦ bus type. -/
abbrev BusMapList := List (Nat × OpenVmBusType)

/-- Convert a `BusMapList` to a `BusMap` lookup function. -/
def BusMapList.toBusMap (busMap : BusMapList) : BusMap :=
  fun busId => busMap.lookup busId

/-- The hard-coded default OpenVM bus map, mirroring powdr's `default_openvm_bus_map`. -/
def defaultBusMap : BusMap
  | 0 => some .executionBridge
  | 1 => some .memory
  | 2 => some .pcLookup
  | 3 => some .variableRangeChecker
  | 6 => some .bitwiseLookup
  | 7 => some (.tupleRangeChecker 256 2048)
  | _ => none

/-- Stateful buses are the execution bridge and memory; the rest are stateless lookups. -/
def OpenVmBusType.isStateful : OpenVmBusType → Bool
  | .executionBridge => true
  | .memory => true
  | .pcLookup => false
  | .variableRangeChecker => false
  | .bitwiseLookup => false
  | .tupleRangeChecker _ _ => false

/-- Whether a field element is a byte (`0 ≤ x < 256`). -/
def isByte (x : ZMod p) : Prop := x.val < 256

/-- The named fields of an OpenVM memory payload,
    `(address_space, pointer, data… (4 limbs), timestamp)`. -/
structure MemoryPayload (p : ℕ) where
  /-- `1` = registers, `2` = main memory. -/
  addressSpace : ZMod p
  /-- The cell's address within its address space. -/
  pointer : ZMod p
  /-- The four limbs of the memory word. -/
  data : Vector (ZMod p) 4

/-- Read a memory payload's named fields; `none` if it is too short to be one. -/
def memoryPayload? : List (ZMod p) → Option (MemoryPayload p)
  | addressSpace :: pointer :: d0 :: d1 :: d2 :: d3 :: _timestamp =>
      some { addressSpace := addressSpace, pointer := pointer, data := #v[d0, d1, d2, d3] }
  | _ => none

/-- Whether the address space is one whose words OpenVM byte-range-checks: registers (`1`) or main
    memory (`2`). -/
def MemoryPayload.isByteChecked (f : MemoryPayload p) : Prop :=
  f.addressSpace.val = 1 ∨ f.addressSpace.val = 2

/-- For lookups, whether the message is in the lookup table. -/
def accepts (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Prop :=
  match busMap msg.busId, msg.payload with
  -- ISSUE:
  -- The PC lookup is a bit special: We would have to know the program to
  -- check whether the PC lookup is valid. So this semantics is **wrong**,
  -- and in theory, the optimizer could add failing PC lookups, losing
  -- completeness.
  -- However, the input circuit already has constraints fixing all of the
  -- lookup fields to constants (added here: [1]), so the optimizer would
  -- not be able to change any of the flags.
  -- Also, the completeness issue could be solved by checking that the
  -- optimized circuit does not contain any PC lookups (they can always
  -- be removed in practice).
  -- [1] https://github.com/powdr-labs/powdr/blob/f94a24f19249af67efbea92ff9c3db6e3e50e7fd/autoprecompiles/src/symbolic_machine_generator.rs#L185-L192
  | some .pcLookup, args => args.length = 9

  | some .bitwiseLookup, [x, y, z, op] =>
    match op.val with
    -- Op 0 range-checks `x` and `y` to be bytes and forces `z = 0`.
    | 0 => isByte x ∧ isByte y ∧ z.val = 0
    -- Op 1 also fixes `z = x ^ y`.
    | 1 => isByte x ∧ isByte y ∧ z.val = Nat.xor x.val y.val
    -- No other op is in the table.
    | _ => False

  | some .variableRangeChecker, [x, bits] =>
    -- `x < 2^bits`, at a width the checker supports: OpenVM's variable range checker rejects any
    -- lookup of more than 17 bits.
    -- TODO: The maximum number of bits is configurable, but the default is 17 and the
    -- OpenVM chips assume that it is at least 17, so we're being conservative here.
    bits.val ≤ 17 ∧ x.val < 2 ^ bits.val

  | some (.tupleRangeChecker s1 s2), [x, y] => x.val < s1 ∧ y.val < s2

  -- For lookups, an unexpected number of arguments is in no table.
  | some .bitwiseLookup, _ => False
  | some .variableRangeChecker, _ => False
  | some (.tupleRangeChecker _ _), _ => False

  -- Stateful buses have no table to contradict.
  | some .executionBridge, _ => True

  -- In OpenVM, the invariant is that only range-checked values are sent to
  -- the register & memory address spaces.
  | some .memory, payload =>
    match memoryPayload? payload with
    | some f => msg.multiplicity = -1 → f.isByteChecked → ∀ d ∈ f.data, isByte d
    | none => True

  -- Invalid bus ID. Won't have a matching receive.
  | none, _ => False

/-- Whether a message maintains the invariants on which soundness depends. Only called
   for messages with nonzero multiplicity. -/
def maintainsInvariants (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Prop :=
  match busMap msg.busId with
  -- Lookups are only ever sent (multiplicity 1).
  | some .pcLookup | some .variableRangeChecker | some .bitwiseLookup
  | some (.tupleRangeChecker _ _) =>
    msg.multiplicity = 1
  -- The execution bridge is stateful: it is sent (1) or received (-1).
  | some .executionBridge =>
    msg.multiplicity = 1 ∨ msg.multiplicity = -1
  -- Memory is stateful (multiplicity 1 or -1), and additionally maintains the invariant
  -- that data limbs written to the register / main-memory address spaces (1 and 2) are
  -- byte-range.
  | some .memory =>
    (msg.multiplicity = 1 ∨ msg.multiplicity = -1) ∧
      (match memoryPayload? msg.payload with
        | some f => f.isByteChecked → ∀ d ∈ f.data, isByte d
        | none => True)
  -- Circuits should not send messages to an unknown bus.
  | none => False

/-- Assume that x0 always returns 0. This should be enforced globally by all OpenVM chips. -/
def x0ReturnsZero (busMap : BusMap) (msgs : List (BusInteraction (ZMod p))) : Prop :=
  ∀ m ∈ msgs, busMap m.busId = some .memory →
    -- If address space is 1 (registers), and address is 0 (x0), then the value must be 0.
    m.payload[0]? = some 1 → m.payload[1]? = some 0 →
      m.payload[2]? = some 0 ∧ m.payload[3]? = some 0 ∧
        m.payload[4]? = some 0 ∧ m.payload[5]? = some 0

/-- Maps a bus ID to its memory bus shape, if applicable. -/
def memShapeOf (busMap : BusMap) (busId : Nat) : Option MemoryBusShape :=
  match busMap busId with
  -- The *actual* memory bus, with address (address space, pointer) in payload slots 0 and 1.
  | some .memory => some { addressFields := [0, 1], direction := .receiveThenSend }
  -- The execution bridge can also be viewed as a memory bus with a single global cell (address `[]`).
  -- Note that in this bus, the memory discipline (for any consecutive send/receive pair, the values
  -- must match) is *not* enforced by the bus itself. By adding the execution bridge here, we make
  -- completeness partial: we assume the prover will always *choose* to prove consecutive cycles.
  | some .executionBridge => some { addressFields := [], direction := .receiveThenSend }
  | _ => none

/-- The payload slot carrying the timestamp on a declared memory-shaped bus: slot 6 on the memory
    bus (`(address_space, pointer, data… (4 limbs), timestamp)`) and slot 1 on the execution
    bridge (`(pc, timestamp)`). -/
def memTsFieldOf (busMap : BusMap) (busId : Nat) : Option Nat :=
  match busMap busId with
  | some .memory => some 6
  | some .executionBridge => some 1
  | _ => none

/-- The entry-record designation on a chain-shaped bus (ENTRY_KEY, `ApcOptimizer/MemoryBus.lean`):
    the execution bridge's record entering the block from outside carries the block's entry pc in
    payload slot `0`, since the block is entered at its first instruction. `none` — hence no
    assumption — where the optimizer was not told the block's entry pc, and on every other bus. -/
def memEntryKeyOf (busMap : BusMap) (entryPc : Option (ZMod p)) (busId : Nat) :
    Option (Nat × ZMod p) :=
  match busMap busId, entryPc with
  | some .executionBridge, some pc => some (0, pc)
  | _, _ => none

/-- The OpenVM bus semantics for a given bus map (default: the hard-coded default bus map) and, if
    the optimizer was told it, the block's entry pc (see `memEntryKeyOf`). -/
def openVmBusSemantics (p : ℕ) (busMap : BusMap := defaultBusMap)
    (entryPc : Option (ZMod p) := none) :
    BusSemantics p where
  isStateful busId :=
    match busMap busId with
    | some t => t.isStateful
    | none => false
  accepts := accepts busMap
  maintainsInvariants := maintainsInvariants busMap
  -- Four conjuncts: the order-free memory discipline per declared bus; the timestamp bound
  -- (TS_BOUND — OpenVM's global timestamp argument keeps every timestamp below `2^29` across
  -- the whole trace); the entry-record designation on a chain bus (ENTRY_KEY, vacuous unless the
  -- block's entry pc was supplied); and the x0-returns-zero rely.
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

/-- Auditor sanity: the whole OpenVM rely (`openVmBusSemantics.admissible`) is order-free — it is
    invariant under reordering the interaction list. -/
theorem openVmAdmissible_perm (busMap : BusMap) (entryPc : Option (ZMod p))
    {msgs msgs' : List (BusInteraction (ZMod p))} (h : msgs.Perm msgs') :
    (openVmBusSemantics p busMap entryPc).admissible msgs ↔
      (openVmBusSemantics p busMap entryPc).admissible msgs' := by
  unfold openVmBusSemantics x0ReturnsZero
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine forall_congr' fun busId => forall_congr' fun shape => imp_congr Iff.rfl ?_
    exact admissibleMemoryBusM_perm shape (h.filter _)
  · refine forall_congr' fun busId => forall_congr' fun tsField => imp_congr Iff.rfl ?_
    exact tsBounded_perm tsField (2 ^ 29) (h.filter _)
  · refine forall_congr' fun busId => forall_congr' fun slot => forall_congr' fun key =>
      forall_congr' fun shape => imp_congr Iff.rfl (imp_congr Iff.rfl ?_)
    exact entryKeyed_perm shape slot key (h.filter _)
  · exact forall_congr' fun m => imp_congr h.mem_iff Iff.rfl

/-- OpenVM's proving-backend degree bound (powdr's `DEFAULT_DEGREE_BOUND`), used when the optimizer
    is run directly rather than with a bound passed in over the FFI. -/
def defaultDegreeBound : DegreeBound := { identities := 3, busInteractions := 2 }

/-- The BabyBear field modulus, `2^31 - 2^27 + 1` — the field all powdr OpenVM exports use. -/
def babyBear : Nat := 2013265921

instance : NeZero babyBear := ⟨by decide⟩

end ApcOptimizer.OpenVM
