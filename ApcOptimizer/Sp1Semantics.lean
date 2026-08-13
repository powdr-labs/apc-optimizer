import ApcOptimizer.Spec
import ApcOptimizer.MemoryBus

set_option autoImplicit false

namespace ApcOptimizer.SP1

variable {p : ℕ}

/-- The SP1 bus types that appear in the default bus map. -/
inductive Sp1BusType where
  /-- The CPU state ("execution bridge"): an instruction receives the current `(clk, pc)` and
      sends the next one. Payload: `(clk... (2 fields), pc... (3 fields))`. -/
  | executionBridge
  /-- To access a memory cell, instructions send the previous record and receive the new one.
      Payload: `(clk... (2 fields), address... (3 limbs), data... (4 × 16-bit limbs))`. -/
  | memory
  /-- Program lookup: fetch the instruction at the current pc. Payload has 16 fields. -/
  | pcLookup
  /-- Byte lookup. Format `(op, a, b, c)`, where `op` selects the operation on bytes `b`, `c`:
      0 `AND` (`a = b & c`), 1 `OR`, 2 `XOR`, 3 `U8Range` (`a = 0`), 4 `LTU` (`a = [b < c]`),
      5 `MSB` (`a = b >> 7`, `c = 0`), 6 `Range` (`a < 2^b`, `c = 0`, `b ≤ 16`). -/
  | byteLookup
  /-- Instruction-fetch lookup (the untrusted instruction table). Payload has 22 fields. -/
  | instructionFetch
  /-- Page-protection lookup. Payload has 6 fields. -/
  | pageProt
  deriving Repr, DecidableEq

/-- A mapping from bus IDs to bus type. -/
abbrev BusMap := Nat → Option Sp1BusType

/-- A concrete bus map as parsed from a powdr export's `bus_map.bus_ids` field:
    an association list bus id ↦ bus type. -/
abbrev BusMapList := List (Nat × Sp1BusType)

/-- Convert a `BusMapList` to a `BusMap` lookup function. -/
def BusMapList.toBusMap (busMap : BusMapList) : BusMap :=
  fun busId => busMap.lookup busId

/-- The hard-coded default SP1 bus map, mirroring powdr's `sp1_bus_map`. -/
def defaultBusMap : BusMap
  | 1 => some .memory
  | 2 => some .pcLookup
  | 5 => some .byteLookup
  | 7 => some .executionBridge
  | 16 => some .instructionFetch
  | 18 => some .pageProt
  | _ => none

/-- Stateful buses are the execution bridge and memory; the rest are stateless lookups. -/
def Sp1BusType.isStateful : Sp1BusType → Bool
  | .executionBridge => true
  | .memory => true
  | .pcLookup => false
  | .byteLookup => false
  | .instructionFetch => false
  | .pageProt => false

/-- Whether a field element is a byte (`0 ≤ x < 256`). -/
def isByte (x : ZMod p) : Prop := x.val < 256

/-- Whether a field element is a 16-bit limb (`0 ≤ x < 2^16`). -/
def is16Bit (x : ZMod p) : Prop := x.val < 2 ^ 16

/-- The named fields of an SP1 memory payload,
    `(clk… (2 fields), address… (3 limbs), data… (4 × 16-bit limbs))`. -/
structure MemoryPayload (p : ℕ) where
  /-- The two clock fields. -/
  clk : Vector (ZMod p) 2
  /-- The three address limbs. -/
  address : Vector (ZMod p) 3
  /-- The four limbs of the memory word. -/
  data : Vector (ZMod p) 4

/-- Read a memory payload's named fields; `none` if the number of entries is wrong. -/
def memoryPayload? : List (ZMod p) → Option (MemoryPayload p)
  | c0 :: c1 :: a0 :: a1 :: a2 :: d0 :: d1 :: d2 :: d3 :: _ =>
      some { clk := #v[c0, c1], address := #v[a0, a1, a2], data := #v[d0, d1, d2, d3] }
  | _ => none

/-- For lookups, whether the message is in the lookup table. -/
def accepts (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Prop :=
  match busMap msg.busId, msg.payload with
  -- As for OpenVM's PC lookup, we only check the arity of these lookups: the input circuit has
  -- already fixed the looked-up fields to constants, so the optimizer cannot change them.
  | some .pcLookup, args => args.length = 16
  | some .instructionFetch, args => args.length = 22
  | some .pageProt, args => args.length = 6

  | some .byteLookup, [op, a, b, c] =>
    match op.val with
    -- AND: `b`, `c` are bytes and `a = b & c`.
    | 0 => isByte b ∧ isByte c ∧ a.val = Nat.land b.val c.val
    -- OR: `a = b | c`.
    | 1 => isByte b ∧ isByte c ∧ a.val = Nat.lor b.val c.val
    -- XOR: `a = b ^ c`.
    | 2 => isByte b ∧ isByte c ∧ a.val = Nat.xor b.val c.val
    -- U8Range: `b`, `c` are bytes and `a = 0`.
    | 3 => isByte b ∧ isByte c ∧ a.val = 0
    -- LTU: `a` is 1 if `b < c`, else 0.
    | 4 => isByte b ∧ isByte c ∧ a.val = if b.val < c.val then 1 else 0
    -- MSB: `a` is the top bit of the byte `b`, and `c = 0`.
    | 5 => isByte b ∧ c.val = 0 ∧ a.val = b.val >>> 7
    -- Range: `a < 2^b` with `c = 0` and `b ≤ 16` (the largest width the table holds).
    | 6 => b.val ≤ 16 ∧ c.val = 0 ∧ a.val < 2 ^ b.val
    -- No other op is in the table.
    | _ => False
  | some .byteLookup, _ => False

  -- Stateful buses have no table to contradict.
  | some .executionBridge, _ => True

  -- In SP1, the invariant is that memory data limbs are 16-bit range-checked. A *send*
  -- (multiplicity 1) reads the previous record, so its data must be 16-bit.
  | some .memory, payload =>
    match memoryPayload? payload with
    | some f => msg.multiplicity = 1 → ∀ d ∈ f.data, is16Bit d
    | none => True

  -- Invalid bus ID. Won't have a matching receive.
  | none, _ => False

/-- Whether a message maintains the invariants on which soundness depends. Only called
    for messages with nonzero multiplicity. -/
def maintainsInvariants (busMap : BusMap) (msg : BusInteraction (ZMod p)) : Prop :=
  match busMap msg.busId with
  -- Lookups are only ever sent (multiplicity 1).
  | some .pcLookup | some .byteLookup | some .instructionFetch | some .pageProt =>
    msg.multiplicity = 1
  -- The execution bridge is stateful: it is sent (1) or received (-1).
  | some .executionBridge =>
    msg.multiplicity = 1 ∨ msg.multiplicity = -1
  -- Memory is stateful (multiplicity 1 or -1), and additionally maintains the invariant that its
  -- data limbs are 16-bit range.
  | some .memory =>
    (msg.multiplicity = 1 ∨ msg.multiplicity = -1) ∧
      (match memoryPayload? msg.payload with
        | some f => ∀ d ∈ f.data, is16Bit d
        | none => True)
  -- Circuits should not send messages to an unknown bus.
  | none => False

/-- Assume that reading register `x0` (address `0`) always returns `0`. This should be enforced
    globally by all SP1 chips. -/
def x0ReturnsZero (busMap : BusMap) (msgs : List (BusInteraction (ZMod p))) : Prop :=
  ∀ m ∈ msgs, busMap m.busId = some .memory →
    -- If all three address limbs are 0 (register x0), then the four data limbs must be 0.
    m.payload[2]? = some 0 → m.payload[3]? = some 0 → m.payload[4]? = some 0 →
      m.payload[5]? = some 0 ∧ m.payload[6]? = some 0 ∧
        m.payload[7]? = some 0 ∧ m.payload[8]? = some 0

/-- Maps a bus ID to its memory bus shape, if applicable. For SP1 *memory*, the `getPrevious` sends
    the previous record and the `setNew` receives the new one, so `direction := .sendThenReceive`
    (`setNewMult = -1`) — the reverse of OpenVM. The *execution bridge* is different: like every VM's,
    an instruction sends the next CPU state and receives the current one, so its `setNew` (the next
    state) is the send — `direction := .receiveThenSend` (`setNewMult = 1`), matching OpenVM's
    execution bridge and OpenVM memory, *not* SP1 memory. -/
def memShapeOf (busMap : BusMap) (busId : Nat) : Option MemoryBusShape :=
  match busMap busId with
  -- The *actual* memory bus, with the three address limbs in payload slots 2, 3 and 4.
  | some .memory => some { addressFields := [2, 3, 4], direction := .sendThenReceive }
  -- The execution bridge is a single-global-cell (address `[]`) memory bus that sends the *next*
  -- CPU state. As in OpenVM, this makes completeness partial: we assume the prover always proves
  -- consecutive cycles.
  | some .executionBridge => some { addressFields := [], direction := .receiveThenSend }
  | _ => none

/-- The payload slot carrying the *low clock limb* on a declared memory-shaped bus, with the bound
    TS_BOUND asserts on its value (`tsBounded`, `ApcOptimizer/MemoryBus.lean`).

    SP1 has no single timestamp field: its clock is the *pair* `(clk_high, clk_low)` (payload
    slots 0 and 1 on both memory and the execution bridge), split at bit 24, and clock order is
    lexicographic on the pair. Within one autoprecompile block, however, `clk_high` is a *single
    shared expression*: instruction chips pass it through untouched, and a block that would need a
    high-limb carry (a `StateBumpChip` row) is never formed as an APC. So within the block, clock
    order is carried entirely by `clk_low`, and bounding that slot is exactly what lets the
    optimizer recover integer order from it — the SP1 analogue of OpenVM's TS_BOUND, with a local
    24-bit bound in place of a global `2^29` one.

    The declared bounds:
    - *memory* (slot 1, `< 2^24`): every record's `clk_low` is the low 24 bits of a real access
      timestamp — the executor splits the clock at bit 24, and in-block current-access timestamps
      stay below `2^24` because each instruction's received CPU state is range-checked canonical
      and its accesses add at most the sub-slot offsets.
    - *execution bridge* (slot 1, `< 2^25`): every *received* state is range-checked canonical
      (`< 2^24`) by the receiving instruction. The block's final *sent* state is checked by no
      in-block chip and may be non-canonical — the carry state a `StateBumpChip` row after the
      block repairs — but it exceeds `2^24` by less than one instruction's clock increment, which
      SP1 itself assumes to be at most `2^24` (the `StateBumpChip` `is_clk` booleanity argument). -/
def memTsFieldOf (busMap : BusMap) (busId : Nat) : Option (Nat × Nat) :=
  match busMap busId with
  | some .memory => some (1, 2 ^ 24)
  | some .executionBridge => some (1, 2 ^ 25)
  | _ => none

/-- The entry-record designation on a chain-shaped bus (ENTRY_KEY, `ApcOptimizer/MemoryBus.lean`):
    the execution bridge's record entering the block from outside carries the block's entry pc,
    since the block is entered at its first instruction. SP1 carries the pc as *limbs*
    `[pc mod 2^16, pc / 2^16, …]` in payload slots 2–4, so the designation is on slot 2 with the
    entry pc's low limb — weaker than the full pc, but enough to separate the entry record from
    the block's interior records, whose pcs step by 4. `none` — hence no assumption — where the
    optimizer was not told the block's entry pc, and on every other bus. -/
def memEntryKeyOf (busMap : BusMap) (entryPc : Option Nat) (busId : Nat) :
    Option (Nat × ZMod p) :=
  match busMap busId, entryPc with
  | some .executionBridge, some pc => some (2, ((pc % 2 ^ 16 : Nat) : ZMod p))
  | _, _ => none

/-- The SP1 bus semantics for a given bus map (default: the hard-coded default bus map) and, if
    the optimizer was told it, the block's entry pc (see `memEntryKeyOf`). -/
def sp1BusSemantics (p : ℕ) (busMap : BusMap := defaultBusMap)
    (entryPc : Option Nat := none) :
    BusSemantics p where
  isStateful busId :=
    match busMap busId with
    | some t => t.isStateful
    | none => false
  accepts := accepts busMap
  maintainsInvariants := maintainsInvariants busMap
  -- Four conjuncts: the order-free memory discipline per declared bus (on SP1 *memory* the
  -- `setNew` multiplicity is `-1`, `direction := .sendThenReceive`; on the *execution bridge* it
  -- is `1`, `.receiveThenSend` — either way `admissibleMemoryBusM` bounds, per evaluated address,
  -- the excess of the `getPrevious` payload multiset over the `setNew` one); the low-clock-limb
  -- bound (TS_BOUND on `clk_low` — sound within one APC block because `clk_high` is a single
  -- shared expression there, see `memTsFieldOf`); the entry-record designation on the chain bus
  -- (ENTRY_KEY, vacuous unless the block's entry pc was supplied); and the x0-returns-zero rely.
  admissible msgs :=
    (∀ (busId : Nat) (shape : MemoryBusShape), memShapeOf busMap busId = some shape →
      admissibleMemoryBusM shape
        (↑(msgs.filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p))))
    ∧ (∀ (busId slot bound : Nat), memTsFieldOf busMap busId = some (slot, bound) →
        tsBounded slot bound (msgs.filter (fun m => m.busId = busId)))
    ∧ (∀ (busId slot : Nat) (key : ZMod p) (shape : MemoryBusShape),
        memShapeOf busMap busId = some shape →
        memEntryKeyOf busMap entryPc busId = some (slot, key) →
        entryKeyed shape slot key
          (↑(msgs.filter (fun m => m.busId = busId)) : Multiset (BusInteraction (ZMod p))))
    ∧ x0ReturnsZero busMap msgs

/-- Auditor sanity: the whole SP1 rely (`sp1BusSemantics.admissible`) is order-free — it is
    invariant under reordering the interaction list. -/
theorem sp1Admissible_perm (busMap : BusMap) (entryPc : Option Nat)
    {msgs msgs' : List (BusInteraction (ZMod p))} (h : msgs.Perm msgs') :
    (sp1BusSemantics p busMap entryPc).admissible msgs ↔
      (sp1BusSemantics p busMap entryPc).admissible msgs' := by
  unfold sp1BusSemantics x0ReturnsZero
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine forall_congr' fun busId => forall_congr' fun shape => imp_congr Iff.rfl ?_
    exact admissibleMemoryBusM_perm shape (h.filter _)
  · refine forall_congr' fun busId => forall_congr' fun slot => forall_congr' fun bound =>
      imp_congr Iff.rfl ?_
    exact tsBounded_perm slot bound (h.filter _)
  · refine forall_congr' fun busId => forall_congr' fun slot => forall_congr' fun key =>
      forall_congr' fun shape => imp_congr Iff.rfl (imp_congr Iff.rfl ?_)
    exact entryKeyed_perm shape slot key (h.filter _)
  · exact forall_congr' fun m => imp_congr h.mem_iff Iff.rfl

/-- SP1's proving-backend degree bound (powdr's `DEFAULT_DEGREE_BOUND` for SP1), used when the
    optimizer is run directly rather than with a bound passed in over the FFI. -/
def defaultDegreeBound : DegreeBound := { identities := 3, busInteractions := 1 }

/-- The KoalaBear field modulus, `2^31 - 2^24 + 1` — the field all powdr SP1 exports use. -/
def koalaBear : Nat := 2130706433

instance : NeZero koalaBear := ⟨by decide⟩

end ApcOptimizer.SP1
