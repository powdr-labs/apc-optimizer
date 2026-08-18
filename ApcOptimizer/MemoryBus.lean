import ApcOptimizer.Spec

set_option autoImplicit false

/-! Helper definitions to encode the semantics of memory buses, used to implement
    `BusSemantics.admissible`. Memory buses are stateful: bus interactions come in
    `getPrevious`/`setNew` pairs — a `setNew` commits a cell's value, and the access reading it
    back issues a same-address `getPrevious` with the same payload (address, timestamp and value).
    Both memory reads and memory writes are such a pair (a read additionally constrains the two
    values to agree).

    `admissibleMemoryBusM` just *asserts* that this discipline holds, per evaluated address and on
    the net bus state alone: the messages balance, except for at most one record entering the block
    from outside and one left behind for later (bus balance, e.g. [1], plus window atomicity). It
    assumes nothing about the order of the interaction list. `tsBounded` (TS_BOUND) and `entryKeyed`
    (ENTRY_KEY) are two further per-bus relies; `MemoryBusShape.rely` bundles the three, and a VM's
    `admissible` states it once per declared bus.

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
  /-- The timestamp payload slot and the bound TS_BOUND asserts on its value (see `tsBounded`), or
      `none` where the bus declares no bounded timestamp. -/
  tsField : Option (Nat × Nat) := none
  /-- The payload slot designating the entering record and the key it carries (see `entryKeyed`),
      or `none` where it is not designated. A `Nat` key, cast into the field, keeps the shape
      independent of the modulus. -/
  entryKey : Option (Nat × Nat) := none

/-- The multiplicity a `setNew` carries on this bus (`1` for `receiveThenSend`, `-1` for
    `sendThenReceive`); the `getPrevious` reading it back carries the negation. -/
def MemoryBusShape.setNewMult (shape : MemoryBusShape) : ZMod p :=
  match shape.direction with
  | .receiveThenSend => 1
  | .sendThenReceive => -1

/-- The address projection of an evaluated payload, per a memory-bus shape. -/
def MemoryBusShape.addressOf (shape : MemoryBusShape) (payload : List (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressFields.map (fun (slot : Nat) => payload[slot]?)

/-- The address projection of an evaluated message, per a memory-bus shape. -/
def MemoryBusShape.address (shape : MemoryBusShape) (m : BusInteraction (ZMod p)) :
    List (Option (ZMod p)) :=
  shape.addressOf m.payload

def busState (M : List (BusInteraction (ZMod p))) : BusState p := fun message =>
  M.filter (fun m => (m.busId, m.payload) = message) |>.map BusInteraction.multiplicity |>.sum

/-- The order-free memory discipline on one bus's messages, on the net bus state (`busState`: the
    multiplicity each message is sent with, summed). The field-valued state stands for the message
    *counts* only because of the two side conditions below: every multiplicity is `±setNewMult`, and
    the message count stays below `p`. -/
def admissibleMemoryBusM (shape : MemoryBusShape) (M : List (BusInteraction (ZMod p))) : Prop :=
  (∀ m ∈ M, m.multiplicity = shape.setNewMult ∨ m.multiplicity = -shape.setNewMult) ∧
  M.length + 1 < p ∧
  ∀ addr : List (Option (ZMod p)),
    -- The bus state, restricted to the messages at the current address
    let state := busState (M.filter (fun m => shape.address m = addr))
    -- Case 1: everything balances (no entry or exit)
    state = (fun _ => 0) ∨
    -- Case 2: exactly one record enters and one exits
    ∃ entryRecord exitRecord : BusMessage p,
      state = fun message =>
        if message = entryRecord then -shape.setNewMult
        else if message = exitRecord then shape.setNewMult
        else 0

/-- ENTRY_KEY: every record entering the block from outside — a message the block leaves as an
    unmatched *receive*, i.e. at net state `-setNewMult` — carries `key` in payload slot `slot`.

    For a chain bus (an execution bridge), window atomicity already says *one* record enters; this
    says it is the block's entry record, at the entry pc the optimizer is told. A rotated filling of
    the block (entered at an interior instruction, wrapping through the exit) leaves the same net
    state with a different entering record, so it takes an assumption to exclude (see the README's
    assumptions). -/
def entryKeyed (shape : MemoryBusShape) (slot : Nat) (key : ZMod p)
    (M : List (BusInteraction (ZMod p))) : Prop :=
  ∀ (busId : Nat) (payload : List (ZMod p)),
    busState M (busId, payload) = -shape.setNewMult → payload[slot]? = some key

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

/-- The whole rely a memory-shaped bus carries: the order-free discipline, plus the TS_BOUND and
    ENTRY_KEY assumptions the shape declares (nothing where it declares none). A VM's
    `BusSemantics.admissible` states this once per declared bus. -/
def MemoryBusShape.rely (shape : MemoryBusShape) (M : List (BusInteraction (ZMod p))) : Prop :=
  admissibleMemoryBusM shape M ∧
  (∀ slot bound : Nat, shape.tsField = some (slot, bound) → tsBounded slot bound M) ∧
  (∀ slot key : Nat, shape.entryKey = some (slot, key) → entryKeyed shape slot (key : ZMod p) M)
