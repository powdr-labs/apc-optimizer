import ApcOptimizer.VmSpec.Legal
import ApcOptimizer.VmSpec.Legal
import ApcOptimizer.OpenVmSemantics

set_option autoImplicit false

/-! Draft `HostChip`s for OpenVM, built against `ApcOptimizer.OpenVM`'s bus semantics
    (`OpenVmSemantics.lean`): the four stateless lookup tables, memory
    initialization/finalization, a `HINT_STOREW` input chip (peeks a pointer register, then
    writes one unconstrained word there), and the connector that seeds and terminates the
    execution bridge — assembled into a concrete `openVmHost : Host p` at the bottom.
    `memoryInitHostChip`/`memoryFinalizeHostChip`/`inputHostChip` are the ones with
    `isIo := true`: the VM's externally observable effect is exactly their instances' own net bus
    contributions — the entire memory boundary (all three address spaces, uniformly) plus the
    input stream, with no dedicated output chip. There is no special treatment of address space
    `3`: whatever memory-finalize reads there is as much a moving part of the fixed boundary as
    address spaces `1`/`2`, not a curated "the output".

    Words: a memory word is four byte limbs (`MemoryPayload.data`), a register spread across all
    four as OpenVM stores it (`wordValue`, `InputRead.ptrLimbs`). A *datum* pulled off the input
    stream is a single byte, in the low limb with the rest zeroed — one value per word, not four
    packed together. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- Build a `BusState p` from a list of already-evaluated bus interactions: pointwise, the net
    multiplicity of a message is the sum of multiplicities of list entries carrying it exactly —
    the same rule `Circuit.allEffects`/`VmAssignment.busEffect` use. -/
def busStateOf (messages : List (BusInteraction (ZMod p))) : BusState p :=
  fun message =>
    ((messages.filter (fun m => decide ((m.busId, m.payload) = message))).map
      (fun m => m.multiplicity)).sum

/-- A host chip pinned exactly to one instance of a witness type's own effects. -/
def singletonWitnessChip {W : Type} (effects : W → BusState p) (isIo : Bool := false) :
    HostChip p where
  canProduce contribution := ∃ w : W, contribution = effects w
  instanceBound := 1
  isIo := isIo

/-- `defaultBusMap`'s execution-bridge bus id (its `0 ↦ some .executionBridge` arm) and memory bus
    id (its `1 ↦ some .memory` arm) — the one place this development picks them, so every other
    `0`/`1` below meaning "the exec bus"/"the mem bus" is one of these two. `abbrev`, not `def`, so
    they stay transparent to `simp`/`decide`/unification wherever a proof already expects the bare
    numeral. -/
abbrev openVmExecBusId : Nat := 0

abbrev openVmMemBusId : Nat := 1

/-- A stateless lookup-table host chip for bus `busId`: legal to touch a payload only if it is
    actually in the table (`accept`), illegal on any other bus.

    One instance per bus (`instanceBound := 1`) loses nothing: the predicate is closed under sums
    and holds of `0`, so one instance's `canProduce` already nets what any number could. -/
def lookupTableHostChip (busId : Nat) (accept : List (ZMod p) → Prop) : HostChip p where
  canProduce contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 → message.1 = busId ∧ accept message.2
  instanceBound := 1
  isIo := false

/-- The PC-lookup host chip (OpenVM's instruction-fetch table, default bus `2`). As faithful as
    `OpenVM.accepts`'s own PC-lookup case, which only checks arity and leaves matching against
    the compiled program's actual instructions unmodeled — see that def's docstring for why. -/
def pcLookupHostChip (busId : Nat := 2) : HostChip p :=
  lookupTableHostChip busId (fun args => args.length = 9)

/-- The bitwise-lookup host chip (default bus `6`): `(x, y, z, op)`, mirroring
    `OpenVM.accepts`. -/
def bitwiseLookupHostChip (busId : Nat := 6) : HostChip p :=
  lookupTableHostChip busId fun
    | [x, y, z, op] =>
      match op.val with
      | 0 => isByte x ∧ isByte y ∧ z.val = 0
      | 1 => isByte x ∧ isByte y ∧ z.val = Nat.xor x.val y.val
      | _ => False
    | _ => False

/-- The variable-range-checker host chip (default bus `3`): `(x, bits)`, mirroring
    `OpenVM.accepts`. -/
def variableRangeCheckerHostChip (busId : Nat := 3) : HostChip p :=
  lookupTableHostChip busId fun
    | [x, bits] => bits.val ≤ 17 ∧ x.val < 2 ^ bits.val
    | _ => False

/-- The tuple-range-checker host chip (default bus `7`, default sizes matching
    `defaultBusMap`): `(x, y)` with `x < size1 ∧ y < size2`, mirroring `OpenVM.accepts`. -/
def tupleRangeCheckerHostChip (busId : Nat := 7) (size1 : Nat := 256) (size2 : Nat := 2048) :
    HostChip p :=
  lookupTableHostChip busId fun
    | [x, y] => x.val < size1 ∧ y.val < size2
    | _ => False

/-- **The initial memory image, required to be a *function* of the address.**

    Whitepaper §4.6.2: the boundary chip "add[s] messages to the send multiset at timestamp 0",
    and "the messages at timestamp 0 … must correspond to the initial memory state"; it "exposes a
    Merkle root of the initial memory state as a public value and constrains the messages at
    timestamp 0 to be consistent with the Merkle root via Merkle proofs".

    A memory state is a function from address to value, and a Merkle root commits to exactly one.
    `memoryInitHostChip` keeps only the per-message shape and drops the correspondence, so it
    admits an image holding two different records for one cell — which is the whole of what makes
    `Audit/AdmissibleGap.lean`'s `badChip` run balance. Since every record here is stamped `0`,
    address injectivity is exactly send-uniqueness at `(address, timestamp)` for this chip.

    The Merkle root itself stays unmodeled (a cross-segment fact, §5.2); this asks only for the
    consequence a single segment's admissibility needs. -/
def memoryInitHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
    (∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = 1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        (∀ d ∈ f.data, isByte d) ∧ message.2[6]? = some 0 ∧
        (f.addressSpace.val = 1 ∨ f.addressSpace.val = 2 ∨ f.addressSpace.val = 3))
    ∧ (∀ m m' : BusMessage p, contribution m ≠ 0 → contribution m' ≠ 0 →
        m.2[0]? = m'.2[0]? → m.2[1]? = m'.2[1]? → m = m')
    -- The initial memory state has `x0 = 0`: RISC-V's hardwired zero register. Without this the
    -- image may seed `(1,0)` with a nonzero word, and `x0ReturnsZero` is then false of any chip
    -- that *reads* `x0` — which `Audit/Apcs/AndBranch` and `Keccak2105000` both do. A chip can
    -- only constrain what it writes (`Circuit.legalGuest`'s `x0Zero`), so the read side has to
    -- come from here.
    ∧ (∀ m : BusMessage p, contribution m ≠ 0 → m.2[0]? = some 1 → m.2[1]? = some 0 →
        m.2[2]? = some 0 ∧ m.2[3]? = some 0 ∧ m.2[4]? = some 0 ∧ m.2[5]? = some 0)
  instanceBound := 1
  isIo := true

/-- The memory-finalization host chip (default bus `1`): the last receive (multiplicity `-1`,
    OpenVM's `getPrevious` polarity) of each touched address, in any address space — registers
    (`1`), main memory (`2`), and (unlike `Implementation/`'s earlier treatment) address space `3`
    alike, since nothing here singles address space `3` out as "the output" any more.

    Unlike memory initialization, no byte fact is asserted here: this chip only receives, so
    whatever it reads is bus-matched to some earlier send whose byte-ness is already established
    elsewhere (the other host chips directly, a guest chip by `maintains_of_stateful_active`'s
    induction) — asserting it again would be redundant. `Host.exemptChip`/
    `openVmHost_finalize_exempt` (`Implementation/OpenVmConnection.lean`) fold this chip into that
    same induction instead, deriving rather than assuming its payload good — the manuscript's
    `eq:legal:recv_byte`, for the one host chip simple enough (one instance, receive-only) to make
    that possible.

    `isIo`: this chip's instances are the other half of the VM's externally observable effect —
    the final memory image, every address space alike. -/
def memoryFinalizeHostChip (memBusId : Nat := openVmMemBusId) : HostChip p where
  canProduce contribution :=
    ∀ message : BusMessage p, contribution message ≠ 0 →
      message.1 = memBusId ∧ contribution message = -1 ∧
      ∃ f : MemoryPayload p, memoryPayload? message.2 = some f ∧
        (f.addressSpace.val = 1 ∨ f.addressSpace.val = 2 ∨ f.addressSpace.val = 3)
  instanceBound := 1
  isIo := true

/-- The value a four-limb OpenVM word encodes: little-endian base-`256`. This is how a 32-bit
    register is spread across `MemoryPayload.data`, and it is why the registers an input read
    peeks are modelled as limb vectors rather than single field elements. -/
def wordValue (limbs : Vector (ZMod p) 4) : ZMod p :=
  limbs[0] + 256 * limbs[1] + 65536 * limbs[2] + 16777216 * limbs[3]

/-- How far a `HINT_STOREW` instance advances the execution-bridge clock: one tick per memory
    access — the pointer-register peek and the word write — plus one, so both sit *strictly*
    inside `(base, base + inputStepWindow)`, the window `StepLayout.tOffsetMatch` allows and
    `Audit/OpenVmLegalAudit.lean`'s `stepChip` exhibits. -/
def inputStepWindow : ℕ := 3

/-- OpenVM's `MemoryConfig.timestamp_max_bits`: "all timestamps must be in the range
    `[0, 2 ^ timestamp_max_bits)`". Capped at `29` by OpenVM itself, and `29` is its default.

    The cap is exactly the anti-wraparound condition of `assertLtChip`: `AssertLtSubAir` decides
    `x < y` by range-checking `y - x - 1` to this many bits, which is the same question only while
    `2 ^ (bits + 1) < p`. For BabyBear `2 ^ 30 < 2013265921`, and `30` bits would not fit —
    hence `29`. -/
def openVmTimestampBits : ℕ := 29

/-- The ceiling every timestamp in a segment sits below, and — the same constant, and not by
    accident — the furthest back a memory access may reach. The lt gadget is sized so that any
    difference between two legitimate timestamps fits in it, which is why merging accesses can
    never push one out of its range: both endpoints stay in `[0, openVmTimestampBound)`.

    This is `Circuit.hasStepLayout`'s `maxLookback` for OpenVM, and the bound
    `ConnectorBoundary.finalTimestampBounded` range-checks. -/
def openVmTimestampBound : ℕ := 2 ^ openVmTimestampBits

/-- A witness that an input-chip instance's contribution is a legal `HINT_STOREW`: which pointer
    register it peeked (`ptrLimbs`, a 32-bit value spread over four byte limbs as OpenVM stores
    it), which value it wrote (`byte`), and which word that write overwrote (`oldWord`,
    unconstrained — a write doesn't care what was there before, but the memory bus still needs a
    value for the receive half of the access).

    One word, not a run of them: `Rv32HintStoreAir` implements two opcodes, and `HINT_STOREW`
    hardcodes `num_words` to `1` and reads no count register at all
    (`extensions/rv32im/circuit/src/hintstore/mod.rs`). `HINT_BUFFER`, which does read a count off
    operand `a`, is a second chip type this host does not model yet — adding it is a new
    `isIo := true` entry in `openVmHost.chips` rather than a reshape. -/

structure InputRead (p : ℕ) where
  ptrLimbs : Vector (ZMod p) 4
  byte : ZMod p
  oldWord : Vector (ZMod p) 4
  /-- Memory holds bytes; see `memoryFinalizeHostChip`. Registers included — a peeked register is
      a memory access like any other, so its limbs carry the same discipline. -/
  byteIsByte : isByte byte
  oldWordIsBytes : ∀ d ∈ oldWord.toList, isByte d
  ptrLimbsAreBytes : ∀ d ∈ ptrLimbs.toList, isByte d
  /-- When the peeked register and the overwritten word were last set — not pinned to `0`: they
      were set by whatever earlier instruction touched them, at whatever time that was, which has
      nothing to do with *this* instance's own timing beyond being *earlier* (`ptrOffsetOk`,
      `wordOffsetOk`). -/
  ptrTime : ZMod p
  wordTime : ZMod p
  /-- This instance's own start time — free rather than pinned to `0`, since the chip may run at
      any point in a segment (`inputHostChip`'s `instanceBound` allows repeats), not only at its
      first instant, which timestamp `0` is reserved for (`memoryInitHostChip`). Both accesses
      land at `base` plus a fixed offset (`InputRead.interactions`) — one shared clock advancing
      once per access, matching `Rv32HintStoreAir`'s single `from_state.timestamp` and its
      `timestamp_pp` counter. -/
  base : ZMod p
  /-- **How far back the peeked register's previous record sits**, as an integer offset from this
      instance's own `base` — the same device `StepLayout.tOffset` uses for a guest chip, and for
      the same reason: `ptrTime` is a field element, so "earlier" is only a question about
      integers.

      §4.6.1: a Read "adds a message `(addr_space, ptr, ·, t_prev)` to the receive set and a
      message `(addr_space, ptr, ·, t)` to the send set", with the AIR constraining `t_prev < t`.
      `Rv32HintStoreAir` is an instruction executor like any other and range-checks that distance
      with the same `AssertLtSubAir`, which is where the lookback bound comes from. This
      instance's register write-back lands at `base + 1` (`InputRead.interactions`), so `t_prev <
      t` reads `ptrOffset < 1`.

      Without it a `HINT_STOREW` may claim to read a record set *after* its own write, and
      `Host.forcesAdmissible` is then false rather than merely unproven.
      `Audit/InputTimeGap.lean` audits this clause and carries the balancing run it excludes, in
      which one instance satisfying every clause of `Circuit.legalGuest` takes in two records at
      a single address; `Implementation/Forces.lean` has the counting argument that breaks without
      it. -/
  ptrOffset : ℤ
  ptrOffsetOk : -(openVmTimestampBound : ℤ) ≤ ptrOffset ∧ ptrOffset < 1
  ptrTimeMatch : ptrTime = base + ((ptrOffset : ℤ) : ZMod p)
  /-- The same for the word this instance overwrites, whose write lands at `base + 2`. -/
  wordOffset : ℤ
  wordOffsetOk : -(openVmTimestampBound : ℤ) ≤ wordOffset ∧ wordOffset < 2
  wordTimeMatch : wordTime = base + ((wordOffset : ℤ) : ZMod p)
  /-- The `pc` this instance starts at, on the execution bridge — an input-chip instance is an
      instruction executor like any other (whitepaper §4.5: "every instruction executor AIR must
      constrain that it adds a message `(pc_from, t_from)` to the receive set and `(pc_to, t_to)`
      to the send set"), not traffic outside the instruction stream. -/
  pcFrom : ZMod p
  /-- The `pc` it hands on. -/
  pcTo : ZMod p

/-- The address the write lands at, decoded from the pointer register's limbs. -/
def InputRead.ptr (r : InputRead p) : ZMod p := wordValue r.ptrLimbs

/-- The bus interactions an `InputRead` describes: one execution-bridge step (`StepLayout`'s
    `bridgeRecv`/`bridgeSend`/`bridgeNoOther` shape, mirrored exactly), receiving `(pcFrom, base)`
    and sending `(pcTo, base + inputStepWindow)`; then peek `ptrReg` (a full four-limb register
    word, whatever was there at `ptrTime`) at `base + 1`, then write `r.byte` (low limb, rest
    zeroed — see the module docstring) at `r.ptr` at `base + 2`, overwriting whatever was there at
    `wordTime`.

    Both accesses land at `r.base` plus their own position in one increasing sequence, not
    independently one tick after whatever they overwrote: an instance advances one shared clock
    once per access (`extensions/rv32im/circuit/src/hintstore/mod.rs`'s `Rv32HintStoreAir`, whose
    `timestamp_pp()` does exactly this off one `from_state.timestamp`). -/

-- TODO(AO): `ptrReg` isn't actually a VM-wide constant the way `openVmHost` treats it. Real OpenVM
-- (`extensions/rv32im/circuit/src/hintstore/execution.rs`, `HintStorePreCompute`/
-- `execute_e12_impl`) has the pointer register as instruction operand `b`, chosen per instruction
-- by the compiler — a faithful model needs it in the per-instance witness, not `openVmHost`'s
-- parameters. Deliberately not done yet.
def InputRead.interactions (r : InputRead p) (ptrReg execBusId memBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  [ { busId := execBusId, multiplicity := -1, payload := [r.pcFrom, r.base] },
    { busId := execBusId, multiplicity := 1,
      payload := [r.pcTo, r.base + (inputStepWindow : ZMod p)] },
    { busId := memBusId, multiplicity := -1,
      payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime] },
    { busId := memBusId, multiplicity := 1,
      payload := [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1] },
    { busId := memBusId, multiplicity := -1,
      payload := [2, r.ptr] ++ r.oldWord.toList ++ [r.wordTime] },
    { busId := memBusId, multiplicity := 1,
      payload := [2, r.ptr, r.byte, 0, 0, 0, r.base + 2] } ]

/-- The `HINT_STOREW` input host chip (default bus `1` for memory, `0` for the execution bridge):
    peeks a pointer register (address space `1`), then writes one unconstrained word at that
    pointer (address space `2`) — pinned exactly to an `InputRead` witness. The one host chip a
    segment may realize more than once, since the hint instruction runs again for each further
    word pulled off the input stream — up to `maxInstances` times, the same trace-budget cap a
    guest chip gets (`HostChip.instanceBound`).

    Its clock advance is the constant `inputStepWindow`, not a witness field, since a real
    `HINT_STOREW` makes a fixed number of accesses. `OpenVmParams.inputWindowOk` is where that
    meets `maxWindow`, the anti-wraparound budget an instance needs alongside guest instances on
    the same execution bridge (`OpenVmParams.windowOk`). -/
def inputHostChip (ptrReg maxInstances : Nat)
    (execBusId : Nat := openVmExecBusId) (memBusId : Nat := openVmMemBusId) :
    HostChip p where
  canProduce contribution :=
    ∃ r : InputRead p, contribution = busStateOf (r.interactions ptrReg execBusId memBusId)
  instanceBound := maxInstances
  -- TODO(AO): As GW observed, it is debatable whether this chip needs to be IO. If not, we'll need
  -- to reason about how the hints can change for completeness and knowledge soundness.
  isIo := true

/-- The timestamp a stateful message carries: payload index `6` for a memory record
    `(addr_space, ptr, data…, t)`, right after the four data limbs (whitepaper §4.6), and index `1`
    for an execution-bridge state `(pc, t)` (§4.5); `0` off both.

    Reading the bridge too is what lets `StepLayout` place *every* stateful interaction in a step's
    window on one scale, so `tOffset` compares across buses: a step's bridge receive sits at offset
    `0`, its memory accesses in between, and its bridge send at offset `d`.

    Positional rather than `getLast?` so it agrees with `memoryPayload?` on every payload: a
    payload too short to be a memory record (`memoryPayload? = none`) reads `0` instead of a data
    limb misread as a timestamp, and a longer one still reads field `6`. -/
def openVmTimestamp (memBusId : Nat := openVmMemBusId) : BusMessage p → ZMod p :=
  fun m => if m.1 = memBusId then m.2[6]?.getD 0
    else if m.1 = openVmExecBusId then m.2[1]?.getD 0 else 0

/-- How far `openVmRank` shifts a timestamp before reading it as a natural.

    A memory *receive* names a record from before its own step, so its offset from the step's base
    is negative and its raw `.val` may have wrapped. Shifting by the maximum lookback moves the
    whole window `[-maxLookback, maxWindow)` into the non-negative naturals, which is what makes
    the rank monotone in the offset — the one thing the soundness induction needs of it. -/
def openVmRankShift : ℕ := openVmTimestampBound

/-- OpenVM's ordering on stateful state: a message's timestamp, shifted into the naturals by
    `openVmRankShift`, which is what makes `<` well-founded and
    `maintains_of_stateful_active`'s induction possible. Off the stateful buses the rank is `0`;
    nothing there needs the induction. -/
def openVmRank (memBusId : Nat := openVmMemBusId) : BusMessage p → ℕ :=
  fun m => if m.1 = memBusId ∨ m.1 = openVmExecBusId then
    ((openVmTimestamp memBusId m) + (openVmRankShift : ZMod p)).val else 0

/-- The `RankModel.bound` that goes with `openVmRank` (see `openVmRankModel`): the timestamp
    ceiling plus the shift that makes room for a step's lookback. `2 ^ 30` for the default
    configuration — exactly the headroom OpenVM already reserves for `AssertLtSubAir`. -/
def openVmRankBound : ℕ := openVmTimestampBound + openVmRankShift

/-- Which OpenVM buses carry VM state: the execution bridge and memory (`OpenVmBusType.isStateful`);
    the four lookup tables do not, and an unmapped id carries nothing. -/
def openVmIsStateful (busMap : BusMap) (busId : Nat) : Bool :=
  match busMap busId with
  | some t => t.isStateful
  | none => false

/-- OpenVM requires sends to memory to be byte-valued. This is that test. -/
def openVmPayloadOk (busMap : BusMap) (m : BusMessage p) : Prop :=
  match busMap m.1 with
  | some .memory =>
    match memoryPayload? m.2 with
    | some f => f.isByteChecked → ∀ d ∈ f.data, isByte d
    | none => True
  | some _ => True
  | none => False

/-- The timestamp an execution-bridge message carries (whitepaper §4.5). -/
def openVmBridgeTimestamp (m : BusMessage p) : ZMod p := m.2[1]?.getD 0

/-- The timestamp a memory message carries: payload index `6` of `(addr_space, ptr, data…, t)`,
    right after the four data limbs (whitepaper §4.6).

    Agrees with `openVmRank` on the memory bus. This is `GuestBusRules.getTimestamp`
    (`Legal.lean`) for OpenVM. -/
def openVmMemTimestamp (m : BusMessage p) : ZMod p := m.2[6]?.getD 0

/-- The access key an OpenVM memory message carries: `(address space, pointer)`, payload slots `0`
    and `1` — `MemoryBusShape.address` at the memory shape, as a `GuestBusRules`-level function.
    This is `Circuit.legalGuest`'s `memAddress`. -/
def openVmMemAddress (m : BusMessage p) : List (Option (ZMod p)) := [m.2[0]?, m.2[1]?]

/-- OpenVM's rules for how guests use buses. Copies `OpenVmSemantics.lean`'s existing `accepts`
    (which defines the tables) rather than restating it, so we trust their table definitions.

    `execBusId` is fixed at `openVmExecBusId`, `defaultBusMap`'s own convention (see `StepLayout`'s
    uses throughout this file); `getTimestamp` is `openVmTimestamp memBusId`.

    `hmem` — `memBusId` is the *only* id `busMap` sends to `.memory` — defaults to
    `defaultBusMap_mem_unique`, so call sites using `defaultBusMap`/`openVmMemBusId` (all but a
    couple, genuinely generic over the bus map) need no change. -/
def openVmGuestRules (busMap : BusMap) (memBusId : Nat)
    (hmem : ∀ b, busMap b = some .memory → b = memBusId := by exact defaultBusMap_mem_unique) :
    GuestBusRules p where
  isStateful := openVmIsStateful busMap
  accepts := ApcOptimizer.OpenVM.accepts busMap
  payloadOk := openVmPayloadOk busMap
  execBusId := openVmExecBusId
  memBusId := memBusId
  getTimestamp := openVmTimestamp memBusId
  memPayloadOnly := fun m hst hne => by
    simp only [openVmIsStateful] at hst
    cases hbm : busMap m.1 with
    | none => rw [hbm] at hst; exact absurd hst (by decide)
    | some t =>
      cases t with
      | memory => exact absurd (hmem m.1 hbm) hne
      | executionBridge | pcLookup | variableRangeChecker | bitwiseLookup
      | tupleRangeChecker _ _ => simp [openVmPayloadOk, hbm]

/-- A witness that the connector chip's contribution closes a segment's execution bridge: the
    segment's initial and final `(pc, timestamp)` states.

    `VmConnectorAir` is a two-row trace of these two states, constraining `begin.timestamp = 1`
    (hence no field for it here) and range-checking *each* row's `timestamp` to
    `timestamp_max_bits` — `finalTimestampBounded`, the one place in this development where the
    rank window is a checked constraint rather than an assumption. -/
structure ConnectorBoundary (p : ℕ) where
  initialPc : ZMod p
  finalPc : ZMod p
  finalTimestamp : ZMod p
  /-- `VmConnectorAir` range-checks every row's `timestamp` to `openVmTimestampBits` bits. -/
  finalTimestampBounded : finalTimestamp.val < openVmTimestampBound

/-- The bus interactions a `ConnectorBoundary` describes. `ExecutionBus::execute(_, _, prev, next)`
    receives `prev` and sends `next`, and `VmConnectorAir` calls it with `prev` the *final* state
    and `next` the *initial* one: the connector seeds the chain at `(initialPc, 1)` and consumes
    whatever the last instruction left. -/
def ConnectorBoundary.interactions (r : ConnectorBoundary p) (execBusId : Nat) :
    List (BusInteraction (ZMod p)) :=
  [ { busId := execBusId, multiplicity := 1, payload := [r.initialPc, 1] },
    { busId := execBusId, multiplicity := -1, payload := [r.finalPc, r.finalTimestamp] } ]

/-- The connector host chip (default bus `0`): OpenVM's `VmConnectorAir`, the execution bridge's
    seed and terminator — without it the bridge would have to balance among the guest chips alone,
    which no real segment does. Pinned exactly to a `ConnectorBoundary` witness, like the input and
    output chips, because the range-checked final timestamp is what a `Host.ordersRanks` argument
    has to start from. -/
def connectorHostChip (execBusId : Nat := openVmExecBusId) : HostChip p :=
  singletonWitnessChip fun r : ConnectorBoundary p => busStateOf (r.interactions execBusId)

/-- **How one OpenVM segment is configured.** Everything `openVmHost` needs that OpenVM itself
    doesn't fix, bundled so the theorems about it quantify over one `P` rather than five numbers
    and two inequalities.

    The two `Ok` fields are the anti-wraparound conditions — *proof obligations on the
    configuration*, checked once here rather than carried through every statement: a segment
    proved at these sizes has timestamps and multiplicities that provably stay inside `ZMod p`.
    No degree bound lives here — that belongs to the proving backend, not the VM, and is a
    parameter of `PreservesDegree`. -/
structure OpenVmParams (p : ℕ) where
  /-- The VM's trace budget (see `VmAssignment.withinBudget`). -/
  maxInstances : ℕ
  /-- The register the input chip peeks for its write pointer. -/
  ptrReg : Nat
  /-- …and it is not `x0`. `InputRead.interactions` writes address space `1` at `ptrReg` carrying
      `ptrLimbs`, which is only constrained to be byte-valued; at `ptrReg = 0` that is a nonzero
      write to the hardwired zero register, falsifying `x0ReturnsZero`. A `HINT_STOREW` whose
      pointer register is `x0` is meaningless anyway.

      As a field element, since that is the form the memory payload carries and the form
      `x0ReturnsZero` compares against: `ptrReg ≠ 0` in `ℕ` would leave a multiple of `p` free to
      alias register `0`. -/
  ptrRegNeZero : ((ptrReg : ZMod p)) ≠ 0
  /-- The most input-chip instances a segment may realize — every other host chip is capped at
      one, so this is what keeps the host side of a run finite (`HostAssignment.satisfies`). One
      instance is one `HINT_STOREW`, hence one input datum: an N-word chunk costs N instances. -/
  maxInputInstances : ℕ
  /-- The `StepLayout` window bound: `StepLayout.tWindowLt`. A property of the chips being run rather
      than of OpenVM — a fused APC advances by its whole basic block, not by one instruction's
      `timestamp_delta`. -/
  maxWindow : ℕ
  /-- The most bus interactions a guest chip may carry. -/
  maxInteractions : ℕ
  /-- No timestamp overflow on the *whole* execution bridge — guest instances and input-chip
      instances together, since both now sit on it (`InputRead.pcFrom`/`pcTo`). Strictly more
      than `Host.noTimeOverflow` (which only needs the guest term); `openVmHost` derives that
      weaker fact from this one. -/
  windowOk : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p
  /-- No multiplicity overflow, counting the *host* side too: every interaction a segment can
      carry — `maxInteractions` per guest instance, six per input-chip instance
      (`InputRead.interactions`), and the four the remaining single-instance host chips
      contribute — fits in `ZMod p` at once. Strictly more than `Host.noMultOverflow`, whose
      `+ 1` budgets only the exempt chip's own touch; `openVmHost` derives that weaker fact from
      this one.

      The host term is what a record-matching argument needs: a run may receive one memory record
      up to `maxInteractions * maxInstances` times from guests *and* once from
      `memoryFinalizeHostChip` *and* twice per input-chip instance, and only a bound on the sum
      keeps that count from wrapping. -/
  budgetOk : maxInteractions * maxInstances + 6 * maxInputInstances + 4 < p
  /-- An input-chip instance's own clock advance fits the window too. Pinned rather than
      per-witness, since `inputStepWindow` is a constant (`inputHostChip`). -/
  inputWindowOk : inputStepWindow < maxWindow
  /-- The rank window fits in the field: a timestamp below the ceiling, shifted by the maximum
      lookback, is still an honest natural. This is OpenVM's own `2 ^ (timestamp_max_bits + 1) < p`
      — the condition that caps `timestamp_max_bits` at `29` for BabyBear, and exactly the headroom
      `AssertLtSubAir` already needs. -/
  rankWindowOk : openVmRankBound < p

/-- A concrete OpenVM `Host`: `defaultBusMap`'s four stateless lookup tables (default bus ids),
    memory initialization (all-zero) and finalization, the output chip, a `HINT_STOREW` input chip
    peeking register `P.ptrReg` — all sharing `openVmMemBusId`, `defaultBusMap`'s memory bus — and
    the connector, which seeds and terminates the execution bridge.

    No `memBusId`/`busMap` parameters: every chip below is already pinned to `defaultBusMap`'s own
    numbering (as `pcLookupHostChip`'s default `busId` is), so a free `memBusId` could only
    disagree with it, not vary it — `openVmGuestRules defaultBusMap openVmMemBusId` already reads
    bus `openVmMemBusId` as `.memory` (`defaultBusMap`'s `1 ↦ some .memory` arm).

    Pair with a `Guest p` to get a `Vm p`, or feed straight into `CanEffect`/`vmEquivalent`. -/
noncomputable def openVmHost (P : OpenVmParams p) : Host p where
  maxInstances := P.maxInstances
  maxWindow := P.maxWindow
  maxLookback := openVmTimestampBound
  maxInteractions := P.maxInteractions
  legalGuest c :=
    c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress P.maxWindow
      openVmTimestampBound P.maxInteractions
  chips :=
    [ pcLookupHostChip, bitwiseLookupHostChip, variableRangeCheckerHostChip,
      tupleRangeCheckerHostChip, memoryInitHostChip,
      memoryFinalizeHostChip,
      inputHostChip P.ptrReg P.maxInputInstances, connectorHostChip ]
  noTimeOverflow := lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (by omega : P.maxInstances + 1 ≤ P.maxInstances + P.maxInputInstances + 1))
    P.windowOk
  noMultOverflow := by
    have := P.budgetOk
    omega

/-- `openVmHost`'s memory-init chip: an IO-labeled (`HostChip.isIo`) entry pinned to
    `memoryInitHostChip`. -/
def openVmMemInitChip (P : OpenVmParams p) : Fin (openVmHost P).chips.length :=
  ⟨4, by simp [openVmHost]⟩

/-- `openVmHost`'s memory-finalize chip: an IO-labeled (`HostChip.isIo`) entry pinned to
    `memoryFinalizeHostChip`. -/
def openVmMemFinalizeChip (P : OpenVmParams p) : Fin (openVmHost P).chips.length :=
  ⟨5, by simp [openVmHost]⟩

/-- `openVmHost`'s input chip: the IO-labeled (`HostChip.isIo`) entry pinned to `inputHostChip`.
    This host models only `HINT_STOREW`, so it is the only chip type that pulls input. -/
def openVmInputChip (P : OpenVmParams p) : Fin (openVmHost P).chips.length :=
  ⟨6, by simp [openVmHost]⟩

end ApcOptimizer.OpenVM
