import ApcOptimizer.VmSpec.Basic

set_option autoImplicit false

/-! What a VM requires of all guest circuits to run correctly. Defines a property
    `Circuit.legalGuest` of an individual circuit, and **not** with respect to a concrete
    assignment — stated against `GuestBusRules`, not `Spec.lean`'s `BusSemantics`. -/

variable {p : ℕ}

/-- Host-specific bus rules that legality depends on. -/
structure GuestBusRules (p : ℕ) where
  /-- Whether this bus ID carries VM state (memory, the execution bridge), rather than being a
      stateless lookup table. -/
  isStateful : Nat → Bool
  /-- For a stateless bus, whether the receiving chip accepts this message. I.e., if it is in the
      table. -/
  accepts : BusInteraction (ZMod p) → Prop
  /-- Whether a *payload* on a stateful bus is Ok, i.e., respects VM invariants.  This `Prop`
      defines the invariant. Elsewhere, we inductively prove it everywhere it is needed.

      For OpenVM: that a memory send's data limbs are bytes. -/
  payloadOk : BusMessage p → Prop
  execBusId : Nat
  memBusId : Nat
  /-- How to get the timestamp for a memory access. -/
  getTimestamp : BusMessage p → ZMod p
  /-- payloadOk must only constrain the memory bus. For other it must be trivially true. -/
  memPayloadOnly : ∀ m : BusMessage p, isStateful m.1 = true → m.1 ≠ memBusId → payloadOk m

/-- Whether a circuit's **algebraic** constraints alone force property `P` on every message it
    writes to a bus of the given statefulness. -/
def Circuit.algebraicallyForces (c : Circuit p) (r : GuestBusRules p) (stateful : Bool)
    (P : BusInteraction (ZMod p) → Prop) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
    ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = stateful → P (bi.eval asg)

/-- A guest chip writes only `0`/`1` multiplicities to stateless buses

    OpenVM §2.2.4: multiset balancing implies lookup-table relations only "under certain conditions
    which prevent integer overflow of the field characteristic". This is that condition on the
    lookup side. -/
def Circuit.statelessSendOnly (c : Circuit p) (r : GuestBusRules p) : Prop :=
  c.algebraicallyForces r false fun msg => msg.multiplicity = 0 ∨ msg.multiplicity = 1

/-- A guest chip writes only `0`/`±1` multiplicities to stateful buses.

    OpenVM §4.5, an instruction executor adds `(pc_from, t_from)` to the execution bus's receive set
    and `(pc_to, t_to)` to its send set "exactly once for each instruction"; and §4.6.1, a read or a
    write adds one memory message to each set. -/
def Circuit.statefulPolarity (c : Circuit p) (r : GuestBusRules p) : Prop :=
  c.algebraicallyForces r true fun msg =>
    msg.multiplicity = 0 ∨ msg.multiplicity = 1 ∨ msg.multiplicity = -1

/-- This assignment respects the table semantics of stateless buses.

    See `Circuit.statelessSendsMaintain`. -/
def Circuit.satisfiesStateless (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p) :
    Prop :=
  ∀ bi ∈ c.busInteractions, r.isStateful bi.busId = false →
    (bi.eval asg).multiplicity ≠ 0 → r.accepts (bi.eval asg)

/-- The message the `i`th interaction writes under `asg`: its bus and payload, dropping the
    multiplicity. -/
def Circuit.msgAt (c : Circuit p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : BusMessage p :=
  let bi := (c.busInteractions.get i).eval asg
  (bi.busId, bi.payload)

/-- The multiplicity the `i`th interaction writes under `asg`. -/
def Circuit.multAt (c : Circuit p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : ZMod p :=
  ((c.busInteractions.get i).eval asg).multiplicity

/-- The `i`th interaction is on a stateful bus and actually happens. -/
def Circuit.activeStateful (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : Prop :=
  r.isStateful (c.busInteractions.get i).busId = true ∧ c.multAt asg i ≠ 0

/-- …and is a *send*. -/
def Circuit.statefulSend (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : Prop :=
  r.isStateful (c.busInteractions.get i).busId = true ∧ c.multAt asg i = 1

/-- …restricted to the memory bus. -/
def Circuit.activeMem (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : Prop :=
  c.activeStateful r asg i ∧ (c.busInteractions.get i).busId = r.memBusId

/-- …and is a memory *send*. -/
def Circuit.memSend (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (i : Fin c.busInteractions.length) : Prop :=
  c.statefulSend r asg i ∧ (c.busInteractions.get i).busId = r.memBusId

/-- The layout of a guest instance's stateful traffic in time.

    The instance performs one instruction step, advancing the clock by fewer than `maxWindow`
    ticks: it receives `(pcFrom, tStart)` from the execution bridge, sends `(pcTo, tStart +
    tWindow)` back, and puts nothing else there. (OpenVM whitepaper §4.5: an executor "adds a
    message `(pc_from, t_from)` to the receive set and a message `(pc_to, t_to)` to the send set
    exactly once", and "must also constrain that `t_from < t_to`".)

    Every stateful interaction sits at an integer offset (`tOffset`) from `tStart`, in
    `[-maxLookback, tWindow]`: inside the step, or up to `maxLookback` ticks before it, where a
    memory *receive* might live, naming the record an earlier instruction left —
    `AssertLtSubAir` range-checks that distance to `timestamp_max_bits` bits, so it cannot reach
    further back. (§4.2 puts guest-state timestamps at `t_from < t < t_to`.) Offsets are integers,
    not field elements, so comparisons work; the timestamps themselves are `ZMod p`.

    This assumes a **fused** APC equates adjacent timestamps on the execution bridge, so the
    step's `tWindow` is the sum of the fused instructions' `tWindow_i` and they execute
    consecutively in time. Currently powdr adds no such equations, so the timestamps are free and
    the instructions can execute out of order — genuinely, not just apparently, so no global
    argument can derive the chaining either, and it makes the byte-constraint induction awkward to
    state. Powdr should add the equations to the fused APCs; that looks like its intent. -/
structure StepLayout {p : ℕ} (c : Circuit p) (r : GuestBusRules p) (asg : ChipAssignment p)
    (memAddress : BusMessage p → List (Option (ZMod p)))
    (maxWindow maxLookback : ℕ) where

  -- EXECUTION BRIDGE

  /-- The `pc` the step starts at. -/
  pcFrom : ZMod p
  /-- The `pc` it hands on. -/
  pcTo : ZMod p
  /-- The timestamp it starts at. -/
  tStart : ZMod p

  /-- How far it advances the clock. -/
  tWindow : ℕ
  /-- The step *advances* the clock... -/
  tWindowPos : 0 < tWindow
  /-- ... and fits in the window. -/
  tWindowLt : tWindow < maxWindow

  /-- We receive `(pcFrom, tStart)` on the bridge, -/
  bridgeRecv : c.allEffects asg (r.execBusId, [pcFrom, tStart]) = -1
  /-- ... send `(pcTo, tStart+d)`, ... -/
  bridgeSend : c.allEffects asg (r.execBusId, [pcTo, tStart + (tWindow : ZMod p)]) = 1
  /-- ... and nothing else. -/
  bridgeNoOther : ∀ m : BusMessage p, m.1 = r.execBusId →
    m ≠ (r.execBusId, [pcFrom, tStart]) →
    m ≠ (r.execBusId, [pcTo, tStart + (tWindow : ZMod p)]) →
      c.allEffects asg m = 0

  -- MEMORY

  /-- Where in the step's window each interaction sits. Essentially, each timestamp as an integer
      offset from `tStart`. Receives from previous steps get negative values. -/
  tOffset : Fin c.busInteractions.length → ℤ

  /-- The offsets match actual timestamps and are in the step's window. -/
  tOffsetMatch : ∀ i : Fin c.busInteractions.length, c.activeStateful r asg i →
    -(maxLookback : ℤ) ≤ tOffset i ∧ tOffset i ≤ (tWindow : ℤ) ∧
      r.getTimestamp (c.msgAt asg i) = tStart + ((tOffset i : ℤ) : ZMod p)

  /-- Memory sends have distinct times. -/
  sendTimesDistinct : ∀ i j : Fin c.busInteractions.length,
    c.memSend r asg i → c.memSend r asg j →
      memAddress (c.msgAt asg i) = memAddress (c.msgAt asg j) →
        tOffset i = tOffset j → i = j

  /-- Memory sends are in-window. -/
  sendInWindow : ∀ i : Fin c.busInteractions.length,
    c.memSend r asg i → 0 ≤ tOffset i ∧ tOffset i < tWindow

  /-- Any pre-window interactions are memory receives. -/
  negOffsetOnlyMemRecv : ∀ i : Fin c.busInteractions.length,
    c.activeStateful r asg i → tOffset i < 0 →
      (c.busInteractions.get i).busId = r.memBusId ∧ c.multAt asg i = -1

  /-- Memory accesses are paired. This function is the pairing; its requirements follow. -/
  memPartner : Fin c.busInteractions.length → Fin c.busInteractions.length

  /-- The pairing is closed on memory interactions and is a fixpoint-free involution there. -/
  memPartner_invol : ∀ i : Fin c.busInteractions.length,
    (c.busInteractions.get i).busId = r.memBusId →
      memPartner (memPartner i) = i ∧ memPartner i ≠ i ∧
        (c.busInteractions.get (memPartner i)).busId = r.memBusId

  /-- Sends and receives are paired. -/
  memPartner_mult : ∀ i : Fin c.busInteractions.length,
    (c.busInteractions.get i).busId = r.memBusId →
      c.multAt asg (memPartner i) = - c.multAt asg i ∧
      memAddress (c.msgAt asg i) = memAddress (c.msgAt asg (memPartner i))

  /-- Receives are constrained to preceed sends. (Typically via range-checks.) -/
  memPartner_time : ∀ i : Fin c.busInteractions.length,
    (c.busInteractions.get i).busId = r.memBusId → c.multAt asg i = -1 →
      tOffset i < tOffset (memPartner i)

  /-- Each memory send is Ok, given that every earlier memory interaction is Ok.

      This is the induction that carries the memory-byte invariant: a send is justified by
      whatever actually precedes it in time. Restricted to the memory bus — `memPayloadOnly`
      already settles every other stateful bus.

      OpenVM §3.2.5, elements of address spaces 1 (registers) and 2 (user memory) "are constrained
      to lie in `[0, 2^8)`". In §4.6: a message appears "if and only if at timestamp `t` the data
      memory had values `data`" at that address. -/
  memSendsOk : ∀ i : Fin c.busInteractions.length, c.memSend r asg i →
    (∀ j : Fin c.busInteractions.length, tOffset j < tOffset i → c.activeMem r asg j →
      r.payloadOk (c.msgAt asg j)) →
    r.payloadOk (c.msgAt asg i)


/-- Every assignment a guest chip admits lays out as one instruction step.

    Needed to avoid timestamp overflow, and to give the soundness argument's induction something to
    descend on. -/
def Circuit.hasStepLayout (c : Circuit p) (r : GuestBusRules p)
    (memAddress : BusMessage p → List (Option (ZMod p))) (maxWindow maxLookback : ℕ) : Prop :=
  ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    Nonempty (StepLayout c r asg memAddress maxWindow maxLookback)

/-- What a VM requires of any guest chip it will run. Instantiates the `Host.legalGuest` field.

    See the consituent fields for the conditions. -/
structure Circuit.legalGuest (c : Circuit p) (r : GuestBusRules p)
    (memAddress : BusMessage p → List (Option (ZMod p)))
    (maxWindow maxLookback maxInteractions : ℕ) : Prop where
  sendOnly : c.statelessSendOnly r
  polarity : c.statefulPolarity r
  stepLayout : c.hasStepLayout r memAddress maxWindow maxLookback
  size : c.busInteractions.length ≤ maxInteractions
  /-- Any assignment that interacts with register 0 has value 0.

      TODO(AO): study APCs that interact with register 0 to see if this requirement is correctly
      phrased. I have not seen such APCs yet. -/
  x0Zero : ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg → c.satisfiesStateless r asg →
    ∀ i : Fin c.busInteractions.length, c.memSend r asg i →
      (c.msgAt asg i).2[0]? = some 1 → (c.msgAt asg i).2[1]? = some 0 →
        (c.msgAt asg i).2[2]? = some 0 ∧ (c.msgAt asg i).2[3]? = some 0 ∧
          (c.msgAt asg i).2[4]? = some 0 ∧ (c.msgAt asg i).2[5]? = some 0
