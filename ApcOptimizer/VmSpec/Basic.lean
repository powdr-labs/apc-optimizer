import ApcOptimizer.Spec
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-! VM-level correctness: what it means to correctly replace one list of guest chips with another,
    against a fixed host.

    `Spec.lean` defines equivalence for a single `Circuit`, with "the rest of the VM" abstracted
    into `BusSemantics`: per-message `accepts`/`admissible`/`maintainsInvariants` predicates, with
    conditions on VM-level invariants that are not obviously true. This file makes the VM explicit
    instead: host chips are named, buses balance globally, and the observable is the VM's
    input/output, so no per-message assumptions are needed.

    The definition is equi-effectfulness: for every effect one chipset can produce (`CanProduce`),
    the other can produce it too — soundness one direction (`VmSoundReplacement`), completeness
    the other.

    This file and the host definition it uses must be audited; nothing in `Implementation/` need
    be checked.

    What is not yet here: a theorem wiring a real per-chip optimizer (`ApcOptimizer/Optimizer.lean`)
    into `VmSoundReplacement` for a whole VM. `vmSoundReplacement_of_forall₂`
    (`Implementation/Connection.lean`) already consumes exactly the per-chip
    `Circuit.isSoundReplacementOf` a chip-level optimizer proves; what blocks assembling the two is
    its legality hypothesis on the optimizer's *output*, which soundness does not give for free —
    see the counterexample in `agent-docs/vm-spec.md`. Closing that gap needs each optimizer pass
    to also prove it preserves `Circuit.legalGuest`, which no pass does today. -/

variable {p : ℕ} [Fact p.Prime]

/-- A host-chip (memory init/final, a lookup table, an input chip, the output chip, ...). It is
    defined only by the effects it can have and by how many instances it can have. There is no
    explicit circuit. -/
structure HostChip (p : ℕ) where
  /-- Whether this `BusState` can be produced by this host-chip type. -/
  canProduce : BusState p → Prop
  /-- The most instances of this chip a satisfying assignment may realize. -/
  instanceBound : ℕ

/-- A VM's input: a stream of values. -/
abbrev VmInput (p : ℕ) := List (ZMod p)

/-- A VM's output: an array of values. -/
abbrev VmOutput (p : ℕ) := List (ZMod p)

/-- The externally observable effect of a VM: inputs and outputs. -/
structure VmEffect (p : ℕ) where
  input : VmInput p
  output : VmOutput p

/-- **The VM the correctness statement is about.** Every field here is audited, on one of two
    counts: it feeds `VmSat`/`VmAssignment.effects`, and so determines what `CanProduce` — hence
    `VmEquivalent` — means; or it is what the theorems require of the guest chips they are handed
    (`legalGuest`, and the sizes it is stated at). Get one wrong and the theorem is about the
    wrong machine, or is about the right one vacuously.

    The sizes are fields rather than loose hypotheses on each theorem precisely so that the latter
    read cleanly: `maxWindow`/`maxInteractions` and the two anti-wraparound conditions are facts
    about how a VM is configured, fixed once when a concrete `Host` is built.

    Deliberately absent is anything the *soundness argument* needs but neither the statement nor
    its hypotheses do. The ordering on stateful state and its window live in
    `Implementation/Rank.lean`'s `RankModel`, which no statement in this file mentions; the
    backend's degree bound is a parameter of `PreservesDegree`. See this module's header for the
    audit tiers. -/
structure Host (p : ℕ) where
  chips : List (HostChip p)
  /-- The VM's trace budget: the most guest-chip instances a satisfying assignment may realize,
      in total across all types (see `VmAssignment.withinBudget`). -/
  maxInstances : ℕ
  /-- The most one guest instance may advance the clock (`Circuit.hasStepLayout`).

      Needed to prevent clock overflows, unlocking time-inductive arguments. -/
  maxWindow : ℕ
  /-- The furthest back in time one guest instance may reach. Needed for send->recieve induction.

      For OpenVM this is `2 ^ timestamp_max_bits`, whose check relies on `AssertLtSubAir` -/
  maxLookback : ℕ
  /-- The most bus interactions one guest instance may carry.

      Needed to prevent multiplicity overflows, unlocking counting arguments. -/
  maxInteractions : ℕ
  /-- Which guest circuits this host is prepared to run.  We need only optimize these correctly.

      For OpenVM: binary multiplicities on lookup buses, `±1` on stateful ones, byte-valued memory
      sends.

      These live on the `Host` because they are the VM's requirements, not any chip's. They are
      *not* a conjunct of `VmSat`, because they are not (and cannot) be checked in constraints.  -/
  legalGuest : Circuit p → Prop
  /-- The `chips` indices that pull the input stream. A list rather than a single index: a VM may
      read input through several chip types. -/
  inputChips : List (Fin chips.length)
  /-- Map from an input chip instance's effects to its contribution to the input stream, indexed
      by which of `inputChips` produced it (chip types read the stream differently). -/
  getInputChunk : Fin chips.length → BusState p → VmInput p
  /-- Map from an input chip instance's effects to when it ran. Input chunks are ordered by this. -/
  getInputTime : Fin chips.length → BusState p → ZMod p
  /-- The `chips` index that is the output chip type (`instanceBound` `1`, so at most one
      instance: see `VmAssignment.effects`). -/
  outputChip : Fin chips.length
  /-- Map from an output chip instance's effects to the output array. -/
  getOutput : BusState p → VmOutput p
  /-- No timestamp overflow: a run of `maxInstances` instructions, each advancing the clock by less
      than `maxWindow`, does not overflow.

      TODO(AO): why the +1's? Are these bounds still tight?
       -/
  noTimeOverflow : (maxInstances + 1) * (maxWindow + 1) < p
  /-- No multiplicity overflow: a run of `maxInstances` instructions, each with at most
      `maxInteractions` bus interactions, does not overflow.

      The `+ 1` is for the exempt host chip's own touch. -/
  noMultOverflow : maxInteractions * maxInstances + 1 < p

/-- A list of guest chips. -/
abbrev Guest (p : ℕ) := List (Circuit p)

/-- Every chip in `G` is one this host will run. -/
def Host.legalGuests (host : Host p) (G : Guest p) : Prop :=
  ∀ c ∈ G, host.legalGuest c

/-- A VM: a host and guest chips. -/
structure Vm (p : ℕ) where
  host : Host p
  guest : Guest p


/-- An assignment to one chip instance: for each variable, what value it takes. -/
abbrev ChipAssignment (p : ℕ) := Variable → ZMod p

/-- A circuit's effects: its net multiplicity contribution to each bus messsage.

    Unlike `Circuit.sideEffects`, this includes all buses, not just stateful ones. -/
def Circuit.allEffects (circuit : Circuit p) (assignment : ChipAssignment p) :
    BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide ((m.busId, m.payload) = message))).map (fun m => m.multiplicity) |>.sum

/-- The guest half of a VM assignment: for each chip *type*, however many algebraic assignments the
    witness chooses to realize. -/
abbrev GuestAssignment (p : ℕ) (guestChips : Guest p) :=
  Fin guestChips.length → List (ChipAssignment p)

/-- The host half of a VM assignment: for each chip type, its effects, one per instance. -/
abbrev HostAssignment (p : ℕ) (host : Host p) := Fin host.chips.length → List (BusState p)

/-- An assignment to a VM. -/
structure VmAssignment (p : ℕ) (vm : Vm p) where
  guestAssignments : GuestAssignment p vm.guest
  hostAssignment : HostAssignment p vm.host

/-- The net effect of the guest instances. -/
def GuestAssignment.busEffect {G : Guest p} (gA : GuestAssignment p G) : BusState p :=
  fun message => ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg message)).sum

/-- The net effect of the host instances. -/
def HostAssignment.busEffect {host : Host p} (hA : HostAssignment p host) : BusState p :=
  fun message => ∑ t : Fin host.chips.length, ((hA t).map (fun effect => effect message)).sum

/-- How many guest instances the assignment realizes, across all types. -/
def GuestAssignment.instanceCount {G : Guest p} (gA : GuestAssignment p G) : ℕ :=
  ∑ t : Fin G.length, (gA t).length

/-- Every realized guest instance satisfies its own chip's algebraic constraints. -/
def GuestAssignment.satisfiesAlgebraic {G : Guest p} (gA : GuestAssignment p G) : Prop :=
  ∀ t : Fin G.length, ∀ asg ∈ gA t, (G.get t).satisfiesAlgebraic asg

/-- All host assignments are producible and stay inside their chip's instance count. -/
structure HostAssignment.satisfies {host : Host p} (hA : HostAssignment p host) : Prop where
  /-- Every realized instance's effect is one its chip can have. -/
  producible : ∀ t : Fin host.chips.length, ∀ effect ∈ hA t, (host.chips.get t).canProduce effect
  /-- No chip is realized more times than the VM allows (`HostChip.instanceBound`). -/
  withinBound : ∀ t : Fin host.chips.length, (hA t).length ≤ (host.chips.get t).instanceBound

/-- The net multiplicity contributed to every bus message, summed over host and guest. -/
def VmAssignment.busEffect {vm : Vm p} (a : VmAssignment p vm) : BusState p :=
  fun message => a.guestAssignments.busEffect message + a.hostAssignment.busEffect message

-- ANCHOR: vmSat
/-- Whether a VM assignment is satisfying: every realized instance behaves (guests meet alebraic
    constraints and hosts can produce their effects), every bus balances, and the instance count is
    small enough.

    Every conjunct is and must be *directly* checked at runtime on a real OpenVM run. Thus, two
    other kinds of constraints are explicitly *excluded* here:

    * Requirements on a guest *circuit* — `Host.legalGuest`, the degree bound. These quantify
      over all assignments---not checkable or checked at runtime. These become
      assumptions/obligations on the optimizer instead (e.g., `Host.legalGuests`).
    * Invariants that are *consequences* of several chips and/or the host. Such invariants are
      proved in `Implementation/` and are not part of this specification. For example, rank
      constraints and byte constraints on writes.
    -/
structure VmSat (vm : Vm p) (a : VmAssignment p vm) : Prop where
  /-- Every guest-chip instance's algebraic constraints hold under `a`. -/
  satisfiesGuest : a.guestAssignments.satisfiesAlgebraic
  /-- The host side of the assignment is producible and within its instance counts
      (`HostAssignment.satisfies`). -/
  satisfiesHost : a.hostAssignment.satisfies
  /-- Every bus balances: the net multiplicity of every message is zero. -/
  balances : ∀ message : BusMessage p, a.busEffect message = 0
  /-- There are not too many guest-chip instances in total. The host side of the same budget is
      `HostAssignment.satisfies`'s count clauses.

      This is enforced by OpenVM's proof system and is needed to prevent overflow, e.g., in
      multiplicities. -/
  withinBudget : a.guestAssignments.instanceCount ≤ vm.host.maxInstances
-- ANCHOR_END: vmSat

/-- Every instance of every input chip, tagged with the `Host.inputChips` index that realized it. -/
def VmAssignment.inputInstances {vm : Vm p} (a : VmAssignment p vm) :
    List (Fin vm.host.chips.length × BusState p) :=
  vm.host.inputChips.flatMap fun i => (a.hostAssignment i).map (fun c => (i, c))

/-- The input-chip instances of a VM assignment, in the order their chunks are read: sorted by
    `Host.getInputTime`. -/
def VmAssignment.orderedInputInstances {vm : Vm p} (a : VmAssignment p vm) :
    List (Fin vm.host.chips.length × BusState p) :=
  a.inputInstances.mergeSort
    (fun x y => decide ((vm.host.getInputTime x.1 x.2).val ≤ (vm.host.getInputTime y.1 y.2).val))

/-- The effects of a VM assignment: input and outputs -/
def VmAssignment.effects {vm : Vm p} (a : VmAssignment p vm) : VmEffect p :=
  { input := a.orderedInputInstances.flatMap (fun x => vm.host.getInputChunk x.1 x.2),
    output := vm.host.getOutput ((a.hostAssignment vm.host.outputChip).headD 0) }

-- ANCHOR: canEffect
/-- Whether `vm` can produce effect `e`. -/
def CanProduce (vm : Vm p) (e : VmEffect p) : Prop :=
  ∃ a : VmAssignment p vm, VmSat vm a ∧ a.effects = e
-- ANCHOR_END: canEffect

-- ANCHOR: vmEquivalent
/-- `guestChips'` is a *sound* VM-level replacement for `guestChips`: it can produce no effect
    the original could not. Nothing new becomes possible.

    The contextual, multi-chip analogue of `Circuit.isSoundReplacementOf`. -/
def VmSoundReplacement (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  ∀ e : VmEffect p, CanProduce ⟨host, guestChips'⟩ e → CanProduce ⟨host, guestChips⟩ e

/-- `guestChips'` is a *complete* VM-level replacement for `guestChips`: every effect the
    original could produce, it can produce too. Nothing is lost.

    The contextual, multi-chip analogue of `Circuit.isCompleteReplacementOf`. -/
def VmCompleteReplacement (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  ∀ e : VmEffect p, CanProduce ⟨host, guestChips⟩ e → CanProduce ⟨host, guestChips'⟩ e

/-- `guestChips'` is a VM-level equivalent replacement for `guestChips` against the fixed
    `host`: they are equi-effectful. -/
def VmEquivalent (host : Host p) (guestChips guestChips' : Guest p) : Prop :=
  VmSoundReplacement host guestChips guestChips' ∧
    VmCompleteReplacement host guestChips guestChips'
-- ANCHOR_END: vmEquivalent

/-- If `guestChips` fit the backend's degree bound, then so do `guestChips'`.

    Analog of `optimizerRespectsDegreeBound`.

    We'll have to prove that the optimizer meets this. -/
def PreservesDegree (b : DegreeBound) (guestChips guestChips' : Guest p) : Prop :=
  (∀ c ∈ guestChips, c.withinDegree b) → ∀ c ∈ guestChips', c.withinDegree b
