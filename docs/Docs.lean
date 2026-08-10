import VersoManual

import ApcOptimizer.Spec
import ApcOptimizer.MemoryBus
import ApcOptimizer.OpenVmSemantics
import ApcOptimizer.Sp1Semantics
import ApcOptimizer.Optimizer

import Docs.Bibliography
import Docs.Cite

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Docs
open Verso.Code.External

set_option pp.rawOnError true

-- Source for `{anchor …}` code blocks: real definition bodies extracted from the audited modules
-- (via their `-- ANCHOR:` comments). The default module is Spec; override per block with `(module := …)`.
set_option verso.exampleProject "."
set_option verso.exampleModule "ApcOptimizer.Spec"

-- Render signatures even where a field/theorem carries no docstring: for the audited theorems the
-- signature *is* the statement we want to show, and we do not add prose to the audited source.
set_option verso.docstring.allowMissing true

#doc (Manual) "`apc-optimizer`: A Verified Constraint-System Optimizer" =>
%%%
shortTitle := "apc-optimizer"
%%%

# Introduction

This document describes `apc-optimizer`{citeNum powdr_apc_compiler}[], a formally verified zkVM circuit optimizer. `apc-optimizer` is a core component in the powdr autoprecompiles{citeNum powdr_autoprecompiles}[] pipeline.

# Background: zkVMs and autoprecompiles

zkVMs such as OpenVM{citeNum openVM}[], SP1{citeNum sp1}[], or powdr WASM{citeNum powdr_wasm}[] are virtual machines that output a cryptographic proof that a program executed correctly. They differ in the instruction sets they emulate but use the same underlying primitives: collections of _circuits_ communicating via shared _buses_.

Each circuit is responsible for one or more instructions in the instruction set and is defined by a set of _constraints_ over a _prime field_. Buses serve two purposes:
- They implement _lookups_ into precomputed tables. For example, a byte range check might be implemented by proving that a circuit variable's value is in a size-256 table of all bytes.
- They implement _stateful communication_ between circuits. For example, a _memory_ is implemented via bus interactions.

_Autoprecompiles_ prove correct execution of an entire _basic block_, which is a sequence of assembly instructions that can only be entered at the first instruction and exited at the last. The initial circuit is compiled from the instruction circuits of the zkVM and the concrete assembly program by instantiating whatever circuits would have been used by the vanilla zkVM within one monolithic circuit:

![Autoprecompiles](autoprecompiles.svg)

Having all instructions within the same circuit enables various optimizations, typically shrinking the circuit size by a factor of 3–4. Examples of these optimizations include:
- *Inlining of constants*. For example, immediate values can be inlined directly, as they are known at compile time. In combination with constant propagation, this specializes the circuit to the concrete basic block being proved.
- *Memory optimizations*. When proving instruction-by-instruction, even temporary values are written to memory and read back. Within a monolithic circuit, these values can be accessed directly, avoiding the overhead of the memory argument. One consequence is that each register is accessed only once, regardless of how many instructions read or write it.
- *Gadget optimizations*. Circuits often contain repeated subcircuits that can be optimized for how they are used. An example is RISC-V's `SEQZ` pseudo-instruction, which sets the output register to 1 if the input is zero, and 0 otherwise. It expands to the `SLTIU` instruction (a less-than comparison) with immediate value 1. But there exists a more efficient circuit for this specific comparison than the general-purpose `SLTIU` circuit.

In the remainder of this document, we formalize the properties that an optimizer must satisfy to be considered _correct_.

# Variables, expressions and assignments

A {deftech}_variable_ is how the _runtime witness data_ is referenced in a circuit. Variables in the input circuit carry a _powdr ID_, while newly introduced variables do not.

{docstring Variable}

An {deftech}_expression_ is defined inductively as a constant, a variable, or the sum or product of two expressions.

{docstring Expression}

An {deftech}_assignment_ maps every variable to a concrete field value. An expression is _evaluated_ under an assignment by folding its constants, variables, sums, and products into a single field element.

```anchor exprEval
def Expression.eval (e : Expression p)
    (assignment : Variable → ZMod p) : ZMod p :=
  match e with
  | .const n => n
  | .var x => assignment x
  | .add e1 e2 => e1.eval assignment + e2.eval assignment
  | .mul e1 e2 => e1.eval assignment * e2.eval assignment
```

# Bus interactions

A {deftech}_bus interaction_ sends a _payload_ tuple to a bus, weighted by a _multiplicity_. Multiplicities are usually constrained to be $`1` (a _bus send_), $`-1` (a _bus receive_), or $`0` (no effect) in practice.

{docstring BusInteraction}

A circuit (defined below) contains a list of _symbolic bus interactions_ (i.e., elements of type `BusInteraction Expression`). For a concrete run of the zkVM, the circuit might be instantiated several times with different variable assignments. Evaluating the symbolic bus interactions under an assignment yields a list of _bus messages_ (i.e., elements of type `BusInteraction (ZMod p)`).

## Bus state

The {deftech}_bus state_ of a circuit instance is the _net_ effect it has on the buses, i.e., the net multiplicity each message is sent with:
```anchor busState
/-- A concrete bus interaction message: which bus, and the tuple sent. -/
abbrev BusMessage (p : ℕ) := Nat × List (ZMod p)

/-- The effect on the stateful buses: the *net* multiplicity each message is
    sent with. -/
abbrev BusState (p : ℕ) := BusMessage p → ZMod p
```

Buses must _balance globally_: summed over all circuit instances in the entire zkVM execution, the net multiplicity of each message must be zero. This is enforced by the zkVM's proving backend, typically employing a protocol such as logup {citeNum logup}[] {citeNum logupGKR}[].

## Stateful and stateless buses

In practice, buses fall into one of two categories:
- A {deftech}_stateless bus_ or {deftech}_lookup_ is one where _most_ circuits are constrained to only send messages with multiplicity $`1` or $`0`. To balance it, a dedicated circuit _receives_ messages with an unconstrained multiplicity. In this chip, the payload is fixed. Therefore, this implements a lookup: By sending to this bus, the prover proves that the sent payload is in the precommitted table.
- A {deftech}_stateful bus_ is one where the multiplicity can be $`1` or $`-1` in any circuit. This implements a stateful communication channel between circuits. An example of this is the _execution bridge_: Each instruction chip might _receive_ the current $`(pc, timestamp)` pair, and _send_ the next $`(pc', timestamp')` pair.

As we will see below, we require that the optimizer preserves the net effect on stateful buses.

## Memory

Most zkVMs implement a memory argument based on the _offline memory checking argument_ due to Blum et al. {citeNum blum}[]. They reduce memory consistency to a _multiset equality_ check, which is essentially implemented by the bus argument.

In short, each read or write memory access is implemented as a series of bus interactions:
- An $`(address, value, timestamp)` pair is _received_ from the memory bus.
- $`timestamp` is asserted to be _smaller than the current timestamp_. This is usually implemented via a limb decomposition and range checks via lookups.
- An updated $`(address, value', timestamp')` pair is _sent_ to the memory bus, with $`timestamp'` equal to the current timestamp. Also, in the case of a _read access_, $`value'` is asserted to be equal to $`value`.

In addition, there are circuits responsible for memory initialization and finalization. All in all, memory consistency is reduced to checking that the bus is balanced. Note that the send and receive directions might also be inverted.

As we will see below, we will assume that all circuits _including the circuit to be optimized_ adhere to the memory discipline. If this was not the case, the original zkVM would not be sound in the first place.

# Circuits

A {deftech}_circuit_ is simply a collection of algebraic constraints and symbolic bus interactions:

{docstring Circuit}

A circuit is satisfied under an assignment when all algebraic constraints evaluate to zero and every bus interaction message is accepted by the bus semantics:

```anchor satisfies
/-- Whether a circuit is satisfied under a given assignment and bus semantics,
    i.e., whether it satisfies all algebraic constraints and every active bus
    interaction message is accepted. -/
def Circuit.satisfies (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : Prop :=
  (∀ c ∈ circuit.algebraicConstraints, c.eval assignment = 0) ∧
  (∀ bi ∈ circuit.busInteractions,
    let message := bi.eval assignment
    message.multiplicity ≠ 0 → busSemantics.accepts message)
```

# Bus Semantics

Bus semantics capture the _zkVM-specific_ semantics of the buses.

{docstring BusSemantics}

Instances exist for OpenVM and SP1. For example, the OpenVM bus semantics defines the following:
- `isStateful`: The "execution bridge" and "memory" buses are stateful, while all other buses are stateless.
- `accepts`: For all lookups, this checks whether the given bus message is in the precomputed table. Also, since OpenVM's circuits maintain the invariant that only range-checked values are sent to the register and memory address spaces, a memory bus _receive_ checks that the received value is in the correct range.
- `maintainsInvariants`: Checks whether all multiplicities are $`1` for stateless buses, and $`1` or $`-1` for stateful buses. Also, for memory bus interactions, it checks that the values are in the correct range. This also applies to _sent_ values, ensuring that the optimized circuit does not violate the invariant mentioned above.
- `admissible`: All symbolic bus interactions to stateful buses are ordered by _time_. Also, we assume that register `x0` always returns `0`.

# Soundness

{deftech}_Soundness_ is arguably the most important property that must be guaranteed by the optimizer. Intuitively, it states that anything the optimized circuit accepts, the original would have accepted too, with the same effect on the rest of the system.

First, we define the side effects of a circuit under an assignment as the net effect it has on the stateful buses.

```anchor sideEffects
/-- The side effects of a circuit under a given assignment and bus semantics:
    the net multiplicity with which each tuple is sent to a *stateful* bus. -/
def Circuit.sideEffects (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => busSemantics.isStateful m.busId &&
        decide ((m.busId, m.payload) = message))).map
      (fun m => m.multiplicity) |>.sum
```

Second, we define that a circuit _guarantees invariants_ if, under any satisfying assignment, every bus interaction maintains the invariants of the bus semantics.

```anchor guaranteesInvariants
/-- Whether a circuit guarantees that all invariants are maintained under a
    given bus semantics. -/
def Circuit.guaranteesInvariants (circuit : Circuit p)
    (busSemantics : BusSemantics p) : Prop :=
  ∀ assignment, circuit.satisfies busSemantics assignment →
    ∀ bi ∈ circuit.busInteractions,
      let message := bi.eval assignment
      message.multiplicity ≠ 0 → busSemantics.maintainsInvariants message
```

Finally, we formalize what it means for an optimized circuit to be a sound replacement for an original circuit:

```anchor isSoundReplacementOf
/-- Whether an optimized circuit is a sound replacement for an original
    circuit. Informally, for any satisfying assignment of the optimized
    circuit, there exists a corresponding satisfying assignment of the original
    circuit *with equal side effects*. Also, the optimized circuit must
    maintain all invariants guaranteed by the original circuit. -/
def Circuit.isSoundReplacementOf (optimizedCircuit originalCircuit : Circuit p)
    (busSemantics : BusSemantics p) : Prop :=
  (∀ assignment, optimizedCircuit.satisfies busSemantics assignment →
    ∃ assignment', originalCircuit.satisfies busSemantics assignment' ∧
      optimizedCircuit.sideEffects busSemantics assignment =
        originalCircuit.sideEffects busSemantics assignment') ∧
  (originalCircuit.guaranteesInvariants busSemantics →
    optimizedCircuit.guaranteesInvariants busSemantics)
```

# Completeness

The {deftech}_completeness_ property ensures that for any valid zkVM execution, the prover _can_ construct a satisfying assignment for the optimized circuit.

## Admissible assignments

First, we define what it means for an assignment to be _admissible_ under a bus semantics. An assignment is admissible if all active stateful messages satisfy the bus semantics' `admissible` predicate:

```anchor admissible
/-- Whether a given assignment is admissible under the bus semantics. -/
def Circuit.admissible (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : Prop :=
  busSemantics.admissible
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide (m.multiplicity ≠ 0) && busSemantics.isStateful m.busId))
```

Completeness is only required for admissible assignments.

## Witness generation

Second, we need to guarantee that the prover can also compute a satisfying assignment for the optimized circuit. To this end, the optimizer emits a list of _derivations_, specified in a custom witness-generation IR:

{docstring ComputationMethod}

```anchor derivations
/-- A list of derived variables paired with how to compute each, consumed by
    witness generation. -/
abbrev Derivations (p : ℕ) := List (Variable × ComputationMethod p)
```

With the data structures in place, we can define a prescribed witness generation algorithm that we expect the prover to implement. The algorithm derives a valid assignment for the optimized circuit from a valid assignment for the input circuit. In essence, for each variable in the output circuit:
- If it is a powdr-ID variable, it is reused from the input assignment.
- If it is a derived variable, the optimizer must have emitted a computation method for it. The witness generation algorithm evaluates this method under the input assignment to compute the output variable's value.

For this to be well-defined, the derivations must _cover_ the output variables:

```anchor methodForCover
/-- The `ComputationMethod` witness generation uses for `v`. If `v` appears
    multiple times, the last derivation is returned; `none` if `v` has no
    derivation. -/
def Derivations.methodFor :
    Derivations p → Variable → Option (ComputationMethod p)
  | [], _ => none
  | (u, cm) :: rest, v =>
      match Derivations.methodFor rest v with
      -- If `v` is derived later, that derivation overrides this one.
      | some later => some later
      | none => if u = v then some cm else none

/-- Whether `ds` lets witness generation produce every element of `outputVars`
    from `inputVars`: each output variable is either an input variable (reused)
    or a derived variable with a method that reads only input variables. -/
def Derivations.cover (ds : Derivations p)
    (inputVars outputVars : List Variable) : Prop :=
  ∀ v ∈ outputVars,
    match v.powdrId? with
    | some _ => v ∈ inputVars
    | none => ∃ cm, ds.methodFor v = some cm ∧ ∀ x ∈ cm.vars, x ∈ inputVars
```

Witness generation generates an assignment as described above. It is only defined on the output circuit's variables, and it is guaranteed to be well-defined by the `cover` property.

```anchor witgen
/-- Witness generation on a variable `ds` covers. Every powdr-ID (input)
    variable passes through unchanged; every other variable is computed by the
    method `ds` records for it. -/
def Derivations.witgen (ds : Derivations p) {inputVars outputVars : List Variable}
    (h : ds.cover inputVars outputVars) (inputAssignment : Variable → ZMod p)
    (v : Variable) (hv : v ∈ outputVars) : ZMod p :=
  match hp : v.powdrId? with
  -- Well-defined: by the `some` branch of `Derivations.cover`, a powdr-ID
  -- variable of the output circuit also exists in the input circuit.
  | some _ => inputAssignment v
  | none => ((ds.methodFor v).get (ds.methodFor_isSome h hv hp)).eval inputAssignment
```

## The full completeness property

Putting the pieces together, we define what it means for an optimized circuit to be a _complete_ replacement for an original circuit. Structurally, the returned derivations must contain no unused entries and must cover every output variable from the input variables. Semantically, every admissible satisfying input assignment must produce a satisfying and admissible output assignment with equal side effects.

```anchor isCompleteReplacementOf
/-- Whether an optimized circuit is a complete replacement for an original circuit. -/
def Circuit.isCompleteReplacementOf
    (optimizedCircuit originalCircuit : Circuit p)
    (busSemantics : BusSemantics p) (ds : Derivations p) : Prop :=

  -- ASSUMPTION: every variable in the original circuit has a powdr ID.
  (∀ v ∈ originalCircuit.vars, v.powdrId?.isSome) →

  -- `ds` does not contain unused derivations.
  (∀ derivation ∈ ds, derivation.1 ∈ optimizedCircuit.vars) ∧

  -- The optimized circuit variables can be derived from the original circuit
  -- variables, and the return derivations.
  ∃ hcover : ds.cover originalCircuit.vars optimizedCircuit.vars,

  -- For any admissible satisfying assignment of the original circuit, the
  -- optimized circuit is also satisfied and admissible, with equal side
  -- effects, under the assignment produced by witness generation.
  ∀ assignment,
    originalCircuit.admissible busSemantics assignment →
    originalCircuit.satisfies busSemantics assignment →
    ∀ assignment' : Variable → ZMod p,
    (∀ v (hv : v ∈ optimizedCircuit.vars),
      assignment' v = ds.witgen hcover assignment v hv) →
    optimizedCircuit.satisfies busSemantics assignment' ∧
      optimizedCircuit.admissible busSemantics assignment' ∧
      originalCircuit.sideEffects busSemantics assignment =
        optimizedCircuit.sideEffects busSemantics assignment'
```

# Degree bound

The {deftech}_multiplicative degree_ of an expression is defined structurally: constants have degree 0, variables have degree 1, addition takes the maximum, and multiplication adds the degrees.
```anchor degree
/-- The multiplicative degree of an expression. -/
def Expression.degree : Expression p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add e1 e2 => max e1.degree e2.degree
  | .mul e1 e2 => e1.degree + e2.degree
```

A {deftech}_degree bound_ specifies the maximum multiplicative degrees allowed for algebraic constraints and bus interactions. The proving backend enforces these bounds, so the optimizer must respect them: a within-bound input yields a within-bound output.

{docstring DegreeBound}

Given a zkVM-specific degree bound and an optimizer, we state what it means for the optimizer to respect the bound: For any input circuit that is within the bound, the output circuit must also be within the bound.

```anchor degreeBound
/-- Whether a circuit stays within a degree bound. -/
def Circuit.withinDegree (circuit : Circuit p) (b : DegreeBound) : Prop :=
  (∀ c ∈ circuit.algebraicConstraints, c.degree ≤ b.identities) ∧
  (∀ bi ∈ circuit.busInteractions,
    bi.multiplicity.degree ≤ b.busInteractions ∧
      ∀ e ∈ bi.payload, e.degree ≤ b.busInteractions)

/-- Whether an optimizer respects a degree bound: a within-bound input always
    yields a within-bound output. -/
def optimizerRespectsDegreeBound (b : DegreeBound)
    (optimizer : Circuit p → Circuit p × Derivations p) : Prop :=
  ∀ circuit : Circuit p,
    circuit.withinDegree b →
    (optimizer circuit).1.withinDegree b
```

# Optimizer

Putting the pieces together, we define what it means for an optimizer to be _correct_. An {deftech}_optimizer_ is a function that maps a circuit to a new circuit and a list of derivations.

```anchor optimizer
abbrev Optimizer (p : ℕ) := Circuit p → Circuit p × Derivations p
```

An optimizer is correct if, for every input circuit, replacing it with the optimized circuit is both sound and complete, and the optimizer respects the degree bound.

```anchor isCorrect
/-- An optimizer is correct if, for every input circuit, replacing it with the
    optimized circuit is both sound and complete, and the optimizer respects
    the degree bound `b`. -/
def Optimizer.isCorrect (optimizer : Optimizer p)
    (busSemantics : BusSemantics p) (b : DegreeBound) : Prop :=
  (∀ originalCircuit : Circuit p,
    let (optimizedCircuit, derivations) := optimizer originalCircuit
    (optimizedCircuit.isSoundReplacementOf originalCircuit busSemantics) ∧
    (optimizedCircuit.isCompleteReplacementOf originalCircuit busSemantics
      derivations))
  ∧ optimizerRespectsDegreeBound b optimizer
```
