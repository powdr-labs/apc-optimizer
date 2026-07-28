import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

-- `p` is the field characteristic; a prime, so `ZMod p` is a field.
variable {p : ℕ} [Fact p.Prime]

--------- Expressions ---------

/-- A circuit variable. -/
structure Variable where
  /-- The _unique_ name of the variable. -/
  name : String
  /-- The optional powdr variable ID. All variables mentioned in the input
      circuit are expected to have a powdr ID. The output circuit may contain
      newly introduced variables whose values can be derived from a valid
      assignment of the input circuit. -/
  powdrId? : Option Nat := none
  deriving DecidableEq, Repr

instance : BEq Variable := ⟨fun a b => decide (a = b)⟩

/-- An arithmetic expression over structured variables and field constants. -/
inductive Expression (p : ℕ) where
  /-- A constant field element. -/
  | const (n : ZMod p)
  /-- A variable reference. -/
  | var (x : Variable)
  /-- The sum of two expressions. -/
  | add (e1 e2 : Expression p)
  /-- The product of two expressions. -/
  | mul (e1 e2 : Expression p)

/-- Evaluate an expression under an `assignment` of variables to field
    elements. -/
-- ANCHOR: exprEval
def Expression.eval (e : Expression p)
    (assignment : Variable → ZMod p) : ZMod p :=
  match e with
  | .const n => n
  | .var x => assignment x
  | .add e1 e2 => e1.eval assignment + e2.eval assignment
  | .mul e1 e2 => e1.eval assignment * e2.eval assignment
-- ANCHOR_END: exprEval

/-- The multiplicative degree of an expression. -/
def Expression.degree : Expression p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add e1 e2 => max e1.degree e2.degree
  | .mul e1 e2 => e1.degree + e2.degree

/-- The variables occurring in an expression. -/
def Expression.vars : Expression p → List Variable
  | .const _ => []
  | .var x => [x]
  | .add e1 e2 => e1.vars ++ e2.vars
  | .mul e1 e2 => e1.vars ++ e2.vars

--------- Computation Methods ---------

/-- A method for computing a *derived* variable's value from other variables,
    mirroring powdr's `ComputationMethod`. For newly introduced variables, this
    is interpreted by powdr's witness generator.
    `quotientOrZero num den` is `num / den` in the field, or `0` when
    `den = 0`; `ifEqZero cond thenM elseM` picks `thenM` when `cond` evaluates
    to `0`, else `elseM`. -/
inductive ComputationMethod (p : ℕ) where
  /-- A constant value. -/
  | const (c : ZMod p)
  /-- The quotient of two expressions, or zero if the denominator is zero. -/
  | quotientOrZero (num den : Expression p)
  /-- Conditional computation: if `cond` evaluates to zero, use `thenM`, else
      use `elseM`. -/
  | ifEqZero (cond : Expression p) (thenM elseM : ComputationMethod p)

/-- Evaluate a computation method under an assignment (cf. powdr's
    `evaluate_computation_method`). -/
def ComputationMethod.eval :
    ComputationMethod p → (Variable → ZMod p) → ZMod p
  | .const c, _ => c
  | .quotientOrZero num den, assignment =>
      if den.eval assignment = 0 then 0
      else (den.eval assignment)⁻¹ * num.eval assignment
  | .ifEqZero cond thenM elseM, assignment =>
      if cond.eval assignment = 0 then thenM.eval assignment
      else elseM.eval assignment

/-- The variables a computation method may read. -/
def ComputationMethod.vars : ComputationMethod p → List Variable
  | .const _ => []
  | .quotientOrZero num den => num.vars ++ den.vars
  | .ifEqZero cond thenM elseM => cond.vars ++ thenM.vars ++ elseM.vars

-- ANCHOR: derivations
/-- A list of derived variables paired with how to compute each, in order — the
    extra output of the optimizer, consumed by witness generation. -/
abbrev Derivations (p : ℕ) := List (Variable × ComputationMethod p)
-- ANCHOR_END: derivations

--------- Bus Interactions ---------

/-- A bus interaction. Typically, α is
    - an expression (_symbolic bus interaction_), or
    - a field element (_bus interaction message_). -/
structure BusInteraction (α : Type) where
  /-- The ID of the bus this interaction is for. Distinct buses cannot
      interact. -/
  busId : Nat
  /-- The multiplicity with which the message is sent to the bus. -/
  multiplicity : α
  /-- The payload of the bus interaction. -/
  payload : List α

/-- Evaluate a bus interaction under an `assignment`, turning a symbolic bus
    interaction into a bus interaction message. -/
def BusInteraction.eval (bi : BusInteraction (Expression p))
    (assignment : Variable → ZMod p) : BusInteraction (ZMod p) :=
  { busId := bi.busId,
    multiplicity := bi.multiplicity.eval assignment,
    payload := bi.payload.map (fun e => e.eval assignment) }

/-- Bound on the multiplicative degree of a circuit's expressions. -/
structure DegreeBound where
  /-- The maximum multiplicative degree of the algebraic constraints. -/
  identities : Nat
  /-- The maximum multiplicative degree of the bus interactions. -/
  busInteractions : Nat

/-- The bus semantics of the zkVM. -/
structure BusSemantics (p : ℕ) where
  /-- Whether the bus of the given ID changes the state of the VM.
      Stateless bus interactions are typically lookups. -/
  isStateful (busId : Nat) : Bool
  /-- Whether sending this bus interaction message violates a constraint in
      *another* chip.
      An example of this is sending a message that conflicts with a lookup
      table entry. -/
  violatesConstraint (busInteractionMessage : BusInteraction (ZMod p)) : Bool
  /-- Whether sending this bus interaction message breaks an invariant on which
      soundness of the system depends.
      For example, a memory bus might have the invariant that all sent values
      must be in a certain range. -/
  breaksInvariant (busInteractionMessage : BusInteraction (ZMod p)) : Bool
  /-- A property on *stateful* bus messages with nonzero multiplicity.
      Completeness is only required for assignments whose stateful messages
      are `admissible`.
      One useful way to use this is to describe the semantics of memory buses,
      see ``ApcOptimizer/MemoryBus.lean``. -/
  admissible (statefulBusMessages : List (BusInteraction (ZMod p))) : Prop

-- ANCHOR: busState
/-- A concrete bus interaction message: which bus, and the tuple sent. -/
abbrev BusMessage (p : ℕ) := Nat × List (ZMod p)

/-- The effect on the stateful buses: the messages sent, each with a
    multiplicity. -/
abbrev BusState (p : ℕ) := List (BusMessage p × ZMod p)

/-- The net multiplicity with which `message` is sent in `state`. -/
def multiplicitySum (message : BusMessage p) (state : BusState p) : ZMod p :=
  match state with
  | [] => 0
  | (msg, mult) :: tl =>
      (if msg = message then mult else 0) + multiplicitySum message tl

/-- Two bus states are equal when every message is sent with the same net
    multiplicity. -/
instance : HasEquiv (BusState p) :=
  ⟨fun s t => ∀ message, multiplicitySum message s = multiplicitySum message t⟩
-- ANCHOR_END: busState

--------- Circuit ---------

/-- A circuit representing a single zkVM chip. -/
structure Circuit (p : ℕ) where
  /-- The list of algebraic constraints. For an assignment to be valid, all
      of them must evaluate to zero. -/
  algebraicConstraints : List (Expression p)
  /-- The list of symbolic bus interactions. These include both the stateless
      bus interactions (lookups) and the stateful bus interactions. -/
  busInteractions : List (BusInteraction (Expression p))

/-- The variables occurring anywhere in a circuit. -/
def Circuit.vars (circuit : Circuit p) : List Variable :=
  circuit.algebraicConstraints.flatMap Expression.vars ++
    circuit.busInteractions.flatMap
      (fun bi => bi.multiplicity.vars ++ bi.payload.flatMap Expression.vars)

-- ANCHOR: sideEffects
/-- The side effects of a circuit under a given assignment and bus semantics.
    The side effects are the tuples sent to the *stateful* buses. -/
def Circuit.sideEffects (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : BusState p :=
  circuit.busInteractions.filter (fun bi => busSemantics.isStateful bi.busId)
    |>.map (fun bi =>
      let m := bi.eval assignment
      ((m.busId, m.payload), m.multiplicity))
-- ANCHOR_END: sideEffects

--------- Derived variables ---------

/-- The `ComputationMethod` witness generation uses for `v`: the **last** one
    `ds` lists for it (later derivations override earlier ones), or `none` if
    `v` is not derived. -/
def Derivations.methodFor :
    Derivations p → Variable → Option (ComputationMethod p)
  | [], _ => none
  | (u, cm) :: rest, v =>
      (Derivations.methodFor rest v).orElse
        (fun _ => if u = v then some cm else none)

-- ANCHOR: witgen
/-- Whether `ds` lets witness generation produce every element of `outputVars`
    from `inputVars`: each output variable is either an input variable (reused)
    or a derived variable with a method that reads only input variables. -/
def Derivations.cover (ds : Derivations p)
    (inputVars outputVars : List Variable) : Prop :=
  ∀ v ∈ outputVars,
    match v.powdrId? with
    | some _ => v ∈ inputVars
    | none => ∃ cm, ds.methodFor v = some cm ∧ ∀ x ∈ cm.vars, x ∈ inputVars

/-- Witness generation: reconstruct an output assignment from an input
    assignment. Every powdr-ID (input) variable passes through unchanged; every
    other variable is computed by the method `ds` records for it, read from the
    input variables. This is what powdr runs to fill the optimized circuit's
    variables from an input trace. -/
def Derivations.witgen (ds : Derivations p)
    (inputAssignment : Variable → ZMod p) : Variable → ZMod p :=
  fun v =>
    match v.powdrId? with
    -- Note that by `Derivations.cover`, if `v` appears in the output circuit,
    -- it must also exist in the input circuit, so this case is always
    -- well-defined.
    | some _ => inputAssignment v
    | none =>
      match Derivations.methodFor ds v with
      | some cm => cm.eval inputAssignment
      -- Note that by `Derivations.cover`, if `v` appears in the output
      -- circuit, this case is impossible.
      | none => inputAssignment v
-- ANCHOR_END: witgen

--------- Circuit implications ---------

-- ANCHOR: admissible
/-- Whether a given assignment is admissible under the bus semantics. -/
def Circuit.admissible (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : Prop :=
  busSemantics.admissible
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => decide (m.multiplicity ≠ 0) && busSemantics.isStateful m.busId))
-- ANCHOR_END: admissible

-- ANCHOR: satisfies
/-- Whether a circuit is satisfied under a given assignment and bus semantics,
    i.e., whether it satisfies all algebraic constraints and does not violate
    any bus constraints. -/
def Circuit.satisfies (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : Prop :=
  (∀ c ∈ circuit.algebraicConstraints, c.eval assignment = 0) ∧
  (∀ bi ∈ circuit.busInteractions,
    let message := bi.eval assignment
    message.multiplicity ≠ 0 → busSemantics.violatesConstraint message = false)
-- ANCHOR_END: satisfies

-- ANCHOR: guaranteesInvariants
/-- Whether a circuit guarantees that all invariants are maintained under a
    given bus semantics. -/
def Circuit.guaranteesInvariants (circuit : Circuit p)
    (busSemantics : BusSemantics p) : Prop :=
  ∀ assignment, circuit.satisfies busSemantics assignment →
    ∀ bi ∈ circuit.busInteractions,
      let message := bi.eval assignment
      message.multiplicity ≠ 0 → busSemantics.breaksInvariant message = false
-- ANCHOR_END: guaranteesInvariants

-- ANCHOR: isSoundReplacementOf
/-- Whether an optimized circuit is a sound replacement for an original
    circuit. Informally, for any satisfying assignment of the optimized
    circuit, there exists a corresponding satisfying assignment of the original
    circuit *with equivalent side effects*. Also, the optimized circuit must
    maintain all invariants guaranteed by the original circuit. -/
def Circuit.isSoundReplacementOf (optimizedCircuit originalCircuit : Circuit p)
    (busSemantics : BusSemantics p) : Prop :=
  (∀ assignment, optimizedCircuit.satisfies busSemantics assignment →
    ∃ assignment', originalCircuit.satisfies busSemantics assignment' ∧
      optimizedCircuit.sideEffects busSemantics assignment ≈
        originalCircuit.sideEffects busSemantics assignment') ∧
  (originalCircuit.guaranteesInvariants busSemantics →
    optimizedCircuit.guaranteesInvariants busSemantics)
-- ANCHOR_END: isSoundReplacementOf

-- ANCHOR: isCompleteReplacementOf
/-- Whether an optimized circuit is a complete replacement for an original one. -/
def Circuit.isCompleteReplacementOf
    (optimizedCircuit originalCircuit : Circuit p)
    (busSemantics : BusSemantics p) (ds : Derivations p) : Prop :=
  -- ASSUMPTION: every variable in the original circuit has a powdr ID.
  (∀ v ∈ originalCircuit.vars, v.powdrId?.isSome) →
  -- `ds` does not contain unused derivations.
  (∀ derivation ∈ ds, derivation.1 ∈ optimizedCircuit.vars) ∧
  -- The optimized circuit variables can be derived from the original circuit
  -- variables, and the return derivations.
  ds.cover originalCircuit.vars optimizedCircuit.vars ∧
  -- For any admissible satisfying assignment of the original circuit, the
  -- optimized circuit is also satisfied and admissible, with equivalent side
  -- effects, under the assignment produced by witness generation.
  ∀ assignment,
    originalCircuit.admissible busSemantics assignment →
    originalCircuit.satisfies busSemantics assignment →
    let assignment' := Derivations.witgen ds assignment
    optimizedCircuit.satisfies busSemantics assignment' ∧
      optimizedCircuit.admissible busSemantics assignment' ∧
      originalCircuit.sideEffects busSemantics assignment ≈
        optimizedCircuit.sideEffects busSemantics assignment'
-- ANCHOR_END: isCompleteReplacementOf

--------- Degree bound ---------

-- ANCHOR: degreeBound
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
-- ANCHOR_END: degreeBound

--------- Optimizer correctness ---------

-- ANCHOR: optimizer
abbrev Optimizer (p : ℕ) := Circuit p → Circuit p × Derivations p
-- ANCHOR_END: optimizer

-- ANCHOR: isCorrect
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
-- ANCHOR_END: isCorrect
