import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

-- `p` is the field characteristic; a prime, so `ZMod p` is a field.
variable {p : ℕ} [Fact p.Prime]

--------- Expressions ---------

/-- A circuit variable. -/
structure Variable where
  /-- The display name of the variable. -/
  name : String
  /-- The optional powdr variable ID. All variables mentioned in the input
      circuit are expected to have a powdr ID. The output circuit may contain
      newly introduced variables whose values can be derived from a valid
      assignment of the input circuit. -/
  powdrId? : Option Nat := none
  deriving DecidableEq, Repr

/-- An arithmetic expression over structured variables and field constants. -/
inductive Expression (p : ℕ) where
  /-- A constant field element. -/
  | const (n : ZMod p)
  /-- A reference to a variable. -/
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

-- ANCHOR: degree
/-- The multiplicative degree of an expression. -/
def Expression.degree : Expression p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add e1 e2 => max e1.degree e2.degree
  | .mul e1 e2 => e1.degree + e2.degree
-- ANCHOR_END: degree

/-- The variables occurring in an expression. -/
def Expression.vars : Expression p → List Variable
  | .const _ => []
  | .var x => [x]
  | .add e1 e2 => e1.vars ++ e2.vars
  | .mul e1 e2 => e1.vars ++ e2.vars

--------- Computation Methods ---------

/-- A method for computing a *derived* variable's value from other variables,
    mirroring powdr's `ComputationMethod`. For newly introduced variables, this
    is interpreted by powdr's witness generator. -/
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
/-- A list of derived variables paired with how to compute each, consumed by
    witness generation. -/
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

/-- Bounds on the multiplicative degree of a circuit's expressions. -/
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
  /-- Whether the receiving chip accepts this bus interaction message, i.e.
      sending it violates no constraint in *another* chip.
      A message that is *not* accepted is, for example, one contradicting a
      lookup table entry.
      Only consulted for messages with nonzero multiplicity. -/
  accepts (busInteractionMessage : BusInteraction (ZMod p)) : Prop
  /-- Whether sending this bus interaction message maintains the invariants on
      which soundness of the system depends.
      For example, a memory bus might have the invariant that all sent values
      must be in a certain range.
      Only consulted for messages with nonzero multiplicity. -/
  maintainsInvariants (busInteractionMessage : BusInteraction (ZMod p)) : Prop
  /-- A property on *stateful* bus messages with nonzero multiplicity.
      Completeness is only required for assignments whose stateful messages
      are `admissible`.
      One useful way to use this is to describe the semantics of memory buses,
      see `ApcOptimizer/MemoryBus.lean`. -/
  admissible (statefulBusMessages : List (BusInteraction (ZMod p))) : Prop

-- ANCHOR: busState
/-- A concrete bus interaction message: which bus, and the tuple sent. -/
abbrev BusMessage (p : ℕ) := Nat × List (ZMod p)

/-- The effect on the stateful buses: the *net* multiplicity each message is
    sent with. -/
abbrev BusState (p : ℕ) := BusMessage p → ZMod p
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
/-- The side effects of a circuit under a given assignment and bus semantics:
    the net multiplicity with which each tuple is sent to a *stateful* bus. -/
def Circuit.sideEffects (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : BusState p :=
  fun message =>
    ((circuit.busInteractions.map (fun bi => bi.eval assignment)).filter
      (fun m => busSemantics.isStateful m.busId &&
        decide ((m.busId, m.payload) = message))).map
      (fun m => m.multiplicity) |>.sum
-- ANCHOR_END: sideEffects

--------- Derived variables ---------

-- ANCHOR: methodForCover
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
-- ANCHOR_END: methodForCover

omit [Fact p.Prime] in
/- Support lemma, does not require audit. -/
theorem Derivations.methodFor_isSome (ds : Derivations p)
    {inputVars outputVars : List Variable} (h : ds.cover inputVars outputVars)
    {v : Variable} (hv : v ∈ outputVars) (hp : v.powdrId? = none) :
    (ds.methodFor v).isSome := by
  have hc := h v hv
  simp only [hp] at hc
  obtain ⟨cm, hcm, -⟩ := hc
  simp [hcm]

-- ANCHOR: witgen
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
    i.e., whether it satisfies all algebraic constraints and every active bus
    interaction message is accepted. -/
def Circuit.satisfies (circuit : Circuit p) (busSemantics : BusSemantics p)
    (assignment : Variable → ZMod p) : Prop :=
  (∀ c ∈ circuit.algebraicConstraints, c.eval assignment = 0) ∧
  (∀ bi ∈ circuit.busInteractions,
    let message := bi.eval assignment
    message.multiplicity ≠ 0 → busSemantics.accepts message)
-- ANCHOR_END: satisfies

-- ANCHOR: guaranteesInvariants
/-- Whether a circuit guarantees that all invariants are maintained under a
    given bus semantics. -/
def Circuit.guaranteesInvariants (circuit : Circuit p)
    (busSemantics : BusSemantics p) : Prop :=
  ∀ assignment, circuit.satisfies busSemantics assignment →
    ∀ bi ∈ circuit.busInteractions,
      let message := bi.eval assignment
      message.multiplicity ≠ 0 → busSemantics.maintainsInvariants message
-- ANCHOR_END: guaranteesInvariants

-- ANCHOR: isSoundReplacementOf
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
-- ANCHOR_END: isSoundReplacementOf

-- ANCHOR: isCompleteReplacementOf
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
-- ANCHOR_END: isCompleteReplacementOf

--------- Optimizer ------------

-- ANCHOR: optimizer
abbrev Optimizer (p : ℕ) := Circuit p → Circuit p × Derivations p
-- ANCHOR_END: optimizer

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
    (optimizer : Optimizer p) : Prop :=
  ∀ circuit : Circuit p,
    circuit.withinDegree b →
    (optimizer circuit).1.withinDegree b
-- ANCHOR_END: degreeBound

--------- Optimizer correctness ---------

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
