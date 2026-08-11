import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Implementation.BusFacts
import ApcOptimizer.Utils.Size
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

/-! # Fact-aware verified passes

A `VerifiedPassW` is a `VerifiedPass` that may additionally consult proven `BusFacts`
(`Implementation/BusFacts.lean`). The `PassCorrect` obligation is unchanged; facts only widen what
a pass can decide, never what it may claim (with `BusFacts.trivial` behavior is fact-free). -/

variable {p : ℕ}

/-- A proof-carrying pass that may consult proven facts about the bus semantics. -/
abbrev VerifiedPassW (p : ℕ) :=
  (cs : OutputCircuit p) → (bs : BusSemantics p) → (facts : BusFacts p bs) → PassResult cs bs

deriving instance DecidableEq for BusInteraction

/-! ## The lexicographic size key

`(#distinct variables, #bus interactions, #algebraic constraints)`, variables most significant —
the optimizer's effectiveness priority. -/

/-- Number of distinct variables via a `HashSet` (linear); same value as `OutputCircuit.size`,
    used only for the loop measure. -/
def OutputCircuit.varCount (cs : OutputCircuit p) : Nat :=
  ((cs.algebraicConstraints.flatMap ExpressionG.vars ++
      cs.busInteractions.flatMap BusInteraction.vars).foldl
        (init := (∅ : Std.HashSet OutputVariable)) (·.insert ·)).size

/-- The lexicographic size key `(#distinct vars, #bus interactions, #constraints)`. Well-founded
    under `<`, so it serves as the fixpoint termination measure. -/
def OutputCircuit.sizeKey (cs : OutputCircuit p) : Nat ×ₗ Nat ×ₗ Nat :=
  toLex (cs.varCount, toLex (cs.busInteractions.length, cs.algebraicConstraints.length))

/-! ## Degree guarding

Each pass is wrapped in a checked guard that falls back to its unchanged input if the output would
exceed the degree bound; `RespectsDeg` propagates through composition and iteration. -/

/-- A pass never pushes a within-bound system past the degree bound `b`. -/
def RespectsDeg (b : DegreeBound) (f : VerifiedPassW p) : Prop :=
  ∀ (cs : OutputCircuit p) (bs : BusSemantics p) (facts : BusFacts p bs),
    cs.withinDegree b → (f cs bs facts).out.withinDegree b
