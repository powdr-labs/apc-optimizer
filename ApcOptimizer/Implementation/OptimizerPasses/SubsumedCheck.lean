import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify

set_option autoImplicit false

/-! # Dense subsumed bound-check removal

Runtime definitions for the subsumed-check droppers; the passes are wrapped in
`Proofs/SubsumedCheck.lean`. One generic base/keep/filter skeleton (`denseSubsumedDropF`),
instantiated by a recognizer returning the checked variable and the bound whose entailment makes
the check droppable. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Recognise a pure single-value range check (`facts.rangeCheckAt`) at multiplicity `1` whose
    value slot holds a bare variable: the checked variable and its bound. -/
def denseSubsumedCheckOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (VarId × Nat) :=
  match facts.rangeCheckAt bi.busId (bi.payload.map DenseExpr.constValue?) with
  | some (valSlot, bound) =>
    if bi.multiplicity = DenseExpr.const 1 then
      match bi.payload[valSlot]? with
      | some (DenseExpr.var x) => some (x, bound)
      | _ => none
    else none
  | none => none

/-- Recognise a single-variable range check `[x, width]` (multiplicity `1`) on a `varRangeBus`
    bus whose width is a *satisfiable* constant (`width.val ≤ 17`): the checked variable and the
    bound `2 ^ width`. -/
def denseSubsumedRangeCheck? (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : Option (VarId × Nat) :=
  match bi.payload with
  | [v, c] =>
    match v with
    | DenseExpr.var x =>
      match c.constValue? with
      | some cv =>
        if facts.varRangeBus bi.busId = true ∧ bi.multiplicity = DenseExpr.const 1
            ∧ cv.val ≤ 17 then some (x, 2 ^ cv.val) else none
      | none => none
    | _ => none
  | _ => none

/-- The justification base: interactions the pass can never drop (not recognised by `f`). -/
def denseSubsumedDropBase (f : BusInteraction (DenseExpr p) → Option (VarId × Nat))
    (d : DenseConstraintSystem p) : List (BusInteraction (DenseExpr p)) :=
  d.busInteractions.filter (fun bi => (f bi).isNone)

/-- Keep `bi` unless it is a recognised check whose variable is already bounded `< B` by a
    retained (base) interaction. -/
def denseSubsumedDropKeep (bs : BusSemantics p) (facts : BusFacts p bs)
    (f : BusInteraction (DenseExpr p) → Option (VarId × Nat))
    (base : List (BusInteraction (DenseExpr p))) (bi : BusInteraction (DenseExpr p)) : Bool :=
  match f bi with
  | some (x, B) =>
    match denseFindVarBound bs facts base x with
    | some b' => !decide (b' ≤ B)
    | none => true
  | none => true

/-- Drops an `f`-recognised bound check on `x` when `x` is already bounded at least as tightly by
    a retained check (wired as `denseSubsumedCheckDropPass` / `denseSubsumedRangeDropPass`). -/
def denseSubsumedDropF (bs : BusSemantics p) (facts : BusFacts p bs)
    (f : BusInteraction (DenseExpr p) → Option (VarId × Nat))
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  d.filterBus (denseSubsumedDropKeep bs facts f (denseSubsumedDropBase f d))

/-! ## Indexed bound lookups (runtime twin)

`denseSubsumedDropKeep` walks the whole `base` list for every recognised check, so the pass is
`O(checks × interactions)`. A bound can only come from an interaction that mentions the variable
(`denseInteractionBound` needs a payload slot holding literally `.var x`), so serving the query from
a per-variable index returns the identical first match — `denseSubsumedDropF_eq_fast`
(`Proofs/SubsumedCheck.lean`) proves it and installs the twin via `@[csimp]`. -/

/-- `denseSubsumedDropKeep` with the justification base served from a per-variable index. -/
def denseSubsumedDropKeepIdx (bs : BusSemantics p) (facts : BusFacts p bs)
    (f : BusInteraction (DenseExpr p) → Option (VarId × Nat))
    (witsOf : VarId → List (BusInteraction (DenseExpr p)))
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  match f bi with
  | some (x, B) =>
    match denseFindVarBound bs facts (witsOf x) x with
    | some b' => !decide (b' ≤ B)
    | none => true
  | none => true

/-- `denseSubsumedDropF` with one index build per invocation. The index is passed as a value with
    the lookup applied at the use site; a partial application stored elsewhere would rebuild it per
    query (`agent-docs/log.md` entries 106, 143). -/
def denseSubsumedDropFFast (bs : BusSemantics p) (facts : BusFacts p bs)
    (f : BusInteraction (DenseExpr p) → Option (VarId × Nat))
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let witsIdx := denseVarBucket denseBIVars (denseSubsumedDropBase f d)
  d.filterBus (denseSubsumedDropKeepIdx bs facts f (denseVarBucketLookup witsIdx))

end ApcOptimizer.Dense
