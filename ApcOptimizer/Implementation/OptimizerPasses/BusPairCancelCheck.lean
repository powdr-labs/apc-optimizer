import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndex
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelLive

set_option autoImplicit false

/-! # Dense emitted-check acceptance for `busPairCancel`

The receive scan (`denseFirstMatchAt`), emitted byte checks (`denseMkByteCheck`/`denseMkBytePair`),
and the per-candidate acceptance test (`denseCheckCancel`). Impl-only; soundness in
`Proofs/BusPairCancelCheck.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The first indexed position after `i` on `busId` whose payload matches `S.payload` among still
    **live** positions (ascending); tombstoned positions are skipped, so it is the first live match. -/
def denseFirstMatchAt (M : Thunk (DenseEqConstraintMap p)) (arr : Array (BusInteraction (DenseExpr p)))
    (alive : Array Bool)
    (busId : Nat) (S : BusInteraction (DenseExpr p)) (i : Nat) : List Nat → Option Nat
  | [] => none
  | j :: rest =>
    if decide (i < j) && alive[j]?.getD false then
      match arr[j]? with
      | some R =>
        if decide (R.busId = busId) && densePayloadEntailedEq M S.payload R.payload then some j
        else denseFirstMatchAt M arr alive busId S i rest
      | none => denseFirstMatchAt M arr alive busId S i rest
    else denseFirstMatchAt M arr alive busId S i rest

/-- Single-value byte check on `e`, emitted through `spec` (multiplicity `1`). -/
def denseMkByteCheck (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.xorOp) e e (.const 0) }

/-- Packed pair byte check on `(e₁, e₂)`, emitted through `spec` (multiplicity `1`). -/
def denseMkBytePair (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.pairOp) e₁ e₂ (.const 0) }

/-- Certificate that an emitted check faithfully carries `R`'s byte obligation: on a `byteXorSpec`
    bus (bound `256`), multiplicity 1, self-check payload `(xorOp, e, e, 0)` for an `e` that is a
    declared byte slot of `R`. -/
def denseEmitOk (ops : DenseZModOps p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (busId : Nat) (shape : MemoryBusShape) (slots : List Nat)
    (R ck : BusInteraction (DenseExpr p)) : Bool :=
  match facts.byteXorSpec ck.busId with
  | none => false
  | some spec =>
    decide (spec.bound = 256) &&
    decide (ck.multiplicity = (.const ops.one : DenseExpr p)) &&
    (match spec.decode ck.payload with
     | some (op, o1, o2, r) =>
       decide (op = (.const spec.xorOp : DenseExpr p)) && decide (o1 = o2) &&
       decide (r = (.const ops.zero : DenseExpr p)) &&
       slots.any (fun slot =>
         decide (R.payload[slot]? = some o1) &&
         (match facts.slotBound busId (denseGetPreviousMult ops shape)
              (R.payload.map DenseExpr.constValue?) slot with
          | some b => decide (b ≤ 256)
          | none => false))
     | none => false)

/-- The declared byte slots of `R` whose payload entries the witnesses do not justify. -/
def denseUnjustifiedSlots (bound : Nat) (deep : Bool)
    (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : VarId → List (BusInteraction (DenseExpr p)))
    (fbasis : VarId → List (DenseLinExpr p × Nat))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : List Nat :=
  slots.filter (fun slot =>
    match R.payload[slot]? with
    | some e => !denseByteJustifiedW bound deep domIdx candsOf bs facts wits fbasis e
    | none => false)

/-- The per-candidate certificate: bus/multiplicity/payload of the pair, the emitted checks'
    certificates, and byte justification of `R`'s declared slots. The split equation and region
    tests are not re-checked here (the scan established them); the justification scan is last, so it
    only runs for already-matching candidates. -/
def denseCheckCancel (ops : DenseZModOps p) (deep : Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (M : Thunk (DenseEqConstraintMap p))
    (domIdx : Std.HashMap VarId (List (DenseExpr p))) (candsOf : VarId → List (DenseExpr p))
    (wits : VarId → List (BusInteraction (DenseExpr p)))
    (fbasis : VarId → List (DenseLinExpr p × Nat))
    (busId : Nat) (shape : MemoryBusShape) (slots : List Nat) (bound : Nat)
    (S R : BusInteraction (DenseExpr p))
    (checks : List (BusInteraction (DenseExpr p))) : Bool :=
  decide (S.busId = busId) && decide (R.busId = busId) &&
  decide (denseMultConst S = some (denseSetNewMult ops shape)) &&
    decide (denseMultConst R = some (denseGetPreviousMult ops shape)) &&
  densePayloadEntailedEq M S.payload R.payload &&
  checks.all (denseEmitOk ops bs facts busId shape slots R) &&
  denseRecvSlotsJustified bound deep domIdx candsOf bs facts wits fbasis slots R

end ApcOptimizer.Dense
