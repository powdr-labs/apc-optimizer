import ApcOptimizer.Implementation.OptimizerPasses.FlagUnify

set_option autoImplicit false

/-! # Dense entailed nonlinear substitution — `flagFold` part A.
Impl-only (correctness in `Proofs/FxSubst.lean`); shares `flagUnify`'s pair-level machinery
(`DenseFuData`/`denseFuPairData?`/`DenseFUSeen`/`denseFuCandidates`) wholesale. Assembled with the
other `flagFold` sub-passes in `FlagFold.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Part A: the entailed nonlinear substitution (dense) -/

def denseIndicatorProdImpl (others : List VarId) (pt : List (VarId × ZMod p)) : DenseExpr p :=
  others.foldl (fun acc v =>
    if zmodIsOne (denseEnvOfFast pt v) then DenseExpr.mul acc (DenseExpr.var v)
    else DenseExpr.mul acc (DenseExpr.add (DenseExpr.const (zmodOneP p))
      (DenseExpr.mul (DenseExpr.const (zmodNegOneP p)) (DenseExpr.var v))))
    (DenseExpr.const (zmodOneP p))

/-- Boolean indicator product `∏ (v or 1−v)` selecting one point of the box. Heuristic data —
    the certificate validates its values pointwise, so the construction carries no proof. -/
def denseIndicatorProd (others : List VarId) (pt : List (VarId × ZMod p)) : DenseExpr p :=
  others.foldl (fun acc v =>
    if denseEnvOfFast pt v = 1 then DenseExpr.mul acc (DenseExpr.var v)
    else DenseExpr.mul acc (DenseExpr.add (DenseExpr.const 1)
      (DenseExpr.mul (DenseExpr.const (-1)) (DenseExpr.var v)))) (DenseExpr.const 1)

@[csimp] theorem denseIndicatorProd_eq_impl : @denseIndicatorProd = @denseIndicatorProdImpl := by
  funext q others pt
  simp [denseIndicatorProd, denseIndicatorProdImpl]

def denseBuildEImpl (d : DenseFuData p) (vy : VarId) : DenseExpr p :=
  let others := d.rxVars.eraseDups.filter (fun v => v != vy)
  d.pts.foldl (fun acc ptb =>
    if ptb.2 && zmodIsOne (denseEnvOfFast ptb.1 vy) then
      DenseExpr.add acc (denseIndicatorProd others ptb.1)
    else acc) (DenseExpr.const (zmodZeroP p))

/-- Interpolate the target's value over the survivor-side flags from the compatible points. -/
def denseBuildE (d : DenseFuData p) (vy : VarId) : DenseExpr p :=
  let others := d.rxVars.eraseDups.filter (fun v => v != vy)
  d.pts.foldl (fun acc ptb =>
    if ptb.2 && (denseEnvOfFast ptb.1 vy == 1) then
      DenseExpr.add acc (denseIndicatorProd others ptb.1)
    else acc) (DenseExpr.const 0)

@[csimp] theorem denseBuildE_eq_impl : @denseBuildE = @denseBuildEImpl := by
  funext q d vy
  simp [denseBuildE, denseBuildEImpl]

/-- Per-target certificate: `vy` is a Y-side flag, the candidate solution `E` mentions neither
    `vy` nor anything outside the survivor's payload, and at every offset-compatible point the
    target equals `E`. -/
def denseFxCheckWith (d : DenseFuData p) (E : DenseExpr p) (vy : VarId) : Bool :=
  decide (vy ∈ d.ryVars) && !(E.mentions vy) &&
  decide (E.vars.all (fun v => v ∈ d.rxVars ∨ v ∈ d.ryVars)) &&
  decide (E.vars.all (fun v => v ∈ d.payXVars)) &&
  d.pts.all (fun ptb => !ptb.2 || decide (denseEnvOfFast ptb.1 vy = E.eval (denseEnvOfFast ptb.1)))

/-- The full certificate, defined through the shared pair data `denseFuPairData?`. -/
def denseFxCheck (bs : BusSemantics p) (facts : BusFacts p bs)
    (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (biX biY : BusInteraction (DenseExpr p)) (x : VarId) (E : DenseExpr p)
    (vy : VarId) : Bool :=
  match denseFuPairData? bs facts domIdx biX biY x with
  | some d => denseFxCheckWith d E vy
  | none => false

/-! ## Fast scaled-check candidate generation

Heuristic: the scan's soundness never reads the candidate list (`denseFxLoop_sound` only uses it to
place a seen-entry's interaction in the system), so this carries no obligation. -/

@[inline] def ffPushVar (acc : Array VarId) (v : VarId) : Array VarId :=
  if acc.contains v then acc else acc.push v

/-- Distinct variables in first-occurrence order — `e.vars.eraseDups` with no intermediate list. -/
def ffVarsAcc : DenseExpr p → Array VarId → Array VarId
  | .const _, acc => acc
  | .var i, acc => ffPushVar acc i
  | .add a b, acc => ffVarsAcc b (ffVarsAcc a acc)
  | .mul a b, acc => ffVarsAcc b (ffVarsAcc a acc)

@[inline] def ffVars (e : DenseExpr p) : Array VarId := ffVarsAcc e #[]

/-- The coefficient of `x` in `e` — `DenseExpr.splitAt` with the remainder deleted, so reading a
    candidate's coefficient does not allocate a rebuilt copy of `e`. -/
def ffCoeffAt (x : VarId) : DenseExpr p → Option (ZMod p)
  | .const _ => some (zmodZeroP p)
  | .var y => if y == x then some (zmodOneP p) else some (zmodZeroP p)
  | .add a b =>
    match ffCoeffAt x a, ffCoeffAt x b with
    | some ca, some cb => some (zmodAddP ca cb)
    | _, _ => none
  | .mul a b =>
    if a.mentions x || b.mentions x then
      match a.constValue? with
      | some k => (ffCoeffAt x b).map (zmodMulP k)
      | none =>
        match b.constValue? with
        | some k => (ffCoeffAt x a).map (zmodMulP k)
        | none => none
    else some (zmodZeroP p)

/-- Scaled-check candidates of one interaction: each carrier variable of the first payload slot
    with a constant-coefficient decomposition, keyed by `(busId, slot-1 constant, k, x)` and
    pre-hashed for the `seen` buckets. A slot 0 with fewer than two distinct variables has an
    empty offset part for every carrier, so it is skipped before any per-variable work. -/
def ffFuCandidates (bi : BusInteraction (DenseExpr p)) :
    List (UInt64 × VarId × (Nat × Option (ZMod p) × ZMod p × VarId)) :=
  match bi.payload with
  | [] => []
  | O :: rest =>
    let vs := ffVars O
    if vs.size < 2 then []
    else
      let c1 := (rest.head?).bind DenseExpr.constValue?
      (vs.foldr (init := []) fun x acc =>
        match ffCoeffAt x O with
        | some k =>
          let key := (bi.busId, c1, k, x)
          (denseFuKeyHash key, x, key) :: acc
        | none => acc)

/-! ## The scan loop and the substitution pass (dense) -/

/-- Scan for matched scaled-check pairs and adopt every certified interpolation `vy := E`. -/
def denseFxLoop (bs : BusSemantics p) (facts : BusFacts p bs)
    (domIdx : Thunk (Std.HashMap VarId (List (DenseExpr p)))) :
    List (BusInteraction (DenseExpr p)) → Std.HashMap UInt64 (List (DenseFUSeen p)) →
      DenseSolved p → DenseSolved p
  | [], _, σ => σ
  | c :: rest, seen, σ =>
    let cands := ffFuCandidates c
    match cands.findSome? (fun xk =>
        (seen.getD xk.1 []).findSome? (fun e =>
          if e.key == xk.2.2 then some (e, xk.2.1) else none)) with
    | some ex =>
        -- pair-level work once per match; per-target checks share it (see `denseFxCheck`).
        -- `domIdx` is forced here and nowhere else: an invocation with no matched pair never
        -- builds the whole-constraint bucket.
        match denseFuPairData? bs facts domIdx.get ex.1.bi c ex.2 with
        | none =>
            denseFxLoop bs facts domIdx rest
              (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.2.1, xk.2.2⟩ : DenseFUSeen p)))) σ
        | some d =>
        let pairs := (d.ryVars.eraseDups.filter (fun v => !(v ∈ d.rxVars))).filterMap (fun vy =>
          let ev := denseBuildE d vy
          if denseFxCheckWith d ev vy then some (vy, ev) else none)
        denseFxLoop bs facts domIdx rest
          (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.2.1, xk.2.2⟩ : DenseFUSeen p))))
          (σ.insertAll pairs)
    | none =>
        denseFxLoop bs facts domIdx rest
          (denseFuInsertAll seen (cands.map (fun xk => (⟨c, xk.2.1, xk.2.2⟩ : DenseFUSeen p)))) σ

/-- Entailed nonlinear substitution. When two bus interactions match up to a scaled range check,
    a survivor-side flag `vy` is often pinned to an interpolation `E` over the other flags (e.g.
    `vy := f * g`); this certifies each such `vy := E` and substitutes it everywhere. Prime `p`
    only (re-checked at runtime); identity otherwise. -/
def denseFxSubstF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let σ := denseFxLoop bs facts
        (Thunk.mk (fun _ => denseVarBucket DenseExpr.vars d.algebraicConstraints))
        d.busInteractions ∅ DenseSolved.empty
    if σ.map.isEmpty then d else d.substF σ.fn
  else d

def denseFxSubstFHints (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : RecoveryMap p :=
  if pw.isPrime = true then
    let σ := denseFxLoop bs facts
        (Thunk.mk (fun _ => denseVarBucket DenseExpr.vars d.algebraicConstraints))
        d.busInteractions ∅ DenseSolved.empty
    if σ.map.isEmpty then .identity else .ofFn (substitutionHints σ.fn)
  else .identity

end ApcOptimizer.Dense
