import ApcOptimizer.Implementation.OptimizerPasses.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.ListSplit
import ApcOptimizer.Implementation.OptimizerPasses.SearchBudgets

set_option autoImplicit false

/-! # Dense byte-justification certificates for `busPairCancel`

Runtime-only certificates for deciding whether an expression is provably a byte (`< 256`) or
otherwise bounded, used by the byte-justified drops. A leaf file — definitions only, no soundness
lemma (that lives in `Proofs/BusPairCancelJustify.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The expression's single distinct variable: `some (some v)` when exactly `v` occurs, `some none`
    when no variable occurs, `none` when several distinct variables occur. -/
def DenseExpr.singleVarAux : DenseExpr p → Option (Option VarId)
  | .const _ => some none
  | .var y => some (some y)
  | .add a b | .mul a b =>
    match a.singleVarAux, b.singleVarAux with
    | some none, r => r
    | r, some none => r
    | some (some u), some (some v) => if u == v then some (some u) else none
    | _, _ => none

/-- Is the expression a single-variable expression (exactly one distinct variable)? -/
def DenseExpr.isSingleVar (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some _) => true
  | _ => false

/-- Per-point core of the deep justification: with the `keys` of `c` pinned by `pt`, the substituted
    and folded constraint must be linear and, once normalized, either pin `x` to a re-checked byte
    constant or equate it to a variable in the precomputed `byteVars`. -/
def densePointByteOk (x : VarId) (c : DenseExpr p) (byteVars : List VarId)
    (keys : List VarId) (pt : List (VarId × ZMod p)) : Bool :=
  match denseLinearize ((c.substF (fun v =>
      if keys.contains v then some (.const (denseEnvOfFast pt v)) else none)).fold) with
  | none => false
  | some l =>
    let ln := DenseLinExpr.norm l
    match ln.terms with
    | [(v, a)] =>
      decide (v = x) && decide (a ≠ 0) &&
        decide (a * (-(a⁻¹ * ln.const)) + ln.const = 0) &&
        decide ((-(a⁻¹ * ln.const) : ZMod p).val < 256)
    | [(v1, a1), (v2, a2)] =>
      decide (ln.const = 0) &&
      (if v1 = x then
        decide (a2 = -a1) && decide (a1 ≠ 0) && byteVars.contains v2
       else if v2 = x then
        decide (a1 = -a2) && decide (a2 ≠ 0) && byteVars.contains v1
       else false)
    | _ => false

/-- The variables of `c` (other than `x`) with a proven byte bound from the remaining interactions —
    computed once per candidate, not once per enumeration point. -/
def denseDeepByteVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) (c : DenseExpr p) :
    List VarId :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filter (fun v =>
    match denseFindVarBound bs facts (wits v) v with
    | some b => decide (b ≤ 256)
    | none => false)

/-- The variables of `c` other than `x` that carry a small proven *constraint-derived* finite domain
    (selector flags) — the candidates for enumeration in the deep justification. -/
def denseDeepEnumDoms (domIdx : Std.HashMap VarId (List (DenseExpr p))) (x : VarId)
    (c : DenseExpr p) :
    List (VarId × List (ZMod p)) :=
  (c.vars.dedup.filter (fun v => v ≠ x)).filterMap (fun v =>
    match denseFindDomainAlg (denseVarBucketLookup domIdx v) v with
    | some d => if d.length ≤ maxDeepDomain then some (v, d) else none
    | none => none)

/-- Deep byte bound for `x` from one constraint `c`: enumerate the small proven finite domains of
    `c`'s other variables (e.g. one-hot selector flags) and require `densePointByteOk` at every
    point. -/
def denseDeepBoundOk (domIdx : Std.HashMap VarId (List (DenseExpr p))) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId)
    (c : DenseExpr p) : Bool :=
  let enum := denseDeepEnumDoms domIdx x c
  if (c.vars.dedup.filter (fun v => v ≠ x)).length ≤ maxDeepVars &&
      (enum.map (fun vd => vd.2.length)).prod ≤ maxDeepPoints then
    (denseAssignments enum).all
      (densePointByteOk x c (denseDeepByteVars bs facts wits x c) (enum.map Prod.fst))
  else false

/-- Deep byte justification for `x`: one of the first `maxDeepConstraints` constraints mentioning `x`
    (the caller passes them as `cands`) pins it via `denseDeepBoundOk`. -/
def denseDeepByteJustified (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (cands : List (DenseExpr p)) (bs : BusSemantics p) (facts : BusFacts p bs)
    (wits : VarId → List (BusInteraction (DenseExpr p))) (x : VarId) : Bool :=
  (cands.take maxDeepConstraints).any (fun c => denseDeepBoundOk domIdx bs facts wits x c)

/-- Evaluate the single-variable expression `e` with its variable fixed to `d` and check the result
    is a byte constant. -/
def denseExprPointByte (e : DenseExpr p) (x : VarId) (d : ZMod p) : Bool :=
  match (e.substF (fun v => if v = x then some (.const d) else none)).fold.constValue? with
  | some c => decide (c.val < 256)
  | none => false

/-- Is `e` a byte because its single variable `x` ranges over a small constraint-derived finite
    domain at every point of which `e` evaluates to a byte? -/
def denseDomainByteJustified (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (e : DenseExpr p) : Bool :=
  match e.singleVarAux with
  | some (some x) =>
    match denseFindDomainAlg (denseVarBucketLookup domIdx x) x with
    | some d => decide (d.length ≤ maxDeepDomain) && d.all (denseExprPointByte e x)
    | none => false
  | _ => false

/-- Natural upper bound of a term list `Σ cᵥ·v` under per-variable value bounds `bnd` (`bnd v`
    bounds `(denv v).val` strictly): `Σ cᵥ.val·(bnd v − 1)`; `none` if any variable is unbounded. -/
def denseLinTermsNatBound (bnd : VarId → Option Nat) : List (VarId × ZMod p) → Option Nat
  | [] => some 0
  | (v, c) :: rest =>
    match bnd v, denseLinTermsNatBound bnd rest with
    | some b, some acc => some (c.val * (b - 1) + acc)
    | _, _ => none

/-- Natural upper bound of `L.eval`: `L.const.val + Σ cᵥ.val·(bnd v − 1)`. -/
def DenseLinExpr.natBound (bnd : VarId → Option Nat) (L : DenseLinExpr p) : Option Nat :=
  (denseLinTermsNatBound bnd L.terms).map (fun s => L.const.val + s)

/-- Affine byte/limb justification: `e` linearizes to a form whose per-variable-bounded natural
    value is `< bound` (and `< p`, so it does not wrap). -/
def denseAffineJustified (bound : Nat) (bnd : VarId → Option Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L =>
    match L.natBound bnd with
    | some M => decide (M < bound) && decide (M < p)
    | none => false
  | none => false

/-- Worst-case subtracted total of a term list read as `− Σ (−cᵥ)·v`: `Σ (−cᵥ).val·(bnd v − 1)`;
    `none` if any variable is unbounded. A genuinely positive coefficient makes `(−c).val` huge and
    the budget test below fail, so no sign analysis is needed. -/
def denseLinTermsNegBound (bnd : VarId → Option Nat) : List (VarId × ZMod p) → Option Nat
  | [] => some 0
  | (v, c) :: rest =>
    match bnd v, denseLinTermsNegBound bnd rest with
    | some b, some acc => some ((-c).val * (b - 1) + acc)
    | _, _ => none

/-- Subtractive affine justification: `e` linearizes to `c₀ − Σ cᵥ·v` with every variable bounded
    and the worst-case subtraction inside `[0, c₀]`, so the value never wraps and is
    `≤ c₀ < bound` — e.g. `255 − a` with `a` byte-checked. -/
def denseNegAffineJustified (bound : Nat) (bnd : VarId → Option Nat) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L =>
    match denseLinTermsNegBound bnd L.terms with
    | some M => decide (M ≤ L.const.val) && decide (L.const.val < bound)
        && decide (L.const.val < p)
    | none => false
  | none => false

/-! ## Basis justification -/

def denseFormBoundAtImpl {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : Nat) : Option (DenseLinExpr p × Nat) :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if zmodIsZero mval then none
    else
      match bi.payload[i]?,
            facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
      | some e, some B =>
        match denseLinearize e with
        | some L => some (L.norm, B)
        | none => none
      | _, _ => none

/-- The linearized (merged) form and bound of payload slot `i` of `bi`, when the multiplicity is
    a nonzero constant and the slot carries a `slotBound`. -/
def denseFormBoundAt {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : Nat) : Option (DenseLinExpr p × Nat) :=
  match bi.multiplicity.constValue? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match bi.payload[i]?,
            facts.slotBound bi.busId mval (bi.payload.map DenseExpr.constValue?) i with
      | some e, some B =>
        match denseLinearize e with
        | some L => some (L.norm, B)
        | none => none
      | _, _ => none

@[csimp] theorem denseFormBoundAt_eq_impl : @denseFormBoundAt = @denseFormBoundAtImpl := by
  funext q bs facts bi i
  simp [denseFormBoundAt, denseFormBoundAtImpl]

/-- The checked linear forms of an interaction's payload slots, with their bounds — the only thing
    the basis reduction ever asks of a witness interaction. A pure function of the interaction, so
    the pass prepares it once per position (`denseBuildFormBounds`) instead of re-deriving it at
    every node of the reduction below. -/
def denseFormBoundsOf {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) : List (DenseLinExpr p × Nat) :=
  (List.range bi.payload.length).filterMap (denseFormBoundAt facts bi)

/-- Fuel-bounded basis reduction: is `L`'s value provably `< bound − used` via per-variable bounds
    (finish arm) after subtracting integer multiples of the checked forms `fbasis` offers for one of
    `L`'s variables? -/
def denseBasisReduceGo (bound : Nat) (bnd : VarId → Option Nat)
    (fbasis : VarId → List (DenseLinExpr p × Nat)) :
    Nat → Nat → DenseLinExpr p → Bool
  | 0, _, _ => false
  | fuel + 1, used, L =>
    (match L.natBound bnd with
     | some M => decide (used + M < bound) && decide (used + M < p)
     | none => false) ||
    -- `L.coeff v` is invariant across the candidate forms, and `L.terms.map Prod.fst` would
    -- allocate a variable list per node: both are hoisted out of the inner scan.
    L.terms.any (fun t =>
      let v := t.1
      let cL := IntervalForce.srep (L.coeff v)
      (fbasis v).any (fun LB =>
        let cF := IntervalForce.srep (LB.1.coeff v)
        let μi := cL / cF
        if cF ≠ 0 ∧ 0 < μi ∧ cF * μi = cL then
          denseBasisReduceGo bound bnd fbasis fuel (used + μi.toNat * (LB.2 - 1))
            ((L.add (LB.1.scale (-(μi.toNat : ZMod p)))).norm)
        else false))

/-- Basis justification: `e` linearizes to a form the fuel-bounded reduction proves `< bound`. -/
def denseBasisJustified (bound : Nat) (bnd : VarId → Option Nat)
    (fbasis : VarId → List (DenseLinExpr p × Nat)) (e : DenseExpr p) : Bool :=
  match denseLinearize e with
  | some L => denseBasisReduceGo bound bnd fbasis basisFuel 0 L.norm
  | none => false

/-- Is `e` provably a byte under every assignment satisfying the remaining system? Tries, in order:
    a constant `< bound`; a variable with a bus-fact bound `≤ bound`; (when `deep`) a
    selector-flag-domain deep justification or a single-variable finite-domain justification; an
    affine recomposition of bounded limbs; or a basis reduction against the range-checked slot forms
    `fbasis` offers per variable. Remaining interactions are consulted through `wits`;
    `domIdx`/`candsOf` are precomputed per-variable indexes (passed as values — a closure payload
    would be re-evaluated per call, cf. `agent-docs/log.md` entry 106). -/
def denseByteJustifiedW (bound : Nat) (deep : Bool)
    (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : VarId → List (BusInteraction (DenseExpr p)))
    (fbasis : VarId → List (DenseLinExpr p × Nat))
    (e : DenseExpr p) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    (match e with
     | .var x =>
       (match denseFindVarBound bs facts (wits x) x with
        | some b => decide (b ≤ bound)
        | none => false) ||
       (deep && decide (256 ≤ bound) &&
         denseDeepByteJustified domIdx (candsOf x) bs facts wits x)
     | _ => false) ||
    (deep && decide (256 ≤ bound) && denseDomainByteJustified domIdx e) ||
    denseAffineJustified bound (fun x => denseFindVarBound bs facts (wits x) x) e ||
    denseNegAffineJustified bound (fun x => denseFindVarBound bs facts (wits x) x) e ||
    denseBasisJustified bound (fun x => denseFindVarBound bs facts (wits x) x) fbasis e

/-- Are all of `R`'s payload entries at the declared byte slots justified (through the witness
    lookup `wits` and precomputed `domIdx`/`candsOf`, see `denseByteJustifiedW`)? -/
def denseRecvSlotsJustified (bound : Nat) (deep : Bool)
    (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits : VarId → List (BusInteraction (DenseExpr p)))
    (fbasis : VarId → List (DenseLinExpr p × Nat))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : Bool :=
  slots.all (fun slot =>
    match R.payload[slot]? with
    | some e => denseByteJustifiedW bound deep domIdx candsOf bs facts wits fbasis e
    | none => true)

end ApcOptimizer.Dense
