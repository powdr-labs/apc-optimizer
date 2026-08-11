import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap

set_option autoImplicit false

/-! # Collapsing a multi-limb reciprocal-witness group to one hint

Runtime computation only; correctness (`collapse_correct`) lives in `Proofs/HintCollapse.lean`. Shaped
for `DenseVerifiedPassW.ofExtending`, since it mints a fresh reciprocal-hint witness (like
`Reencode.lean`). The fresh `VarId` is registered only on the accepting branch. -/

/-! ## Representation-independent field-sum lemmas (consumed by `Proofs/HintCollapse.lean`) -/

section RehomedHintCollapse
variable {p : ℕ}

/-- Wrap-free: with the value-sum below `p`, the field sum's `.val` is the natural-number sum. -/
theorem sum_val_eq (hp : 0 < p) :
    ∀ (L : List (ZMod p)), (L.map (fun x => x.val)).sum < p →
      L.sum.val = (L.map (fun x => x.val)).sum
  | [], _ => by simp
  | x :: rest, hfit => by
      haveI : NeZero p := ⟨hp.ne'⟩
      simp only [List.map_cons, List.sum_cons] at hfit ⊢
      have hrest : (rest.map (fun x => x.val)).sum < p := by omega
      have ih := sum_val_eq hp rest hrest
      have hadd : (x + rest.sum).val = x.val + rest.sum.val :=
        ZMod.val_add_of_lt (by rw [ih]; omega)
      rw [hadd, ih]

/-- Byte-bounded field elements summing to `0` with the value-sum below `p` are all `0`. -/
theorem sum_zero_all_zero (hp : 0 < p) (L : List (ZMod p))
    (hfit : (L.map (fun x => x.val)).sum < p) (h0 : L.sum = 0) :
    ∀ x ∈ L, x = 0 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hval : (L.map (fun x => x.val)).sum = 0 := by
    have := sum_val_eq hp L hfit
    rw [h0] at this; simpa using this.symm
  intro x hx
  have hxval : x.val = 0 := by
    have : x.val ≤ (L.map (fun y => y.val)).sum :=
      List.single_le_sum (by intro _ _; exact Nat.zero_le _) _ (List.mem_map.2 ⟨x, hx, rfl⟩)
    omega
  exact (ZMod.val_eq_zero x).1 hxval

/-- The value of a squared difference of two byte-bounded field elements is `< 256²`. -/
theorem sq_diff_val_lt [NeZero p] (hp : 65536 ≤ p) (x y : ZMod p)
    (hx : x.val < 256) (hy : y.val < 256) : ((x - y) * (x - y)).val < 65536 := by
  rcases Nat.lt_or_ge x.val y.val with hlt | hge
  · have hd : x - y = -((y.val - x.val : ℕ) : ZMod p) := by
      have hcast : ((y.val - x.val : ℕ) : ZMod p) = y - x := by
        rw [Nat.cast_sub (le_of_lt hlt), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [hcast]; ring
    have hb : y.val - x.val ≤ 255 := by omega
    have hsq : (y.val - x.val) * (y.val - x.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, neg_mul_neg, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega
  · have hd : x - y = ((x.val - y.val : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hge, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hb : x.val - y.val ≤ 255 := by omega
    have hsq : (x.val - y.val) * (x.val - y.val) ≤ 255 * 255 := Nat.mul_le_mul hb hb
    rw [hd, ← Nat.cast_mul, ZMod.val_natCast_of_lt (by omega)]; omega

end RehomedHintCollapse

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Splitting off the linear part in one variable -/

/-- Split `E` as `coeff · wv + rest` in the single variable `wv`. -/
def denseExtractLinear (wv : VarId) : DenseExpr p → DenseExpr p × DenseExpr p
  | .const c => (.const 0, .const c)
  | .var x => if x = wv then (.const 1, .const 0) else (.const 0, .var x)
  | .add e1 e2 =>
      let (c1, r1) := denseExtractLinear wv e1
      let (c2, r2) := denseExtractLinear wv e2
      (.add c1 c2, .add r1 r2)
  | .mul e1 e2 =>
      if wv ∈ e1.vars then
        let (c1, r1) := denseExtractLinear wv e1
        (.mul c1 e2, .mul r1 e2)
      else
        let (c2, r2) := denseExtractLinear wv e2
        (.mul e1 c2, .mul e1 r2)

/-- Peel every variable of `ds` off `E` in turn, returning the list of coefficients (one per `ds`
    entry) and the final remainder. -/
def densePeel : List VarId → DenseExpr p → List (DenseExpr p) × DenseExpr p
  | [], E => ([], E)
  | wv :: ds, E =>
      let (c, r) := denseExtractLinear wv E
      let (cs, rest) := densePeel ds r
      (c :: cs, rest)

/-! ## Sum of expressions -/

/-- The expression `Σ l`. -/
def denseSumExpr (l : List (DenseExpr p)) : DenseExpr p := l.foldr DenseExpr.add (DenseExpr.const 0)

/-! ## Plain-sum coefficient recognizer -/

/-- The single variable a coefficient reduces to: a bare `var a`, or `a·1` / `1·a`. -/
def denseCoeffVar : DenseExpr p → Option VarId
  | .var a => some a
  | .mul (.var a) (.const c) => if c = 1 then some a else none
  | .mul (.const c) (.var a) => if c = 1 then some a else none
  | _ => none

/-- Each coefficient's `fold` reduces to one `≤ 256`-bounded, `D`-free, input-column variable. -/
def denseCoeffsByteOK (reg : VarRegistry) (B : Std.HashMap VarId Nat) (D : List VarId) :
    List (DenseExpr p) → Bool
  | [] => true
  | c :: cs =>
    (match denseCoeffVar c.fold with
     | some a => (match B[a]? with | some b => decide (b ≤ 256) | none => false)
     | none => false) &&
    D.all (fun wv => decide (wv ∉ c.vars)) &&
    c.vars.all (fun x => reg.isInput x) &&
    denseCoeffsByteOK reg B D cs

/-! ## Sum-of-squares (difference) coefficient recognizer -/

/-- Recognize a `fold`-normalized difference `a - b` of two variables. -/
def denseDiffVarsOf : DenseExpr p → Option (VarId × VarId)
  | .add (.var a) (.mul (.const c) (.var b)) => if c = -1 then some (a, b) else none
  | _ => none

/-- Each coefficient's `fold` is a difference of two `≤ 256`-bounded, `D`-free, input-column
    variables. -/
def denseSqCoeffsOK (reg : VarRegistry) (B : Std.HashMap VarId Nat) (D : List VarId) :
    List (DenseExpr p) → Bool
  | [] => true
  | c :: cs =>
    (match denseDiffVarsOf c.fold with
     | some (a, b) =>
         (match B[a]? with | some ba => decide (ba ≤ 256) | none => false) &&
         (match B[b]? with | some bb => decide (bb ≤ 256) | none => false)
     | none => false) &&
    D.all (fun wv => decide (wv ∉ c.vars)) &&
    c.vars.all (fun x => reg.isInput x) &&
    denseSqCoeffsOK reg B D cs

/-! ## The occurrence-code array

One `VarId`-indexed code per variable answers every discovery question the pass asks:

| code | meaning |
|---|---|
| `0` | unseen |
| `1` | disqualified: occurs in a bus interaction, or in ≥ 2 constraint entries |
| `2 + i` | occurs in exactly one constraint entry, at index `i` |

The bus walk runs first, so a `2 + i` code *is* a witness (`denseHcWits`) — no filter needed at use,
and no set of all bus variables is ever built. -/

/-- Disqualify every variable of `e`. The already-disqualified read spares the write: bus variables
    repeat heavily across interactions (addresses, timestamps). -/
def denseHcBusMark : DenseExpr p → Array Nat → Array Nat
  | .const _, st => st
  | .var v, st => if st.getD v.index 1 == 1 then st else st.setIfInBounds v.index 1
  | .add a b, st => denseHcBusMark b (denseHcBusMark a st)
  | .mul a b, st => denseHcBusMark b (denseHcBusMark a st)

/-- Both list walks are explicit recursions rather than `List.foldl`: a closure application per
    payload slot is a measurable share of a sweep this shallow. -/
def denseHcBusMarkL : List (DenseExpr p) → Array Nat → Array Nat
  | [], st => st
  | e :: es, st => denseHcBusMarkL es (denseHcBusMark e st)

def denseHcBusScan : List (BusInteraction (DenseExpr p)) → Array Nat → Array Nat
  | [], st => st
  | bi :: rest, st =>
    denseHcBusScan rest (denseHcBusMarkL bi.payload (denseHcBusMark bi.multiplicity st))

/-- Record constraint entry `i`'s leaves. A repeat inside the same entry keeps its code — that is
    the per-constraint deduplication, without a `vars` list or a `dedup`. -/
def denseHcCsMark (i : Nat) : DenseExpr p → Array Nat → Array Nat
  | .const _, st => st
  | .var v, st =>
      let c := st.getD v.index 1
      if c == 0 then st.setIfInBounds v.index (2 + i)
      else if c == 2 + i || c == 1 then st
      else st.setIfInBounds v.index 1
  | .add a b, st => denseHcCsMark i b (denseHcCsMark i a st)
  | .mul a b, st => denseHcCsMark i b (denseHcCsMark i a st)

def denseHcCsScan : Nat → List (DenseExpr p) → Array Nat → Array Nat
  | _, [], st => st
  | i, c :: cs, st => denseHcCsScan (i + 1) cs (denseHcCsMark i c st)

/-- The occurrence codes of `d`, over `nvars` (the registry size). -/
def denseHcScan (nvars : Nat) (d : DenseConstraintSystem p) : Array Nat :=
  denseHcCsScan 0 d.algebraicConstraints
    (denseHcBusScan d.busInteractions (Array.replicate nvars 0))

/-- Constraint entries holding at least two witnesses, ascending — the only collapse candidates,
    since a collapse needs `2 ≤ D.length`. -/
def denseHcGroups (st : Array Nat) : List Nat :=
  let m : Std.HashMap Nat Nat := st.foldl (init := ∅) fun m c =>
    if 2 ≤ c then m.insert (c - 2) (m.getD (c - 2) 0 + 1) else m
  ((m.toList.filter (fun kv => 2 ≤ kv.2)).map (·.1)).mergeSort (· ≤ ·)

/-- The constraints at the ascending indices `is`, paired with their index. -/
def denseHcPick (j : Nat) (is : List Nat) :
    List (DenseExpr p) → List (Nat × DenseExpr p)
  | [] => []
  | c :: cs =>
    match is with
    | [] => []
    | i :: is' =>
      if i == j then (i, c) :: denseHcPick (j + 1) is' cs else denseHcPick (j + 1) is cs

/-- `E`'s witnesses in first-occurrence order (the order that fixes `denom`'s term order and the
    minted variable's name), deduplicated. -/
def denseHcWitsGo (st : Array Nat) (code : Nat) : DenseExpr p → List VarId → List VarId
  | .const _, acc => acc
  | .var v, acc => if st.getD v.index 0 == code && !acc.contains v then v :: acc else acc
  | .add a b, acc => denseHcWitsGo st code b (denseHcWitsGo st code a acc)
  | .mul a b, acc => denseHcWitsGo st code b (denseHcWitsGo st code a acc)

def denseHcWits (st : Array Nat) (idx : Nat) (E : DenseExpr p) : List VarId :=
  (denseHcWitsGo st (2 + idx) E []).reverse

/-! ## Freshness: no collision with the current system -/

/-- Is `v` absent from the current system? An unregistered candidate cannot be a member (`none`);
    otherwise membership in `d.occ` (`Measure.lean`) is checked by `VarId`. -/
def denseIsFresh (reg : VarRegistry) (d : DenseConstraintSystem p) (v : OutputVariable) : Bool :=
  match reg.idOf? v with
  | some i => !d.occ.contains i
  | none => true

/-- `denseIsFresh` served from the occurrence codes: `i ∈ d.occ` is exactly `st[i] ≠ 0`. -/
def denseHcFresh (reg : VarRegistry) (st : Array Nat) (v : OutputVariable) : Bool :=
  match reg.idOf? v with
  | some i => st.getD i.index 0 == 0
  | none => true

/-! ## The bounds map, restricted to the queried variables -/

/-- The coefficient variables whose bounds the certificates will query. -/
def denseHcWantVars : List (DenseExpr p) → List VarId
  | [] => []
  | c :: cs =>
    let f := c.fold
    (match denseCoeffVar f with
     | some a => [a]
     | none => match denseDiffVarsOf f with
       | some (a, b) => [a, b]
       | none => []) ++ denseHcWantVars cs

/-- The wanted variables as `VarId`-indexed marks: the sweep tests one array element per payload
    slot, where a `Std.HashSet VarId` hashed a boxed `VarId` per slot. -/
def denseHcWantArr (nvars : Nat) (want : List VarId) : Array Bool :=
  want.foldl (fun a v => a.setIfInBounds v.index true) (Array.replicate nvars false)

def denseHcAnyWanted (want : Array Bool) : List (DenseExpr p) → Bool
  | [] => false
  | .var v :: rest => want.getD v.index false || denseHcAnyWanted want rest
  | _ :: rest => denseHcAnyWanted want rest

/-- `denseBuild` over the interactions that can bound a wanted variable: an interaction whose raw
    payload slots hold no wanted variable is dropped, so it pays no `denseBiPrepOf` (with its
    compound-slot linearizations) and no `slotBound` call. This is `denseAddAll` on a sublist, so its
    bounds are sound for exactly the reason `denseBuild`'s are (`denseHcBounds_sound`) — dropping
    interactions can only lose bounds, never invent one. -/
def denseHcBounds (bs : BusSemantics p) (facts : BusFacts p bs) (nvars : Nat) (want : List VarId)
    (dbis : List (BusInteraction (DenseExpr p))) : Std.HashMap VarId Nat :=
  match want with
  | [] => ∅
  | _ =>
    let w := denseHcWantArr nvars want
    denseAddAll bs facts (dbis.filter (fun bi => denseHcAnyWanted w bi.payload)) ∅

/-! ## The collapse attempt -/

/-- The accepted collapse: mint `invVar` and replace the target at its index. Replacing at the index
    rather than by value is the same list — the target is unique among the constraints, since a
    duplicate entry would have disqualified every witness (`hcSet_eq_map` in the proof). -/
def denseHcAccept (reg : VarRegistry) (d : DenseConstraintSystem p) (idx : Nat) (invVar : OutputVariable)
    (denom rest : DenseExpr p) : VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  let invId := (reg.register invVar).2
  ((reg.register invVar).1,
    { d with algebraicConstraints :=
        d.algebraicConstraints.set idx (.add (.mul denom (.var invId)) rest) },
    [(invId, DenseComputationMethod.quotientOrZero (.mul (.const (-1)) rest) denom)])

/-- One collapse attempt on the candidate target `E` at index `idx` with witnesses `D`: peel once,
    then offer the peel to the plain-sum recognizer (`is-zero`/`seqz`) and, failing that, to the
    sum-of-squares one (`is-equal`). The fresh witness is registered only on the accepting branch. -/
def denseHcTry (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (st : Array Nat) (idx : Nat) (E : DenseExpr p) (D : List VarId) :
    Option (VarRegistry × DenseConstraintSystem p × DenseDerivations p) :=
  if 2 ≤ D.length then
    let coeffs := (densePeel D E).1
    let rest := (densePeel D E).2
    if D.all (fun wv => decide (wv ∉ rest.vars)) then
    if rest.vars.all (fun x => reg.isInput x) then
      let Bm := denseHcBounds bs facts st.size (denseHcWantVars coeffs) d.busInteractions
      if denseCoeffsByteOK reg Bm D coeffs && decide (coeffs.length * 256 ≤ p) then
        let invVar : OutputVariable := ⟨"hcinv#" ++ (reg.resolve (D.headD default)).name, none⟩
        if denseHcFresh reg st invVar then
          some (denseHcAccept reg d idx invVar (denseSumExpr coeffs) rest)
        else none
      else if denseSqCoeffsOK reg Bm D coeffs && decide (coeffs.length * 65536 ≤ p) then
        let invVar : OutputVariable := ⟨"hcsq#" ++ (reg.resolve (D.headD default)).name, none⟩
        if denseHcFresh reg st invVar then
          some (denseHcAccept reg d idx invVar
            (denseSumExpr (coeffs.map (fun c => DenseExpr.mul c c))) rest)
        else none
      else none
    else none
    else none
  else none

/-- The first candidate target that collapses. -/
def denseHcScanTry (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (st : Array Nat) :
    List (Nat × DenseExpr p) → Option (VarRegistry × DenseConstraintSystem p × DenseDerivations p)
  | [] => none
  | (idx, E) :: rest =>
    match denseHcTry bs facts reg d st idx E (denseHcWits st idx E) with
    | some r => some r
    | none => denseHcScanTry bs facts reg d st rest

/-! ## The pass, as a registry-extending transform -/

/-- Collapses a group of witnesses that each occur in a single constraint into one reciprocal hint:
    `Σ aᵢ·wᵢ + rest = 0` (byte-bounded `wᵢ`, each occurring only here) becomes `denom·inv + rest`
    with `denom = Σ aᵢ` and one fresh `inv := QuotientOrZero(−rest, denom)` (the `seqz`/`is-zero`
    idiom; a sum-of-squares variant handles `is-equal`). Identity unless `p` is witnessed prime.

    Everything past the occurrence-code scan is proportional to the candidate constraints: with no
    candidate group there is no bounds map and no per-constraint work at all. -/
def denseHintCollapseF (pw : PrimeWitness p) (reg : VarRegistry) (bsem : BusSemantics p)
    (facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    let st := denseHcScan reg.byId.size d
    match denseHcGroups st with
    | [] => (reg, d, [])
    | is =>
      (denseHcScanTry bsem facts reg d st
        (denseHcPick 0 is d.algebraicConstraints)).getD (reg, d, [])
  else (reg, d, [])

end ApcOptimizer.Dense
