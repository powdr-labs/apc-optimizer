import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.Normalize

set_option autoImplicit false

/-! # Dense carry-branch resolution (runtime). Pass and `DensePassCorrect` proof in
`Proofs/CarryBranch.lean`; bounds map via `denseBuild` (`DigitFold.lean`).

The never-zero certificate runs on a **compiled row**: the affine form's terms paired with their
variables' widths (`bound - 1`), resolved from the bounds map once. Everything after that is `Nat`
arithmetic — `(k * a).val` is `k.val * a.val % p` — so a rescaling costs no `ZMod` operation, no
allocation and no `B` lookup. Only a `true` answer is a claim, so the bound gates, the early abort
and the batch inversion below are all free of proof obligations. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The compiled certificate row -/

/-- An affine form compiled for the interval certificate: per term, the coefficient's `val` and the
    width `bound - 1` of its variable's value range. -/
abbrev DenseCbRow := List (Nat × Nat)

/-- Compile `terms` against the bounds map, `none` as soon as a variable is unbounded or pinned to
    the empty range. This is the rescaling-independent gate: an unbounded term defeats every
    candidate, so the whole search is skipped. -/
def denseCbRow? (B : Std.HashMap VarId Nat) : List (VarId × ZMod p) → Option DenseCbRow
  | [] => some []
  | (v, a) :: rest =>
    match B[v]? with
    | none => none
    | some bound =>
      if bound = 0 then none
      else
        match denseCbRow? B rest with
        | none => none
        | some r => some ((a.val, bound - 1) :: r)

/-! ## One rescaling's interval scan -/

/-- Accumulate the positive- and negative-side magnitudes of `k · row` under the widths, aborting
    the moment either can no longer fit: the certificate needs `mn < c` and `c + mp < p`, and both
    sums are monotone, so `mp ≥ hiCap` or `mn ≥ loCap` is final. `kv * av % P` is `(k * a).val`. -/
def denseCbScan (P kv loCap hiCap : Nat) : DenseCbRow → Nat → Nat → Bool
  | [], _, _ => true
  | (av, w) :: rest, mp, mn =>
    let v := kv * av % P
    let nv := P - v
    if v ≤ nv then
      let mp' := mp + v * w
      if mp' < hiCap then denseCbScan P kv loCap hiCap rest mp' mn else false
    else
      let mn' := mn + nv * w
      if mn' < loCap then denseCbScan P kv loCap hiCap rest mp mn' else false

/-- The rescaled form's value is pinned to `(0, P)`, hence nonzero. `cv` is the form's constant. -/
def denseCbCert (P cv kv : Nat) (row : DenseCbRow) : Bool :=
  let c := kv * cv % P
  decide (0 < c) && decide (c < P) && denseCbScan P kv c (P - c) row 0 0

/-! ## The candidate rescalings -/

/-- Modular inverse of `x`. A rescaling scalar is a pure heuristic — `k · l ≠ 0` gives `l ≠ 0` for
    any `k` — so nothing here is a proof obligation. -/
def denseCbInv (P x : Nat) : Nat := (ZMod.inv P ((x : ZMod P))).val

/-- Montgomery batch inversion, fused with the certificate test: one extended gcd and three
    multiplications per term give every `a⁻¹` rescaling, instead of one gcd per term. `pre` is the
    product of the entries above; the returned scalar is `pre⁻¹`, so seeding with the form's
    constant makes the top-level result the `const⁻¹` candidate. -/
def denseCbTryRow (P cv : Nat) (row : DenseCbRow) : DenseCbRow → Nat → Nat × Bool
  | [], pre => (denseCbInv P pre, false)
  | (av, _) :: rest, pre =>
    let r := denseCbTryRow P cv row rest (pre * av % P)
    (r.1 * av % P, r.2 || denseCbCert P cv (r.1 * pre % P) row)

/-- Try `k = 1` first (no inversion at all), then the batched `a⁻¹` and `const⁻¹` rescalings. -/
def denseCbSearch (P cv : Nat) (row : DenseCbRow) : Bool :=
  denseCbCert P cv (1 % P) row ||
    (let r := denseCbTryRow P cv row row cv
     r.2 || denseCbCert P cv r.1 row)

/-! ## Dense never-zero certificate -/

/-- Fail-fast bound check straight on the expression tree, ahead of the linearization: an unbounded
    variable defeats every rescaling, and this exits at the first one instead of building a term
    list first. In the first cleanup cycle no interaction has produced a bound yet, so it exits on
    the leftmost variable of every candidate. -/
def denseCbBounded (B : Std.HashMap VarId Nat) : DenseExpr p → Bool
  | .const _ => true
  | .var i => match B[i]? with | some b => decide (b ≠ 0) | none => false
  | .add a b => denseCbBounded B a && denseCbBounded B b
  | .mul a b => denseCbBounded B a && denseCbBounded B b

/-- Certifies `e` never-zero under the bounds `B`: linearize, compile the row, then search the
    rescalings. A zero constant defeats every rescaling (`c` would be `0`), so it exits first. -/
def denseNeverZeroB (ops : DenseZModOps p) (B : Std.HashMap VarId Nat) (e : DenseExpr p) : Bool :=
  denseCbBounded B e &&
  match denseLinearizeWith ops e with
  | none => false
  | some l =>
    let n := l.normWith ops
    let cv := n.const.val
    if cv = 0 then false
    else
      match denseCbRow? B n.terms with
      | none => false
      | some row => denseCbSearch p cv row

/-! ## Dense product-constraint resolution -/

/-- Collapse a product `f·g` in a constraint to the surviving factor when the other factor is
    certified never-zero by the value bounds `B`: e.g. `(x-5)·g = 0` with `g` provably nonzero
    becomes `x-5 = 0`. Recurses into the surviving factor. -/
def denseResolveExpr (ops : DenseZModOps p) (B : Std.HashMap VarId Nat) :
    DenseExpr p → DenseExpr p
  | e@(.mul f g) =>
      if denseNeverZeroB ops B g then denseResolveExpr ops B f
      else if denseNeverZeroB ops B f then denseResolveExpr ops B g
      else e
  | e => e

theorem denseResolveExpr_vars (ops : DenseZModOps p) (B : Std.HashMap VarId Nat) (e : DenseExpr p) :
    ∀ x ∈ (denseResolveExpr ops B e).vars, x ∈ e.vars := by
  induction e with
  | mul f g ihf ihg =>
      intro x hx
      simp only [denseResolveExpr] at hx
      simp only [DenseExpr.vars, List.mem_append]
      split_ifs at hx with h1 h2
      · exact Or.inl (ihf x hx)
      · exact Or.inr (ihg x hx)
      · simpa only [DenseExpr.vars, List.mem_append] using hx
  | const n => intro x hx; simpa only [denseResolveExpr] using hx
  | var y => intro x hx; simpa only [denseResolveExpr] using hx
  | add a b iha ihb => intro x hx; simpa only [denseResolveExpr] using hx

/-! ## The dense transform -/

/-- The dense carry-branch-resolution transform (gated on `p` prime). -/
def denseCarryBranchF (pw : PrimeWitness p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    { d with algebraicConstraints :=
        d.algebraicConstraints.map (denseResolveExpr denseZModOps
          (denseBuild bs facts d.busInteractions)) }
  else d

theorem denseCarryBranchF_covered (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseCarryBranchF pw bs facts d).CoveredBy reg := by
  unfold denseCarryBranchF
  by_cases h : pw.isPrime = true
  · rw [if_pos h]
    refine ⟨fun e he => ?_, fun bi hbi => hcov.2 bi hbi⟩
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact fun i hi =>
      hcov.1 e0 he0 i (denseResolveExpr_vars _ _ e0 i hi)
  · rw [if_neg h]; exact hcov

end ApcOptimizer.Dense
