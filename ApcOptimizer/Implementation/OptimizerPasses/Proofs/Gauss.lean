import ApcOptimizer.Implementation.OptimizerPasses.Gauss
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagUnify

set_option autoImplicit false

/-! # Correctness for the dense Gauss-elimination pass

Substitution-shaped, like every solver pass: correctness rides on
`DenseConstraintSystem.substF_denseCorrect`, fed the final solution map's *entailment* and
*occurrence closure*. Those two facts are all the spec asks for, so the scheduler — buckets, watch
lists, `occ`/`prot`, `status`, `woken` — appears nowhere below: a wrong entry costs elimination
opportunities, never soundness.

Part one is the affine layer: substituting a solution map into a row preserves its value and
introduces no variable, and solving an entailed row for a unit-coefficient variable yields an
entailed assignment. Part two carries two invariants through the engine (`GInv`) — every pending row
is entailed and occurrence-closed, every stored solution is an entailed assignment with the same
closure — of which `gAdopt` is the only step that touches either. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

def denseLinEnv (σ : VarId → Option (DenseLinExpr p)) (denv : VarId → ZMod p) :
    VarId → ZMod p :=
  fun i => match σ i with | some row => row.eval denv | none => denv i

theorem denseLinSubstData_eval (terms : List (VarId × ZMod p))
    (σ : VarId → Option (DenseLinExpr p)) (denv : VarId → ZMod p) (k : ZMod p) :
    terms.foldl (fun out yc =>
        match σ yc.1 with
        | some t => out + yc.2 * t.const
        | none => out) k
      + ((terms.flatMap (fun yc =>
          match σ yc.1 with
          | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
          | none => [yc])).map (fun zc => zc.2 * denv zc.1)).sum
    = k + (terms.map (fun yc => yc.2 * denseLinEnv σ denv yc.1)).sum := by
  induction terms generalizing k with
  | nil => simp
  | cons yc rest ih =>
      simp only [List.foldl_cons, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      cases hσ : σ yc.1 with
      | none =>
          simp only [List.map_singleton, List.sum_singleton]
          rw [show denseLinEnv σ denv yc.1 = denv yc.1 by simp [denseLinEnv, hσ]]
          have hrest := ih k
          linear_combination hrest
      | some row =>
          simp only [List.map_map]
          rw [show denseLinEnv σ denv yc.1 = row.eval denv by simp [denseLinEnv, hσ],
            DenseLinExpr.eval]
          have hrest := ih (k + yc.2 * row.const)
          have hscale :
              ((row.terms.map fun zc => (zc.1, yc.2 * zc.2)).map
                  fun zc => zc.2 * denv zc.1).sum
                = yc.2 * ((row.terms.map fun zc => zc.2 * denv zc.1).sum) := by
            induction row.terms with
            | nil => simp
            | cons zc zs ihz =>
                simp only [List.map_cons, List.sum_cons, ihz]
                ring
          rw [show
            (row.terms.map ((fun zc => zc.2 * denv zc.1) ∘
              fun zc => (zc.1, yc.2 * zc.2))).sum
              = yc.2 * ((row.terms.map fun zc => zc.2 * denv zc.1).sum) by
                simpa [Function.comp_def] using hscale]
          linear_combination hrest

theorem denseLinSubstF_eval (l : DenseLinExpr p)
    (σ : VarId → Option (DenseLinExpr p)) (denv : VarId → ZMod p) :
    (denseLinSubstF l σ).eval denv = l.eval (denseLinEnv σ denv) := by
  rw [denseLinSubstF, DenseLinExpr.norm_eval]
  simp only [DenseLinExpr.eval]
  exact denseLinSubstData_eval l.terms σ denv l.const

theorem denseLinSubstF_terms_closed (l : DenseLinExpr p)
    (σ : VarId → Option (DenseLinExpr p)) (S : VarId → Prop)
    (hl : ∀ z ∈ l.terms.map Prod.fst, S z)
    (hσ : ∀ i row, σ i = some row → ∀ z ∈ row.terms.map Prod.fst, S z) :
    ∀ z ∈ (denseLinSubstF l σ).terms.map Prod.fst, S z := by
  intro z hz
  let rawTerms := l.terms.flatMap (fun yc =>
    match σ yc.1 with
    | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
    | none => [yc])
  have hzraw : z ∈ rawTerms.map Prod.fst := by
    exact DenseLinExpr.norm_terms_fst
      ⟨l.terms.foldl (fun out yc =>
        match σ yc.1 with
        | some t => out + yc.2 * t.const
        | none => out) l.const, rawTerms⟩ z hz
  simp only [rawTerms, List.mem_map, List.mem_flatMap] at hzraw
  obtain ⟨zc, ⟨yc, hyc, hyout⟩, hzc⟩ := hzraw
  cases hrow : σ yc.1 with
  | none =>
      simp only [hrow, List.mem_singleton] at hyout
      subst zc
      exact hzc ▸ hl yc.1 (List.mem_map.2 ⟨yc, hyc, rfl⟩)
  | some row =>
      simp only [hrow, List.mem_map] at hyout
      obtain ⟨rc, hrc, hrczc⟩ := hyout
      subst zc
      exact hzc ▸ hσ yc.1 row hrow rc.1 (List.mem_map.2 ⟨rc, hrc, rfl⟩)

theorem denseLinScale_eval (k : ZMod p) (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    (denseLinScale k l).eval denv = k * l.eval denv := by
  rw [denseLinScale, DenseLinExpr.norm_eval, DenseLinExpr.scale_eval]


theorem denseLinSubst_eval (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p)
    (denv : VarId → ZMod p) (hx : denv x = t.eval denv) :
    (denseLinSubst s x t).eval denv = s.eval denv := by
  rw [denseLinSubst, denseLinSubstF_eval]
  congr 1
  funext y
  by_cases hy : y = x
  · subst y
    simp [denseLinEnv, hx]
  · simp [denseLinEnv, hy]

theorem denseLinSubst_terms_closed (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p)
    (S : VarId → Prop) (hs : ∀ z ∈ s.terms.map Prod.fst, S z)
    (ht : ∀ z ∈ t.terms.map Prod.fst, S z) :
    ∀ z ∈ (denseLinSubst s x t).terms.map Prod.fst, S z := by
  apply denseLinSubstF_terms_closed s _ S hs
  intro i row hi
  by_cases hix : i = x
  · subst i
    have hrow : t = row := by simpa using hi
    subst row
    exact ht
  · simp [hix] at hi

theorem denseSparseSolveAt_sound (l : DenseLinExpr p) (x y : VarId)
    (t : DenseLinExpr p) (h : denseSparseSolveAt l x = some (y, t))
    (denv : VarId → ZMod p) (hl : l.eval denv = 0) :
    denv y = t.eval denv := by
  unfold denseSparseSolveAt at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denseLinScale_eval]
    have hs := l.eval_split x denv
    rw [h1, one_mul] at hs
    rw [hs] at hl
    linear_combination hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := l.eval_split x denv
    rw [h2] at hs
    rw [hs] at hl
    linear_combination -hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denseLinScale_eval]
    have hs := l.eval_split x denv
    have h0 : l.coeff x * denv x + (l.others x).eval denv = 0 := by
      rw [← hs]
      exact hl
    linear_combination (l.coeff x)⁻¹ * h0 - denv x * h3

theorem denseSparseSolveAt_terms (l : DenseLinExpr p) (x y : VarId)
    (t : DenseLinExpr p) (h : denseSparseSolveAt l x = some (y, t)) :
    ∀ z ∈ t.terms.map Prod.fst, z ∈ l.terms.map Prod.fst := by
  unfold denseSparseSolveAt at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro z hz
    have hz' := DenseLinExpr.norm_terms_fst ((l.others x).scale (-1)) z hz
    rw [DenseLinExpr.scale_terms_fst] at hz'
    exact l.others_terms_fst_mem x z hz'
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun z hz => l.others_terms_fst_mem x z hz
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro z hz
    have hz' := DenseLinExpr.norm_terms_fst
      ((l.others x).scale (-(l.coeff x)⁻¹)) z hz
    rw [DenseLinExpr.scale_terms_fst] at hz'
    exact l.others_terms_fst_mem x z hz'

/-! ## The three predicates -/

/-- `l` vanishes on every satisfying assignment. -/
def GEnt (bs : BusSemantics p) (d : DenseConstraintSystem p) (l : DenseLinExpr p) : Prop :=
  ∀ denv, d.satisfies bs denv → l.eval denv = 0

/-- `x` equals `t` on every satisfying assignment. -/
def GAsg (bs : BusSemantics p) (d : DenseConstraintSystem p) (x : VarId) (t : DenseLinExpr p) :
    Prop :=
  ∀ denv, d.satisfies bs denv → denv x = t.eval denv

/-- Every variable of `l` occurs in the system. -/
def GCl (d : DenseConstraintSystem p) (l : DenseLinExpr p) : Prop :=
  ∀ z ∈ l.terms.map Prod.fst, z ∈ d.occ

theorem GCl_nil (d : DenseConstraintSystem p) (c : ZMod p) : GCl d ⟨c, []⟩ := by
  intro z hz; simp at hz

/-! ## The walk

`GRes.toLin` is the affine form a walk result stands for; `blk` stands for none, which is what makes
the blocked case vacuous in every lemma below. -/

def GRes.toLin : GRes p → Option (DenseLinExpr p)
  | .cst c => some ⟨c, []⟩
  | .lin l => some l
  | .blk _ => none

theorem gAddRes_eval (ops : DenseZModOps p) (ra rb : GRes p) (l : DenseLinExpr p)
    (h : (gAddRes ops ra rb).toLin = some l) :
    ∃ la lb, ra.toLin = some la ∧ rb.toLin = some lb ∧
      ∀ denv, l.eval denv = la.eval denv + lb.eval denv := by
  cases ra with
  | blk w => simp [gAddRes, GRes.toLin] at h
  | cst c1 =>
      cases rb with
      | blk w => simp [gAddRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h
          subst h
          exact ⟨⟨c1, []⟩, ⟨c2, []⟩, rfl, rfl, by intro denv; simp [DenseLinExpr.eval, ops.add_eq]⟩
      | lin l2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h
          subst h
          refine ⟨⟨c1, []⟩, l2, rfl, rfl, ?_⟩
          intro denv
          simp only [DenseLinExpr.eval, ops.add_eq, List.map_nil, List.sum_nil, add_zero]
          ring
  | lin l1 =>
      cases rb with
      | blk w => simp [gAddRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h
          subst h
          refine ⟨l1, ⟨c2, []⟩, rfl, rfl, ?_⟩
          intro denv
          simp only [DenseLinExpr.eval, ops.add_eq, List.map_nil, List.sum_nil, add_zero]
          ring
      | lin l2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h
          subst h
          refine ⟨l1, l2, rfl, rfl, ?_⟩
          intro denv
          rw [DenseLinExpr.addWith_eq, DenseLinExpr.add_eval]

theorem gAddRes_terms (ops : DenseZModOps p) (ra rb : GRes p) (l la lb : DenseLinExpr p)
    (h : (gAddRes ops ra rb).toLin = some l)
    (hla : ra.toLin = some la) (hlb : rb.toLin = some lb) :
    ∀ z ∈ l.terms.map Prod.fst,
      z ∈ la.terms.map Prod.fst ∨ z ∈ lb.terms.map Prod.fst := by
  cases ra with
  | blk w => simp [gAddRes, GRes.toLin] at h
  | cst c1 =>
      cases rb with
      | blk w => simp [gAddRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h hla hlb
          subst h; intro z hz; simp at hz
      | lin l2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h hla hlb
          subst h; subst hlb; intro z hz; exact Or.inr hz
  | lin l1 =>
      cases rb with
      | blk w => simp [gAddRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h hla hlb
          subst h; subst hla; intro z hz; exact Or.inl hz
      | lin l2 =>
          simp only [gAddRes, GRes.toLin, Option.some.injEq] at h hla hlb
          subst h; subst hla; subst hlb
          intro z hz
          rw [DenseLinExpr.addWith_eq] at hz
          simpa [DenseLinExpr.add, List.map_append] using hz

theorem gMulRes_eval (ops : DenseZModOps p) (ra rb : GRes p) (l : DenseLinExpr p)
    (h : (gMulRes ops ra rb).toLin = some l) :
    ∃ la lb, ra.toLin = some la ∧ rb.toLin = some lb ∧
      ∀ denv, l.eval denv = la.eval denv * lb.eval denv := by
  cases ra with
  | blk w => simp [gMulRes, GRes.toLin] at h
  | cst c1 =>
      cases rb with
      | blk w => simp [gMulRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gMulRes, GRes.toLin, Option.some.injEq] at h
          subst h
          exact ⟨⟨c1, []⟩, ⟨c2, []⟩, rfl, rfl, by intro denv; simp [DenseLinExpr.eval, ops.mul_eq]⟩
      | lin l2 =>
          simp only [gMulRes, GRes.toLin, Option.some.injEq] at h
          subst h
          refine ⟨⟨c1, []⟩, l2, rfl, rfl, ?_⟩
          intro denv
          rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_eval]
          simp only [DenseLinExpr.eval, List.map_nil, List.sum_nil, add_zero]
  | lin l1 =>
      cases rb with
      | blk w => simp [gMulRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gMulRes, GRes.toLin, Option.some.injEq] at h
          subst h
          refine ⟨l1, ⟨c2, []⟩, rfl, rfl, ?_⟩
          intro denv
          rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_eval]
          simp only [DenseLinExpr.eval, List.map_nil, List.sum_nil, add_zero]
          ring
      | lin l2 =>
          refine ⟨l1, l2, rfl, rfl, ?_⟩
          simp only [gMulRes] at h
          by_cases h1 : (l1.normWith ops).terms.isEmpty
          · rw [if_pos h1] at h
            simp only [GRes.toLin, Option.some.injEq] at h
            subst h
            intro denv
            rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_eval]
            have hn : (l1.normWith ops).terms = [] := List.isEmpty_iff.1 (by simpa using h1)
            have hc : (l1.normWith ops).eval denv = (l1.normWith ops).const := by
              simp only [DenseLinExpr.eval, hn, List.map_nil, List.sum_nil, add_zero]
            have hq : (l1.normWith ops).eval denv = l1.eval denv := by
              rw [DenseLinExpr.normWith_eq, DenseLinExpr.norm_eval]
            rw [← hq, hc]
          · rw [if_neg h1] at h
            by_cases h2 : (l2.normWith ops).terms.isEmpty
            · rw [if_pos h2] at h
              simp only [GRes.toLin, Option.some.injEq] at h
              subst h
              intro denv
              rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_eval]
              have hn : (l2.normWith ops).terms = [] := List.isEmpty_iff.1 (by simpa using h2)
              have hc : (l2.normWith ops).eval denv = (l2.normWith ops).const := by
                simp only [DenseLinExpr.eval, hn, List.map_nil, List.sum_nil, add_zero]
              have hq : (l2.normWith ops).eval denv = l2.eval denv := by
                rw [DenseLinExpr.normWith_eq, DenseLinExpr.norm_eval]
              have e1 : (l1.normWith ops).eval denv = l1.eval denv := by
                rw [DenseLinExpr.normWith_eq, DenseLinExpr.norm_eval]
              rw [e1, ← hq, hc, mul_comm]
            · rw [if_neg h2] at h
              simp [GRes.toLin] at h

theorem gMulRes_terms (ops : DenseZModOps p) (ra rb : GRes p) (l la lb : DenseLinExpr p)
    (h : (gMulRes ops ra rb).toLin = some l)
    (hla : ra.toLin = some la) (hlb : rb.toLin = some lb) :
    ∀ z ∈ l.terms.map Prod.fst,
      z ∈ la.terms.map Prod.fst ∨ z ∈ lb.terms.map Prod.fst := by
  cases ra with
  | blk w => simp [gMulRes, GRes.toLin] at h
  | cst c1 =>
      cases rb with
      | blk w => simp [gMulRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gMulRes, GRes.toLin, Option.some.injEq] at h
          subst h; intro z hz; simp at hz
      | lin l2 =>
          simp only [gMulRes, GRes.toLin, Option.some.injEq] at h hlb
          subst h; subst hlb
          intro z hz
          rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_terms_fst] at hz
          exact Or.inr hz
  | lin l1 =>
      cases rb with
      | blk w => simp [gMulRes, GRes.toLin] at h
      | cst c2 =>
          simp only [gMulRes, GRes.toLin, Option.some.injEq] at h hla
          subst h; subst hla
          intro z hz
          rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_terms_fst] at hz
          exact Or.inl hz
      | lin l2 =>
          simp only [GRes.toLin, Option.some.injEq] at hla hlb
          subst hla; subst hlb
          simp only [gMulRes] at h
          by_cases h1 : (l1.normWith ops).terms.isEmpty
          · rw [if_pos h1] at h
            simp only [GRes.toLin, Option.some.injEq] at h
            subst h
            intro z hz
            rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_terms_fst] at hz
            exact Or.inr hz
          · rw [if_neg h1] at h
            by_cases h2 : (l2.normWith ops).terms.isEmpty
            · rw [if_pos h2] at h
              simp only [GRes.toLin, Option.some.injEq] at h
              subst h
              intro z hz
              rw [DenseLinExpr.scaleWith_eq, DenseLinExpr.scale_terms_fst,
                DenseLinExpr.normWith_eq] at hz
              exact Or.inl (DenseLinExpr.norm_terms_fst l1 z hz)
            · rw [if_neg h2] at h
              simp [GRes.toLin] at h

/-- The walk is eval-preserving: whenever it produces an affine form, that form agrees with the
    expression on every assignment the stored solutions are true of. -/
theorem gEval_eval (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p)))
    (denv : VarId → ZMod p)
    (hσ : ∀ i t, gSolFn sol i = some t → denv i = t.eval denv) :
    ∀ (e : DenseExpr p) (l : DenseLinExpr p), (gEval ops sol e).toLin = some l →
      e.eval denv = l.eval denv := by
  intro e
  induction e with
  | const n =>
      intro l h
      simp only [gEval, GRes.toLin, Option.some.injEq] at h
      subst h
      simp [DenseExpr.eval, DenseLinExpr.eval]
  | var x =>
      intro l h
      simp only [gEval] at h
      cases hx : gSolFn sol x with
      | none =>
          rw [hx] at h
          simp only [GRes.toLin, Option.some.injEq] at h
          subst h
          simp [DenseExpr.eval, DenseLinExpr.eval, ops.zero_eq, ops.one_eq]
      | some t =>
          rw [hx] at h
          simp only [GRes.toLin, Option.some.injEq] at h
          subst h
          exact hσ x t hx
  | add a b iha ihb =>
      intro l h
      simp only [gEval] at h
      cases ha : gEval ops sol a with
      | blk w => rw [ha] at h; simp [GRes.toLin] at h
      | cst c1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, hev⟩ := gAddRes_eval ops _ _ l h
          rw [DenseExpr.eval, iha la (by rw [ha]; exact hla), ihb lb hlb, hev]
      | lin l1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, hev⟩ := gAddRes_eval ops _ _ l h
          rw [DenseExpr.eval, iha la (by rw [ha]; exact hla), ihb lb hlb, hev]
  | mul a b iha ihb =>
      intro l h
      simp only [gEval] at h
      cases ha : gEval ops sol a with
      | blk w => rw [ha] at h; simp [GRes.toLin] at h
      | cst c1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, hev⟩ := gMulRes_eval ops _ _ l h
          rw [DenseExpr.eval, iha la (by rw [ha]; exact hla), ihb lb hlb, hev]
      | lin l1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, hev⟩ := gMulRes_eval ops _ _ l h
          rw [DenseExpr.eval, iha la (by rw [ha]; exact hla), ihb lb hlb, hev]

/-- The walk introduces no variable: every term variable of the result comes from the expression or
    from a stored solution. -/
theorem gEval_terms (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p)))
    (S : VarId → Prop) (hσ : ∀ i t, gSolFn sol i = some t → ∀ z ∈ t.terms.map Prod.fst, S z) :
    ∀ (e : DenseExpr p) (l : DenseLinExpr p), (gEval ops sol e).toLin = some l →
      (∀ z ∈ e.vars, S z) → ∀ z ∈ l.terms.map Prod.fst, S z := by
  intro e
  induction e with
  | const n =>
      intro l h _
      simp only [gEval, GRes.toLin, Option.some.injEq] at h
      subst h; intro z hz; simp at hz
  | var x =>
      intro l h he
      simp only [gEval] at h
      cases hx : gSolFn sol x with
      | none =>
          rw [hx] at h
          simp only [GRes.toLin, Option.some.injEq] at h
          subst h
          intro z hz
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hz
          rw [hz]
          exact he x (by simp [DenseExpr.vars])
      | some t =>
          rw [hx] at h
          simp only [GRes.toLin, Option.some.injEq] at h
          subst h
          exact hσ x t hx
  | add a b iha ihb =>
      intro l h he
      have hea : ∀ z ∈ a.vars, S z := fun z hz => he z (by simp [DenseExpr.vars, hz])
      have heb : ∀ z ∈ b.vars, S z := fun z hz => he z (by simp [DenseExpr.vars, hz])
      simp only [gEval] at h
      cases ha : gEval ops sol a with
      | blk w => rw [ha] at h; simp [GRes.toLin] at h
      | cst c1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, _⟩ := gAddRes_eval ops _ _ l h
          intro z hz
          rcases gAddRes_terms ops _ _ l la lb h hla hlb z hz with hz' | hz'
          · exact iha la (by rw [ha]; exact hla) hea z hz'
          · exact ihb lb hlb heb z hz'
      | lin l1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, _⟩ := gAddRes_eval ops _ _ l h
          intro z hz
          rcases gAddRes_terms ops _ _ l la lb h hla hlb z hz with hz' | hz'
          · exact iha la (by rw [ha]; exact hla) hea z hz'
          · exact ihb lb hlb heb z hz'
  | mul a b iha ihb =>
      intro l h he
      have hea : ∀ z ∈ a.vars, S z := fun z hz => he z (by simp [DenseExpr.vars, hz])
      have heb : ∀ z ∈ b.vars, S z := fun z hz => he z (by simp [DenseExpr.vars, hz])
      simp only [gEval] at h
      cases ha : gEval ops sol a with
      | blk w => rw [ha] at h; simp [GRes.toLin] at h
      | cst c1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, _⟩ := gMulRes_eval ops _ _ l h
          intro z hz
          rcases gMulRes_terms ops _ _ l la lb h hla hlb z hz with hz' | hz'
          · exact iha la (by rw [ha]; exact hla) hea z hz'
          · exact ihb lb hlb heb z hz'
      | lin l1 =>
          rw [ha] at h
          obtain ⟨la, lb, hla, hlb, _⟩ := gMulRes_eval ops _ _ l h
          intro z hz
          rcases gMulRes_terms ops _ _ l la lb h hla hlb z hz with hz' | hz'
          · exact iha la (by rw [ha]; exact hla) hea z hz'
          · exact ihb lb hlb heb z hz'

/-- `gRoot`'s row agrees with the constraint on every assignment the stored solutions are true of. -/
theorem gRoot_eval (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p)))
    (denv : VarId → ZMod p) (hσ : ∀ i t, gSolFn sol i = some t → denv i = t.eval denv)
    (e : DenseExpr p) (l : DenseLinExpr p) (h : gRoot ops sol e = .row l) :
    e.eval denv = l.eval denv := by
  simp only [gRoot] at h
  cases he : gEval ops sol e with
  | cst c =>
      rw [he] at h
      simp only [GTop.row.injEq] at h
      subst h
      exact gEval_eval ops sol denv hσ e _ (by rw [he]; rfl)
  | lin l1 =>
      rw [he] at h
      simp only [GTop.row.injEq] at h
      subst h
      rw [gEval_eval ops sol denv hσ e l1 (by rw [he]; rfl), DenseLinExpr.normWith_eq,
        DenseLinExpr.norm_eval]
  | blk w => rw [he] at h; simp at h

/-- `gRoot`'s row introduces no variable. -/
theorem gRoot_terms (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p)))
    (S : VarId → Prop) (hσ : ∀ i t, gSolFn sol i = some t → ∀ z ∈ t.terms.map Prod.fst, S z)
    (e : DenseExpr p) (l : DenseLinExpr p) (h : gRoot ops sol e = .row l)
    (he : ∀ z ∈ e.vars, S z) : ∀ z ∈ l.terms.map Prod.fst, S z := by
  simp only [gRoot] at h
  cases hev : gEval ops sol e with
  | cst c =>
      rw [hev] at h
      simp only [GTop.row.injEq] at h
      subst h
      intro z hz; simp at hz
  | lin l1 =>
      rw [hev] at h
      simp only [GTop.row.injEq] at h
      subst h
      intro z hz
      rw [DenseLinExpr.normWith_eq] at hz
      exact gEval_terms ops sol S hσ e l1 (by rw [hev]; rfl) he z
        (DenseLinExpr.norm_terms_fst l1 z hz)
  | blk w => rw [hev] at h; simp at h


/-! ## Array-index plumbing

Both invariants are stated over `getElem?`, so each write needs only "the entry is the new value, or
the one that was there before". -/

theorem gSolFn_set (sol : Array (Option (DenseLinExpr p))) (i : Nat) (v : Option (DenseLinExpr p))
    (x : VarId) :
    (i = x.index ∧ gSolFn (sol.setIfInBounds i v) x = v) ∨
      gSolFn (sol.setIfInBounds i v) x = gSolFn sol x := by
  unfold gSolFn
  by_cases hx : i = x.index
  · subst hx
    by_cases hi : x.index < sol.size
    · exact Or.inl ⟨rfl, by simp [hi]⟩
    · exact Or.inr (by
        simp [hi])
  · right; simp [hx]

theorem gRows_set (rows : Array (DenseLinExpr p)) (i : Nat) (l : DenseLinExpr p) (j : Nat)
    (l' : DenseLinExpr p) (h : (rows.setIfInBounds i l)[j]? = some l') :
    l' = l ∨ rows[j]? = some l' := by
  by_cases hj : i = j
  · subst hj
    by_cases hi : i < rows.size
    · rw [show (rows.setIfInBounds i l)[i]? = some l by
        simp [hi]] at h
      exact Or.inl (Option.some.inj h).symm
    · rw [show (rows.setIfInBounds i l)[i]? = rows[i]? by
        simp [hi]] at h
      exact Or.inr h
  · rw [show (rows.setIfInBounds i l)[j]? = rows[j]? by
      simp [hj]] at h
    exact Or.inr h

theorem gRows_replicate (n : Nat) (c : ZMod p) (j : Nat) (l : DenseLinExpr p)
    (h : (Array.replicate n (⟨c, []⟩ : DenseLinExpr p))[j]? = some l) : l = ⟨c, []⟩ := by
  by_cases hj : j < n
  · rw [show (Array.replicate n (⟨c, []⟩ : DenseLinExpr p))[j]? = some ⟨c, []⟩ by
      simp [hj]] at h
    exact (Option.some.inj h).symm
  · rw [show (Array.replicate n (⟨c, []⟩ : DenseLinExpr p))[j]? = none by
      simp [hj]] at h
    exact absurd h (by simp)

/-! ## The engine invariant -/

/-- Pending rows are entailed and occurrence-closed; stored solutions are entailed assignments with
    the same closure. Nothing else about the state is claimed. -/
structure GInv (bs : BusSemantics p) (d : DenseConstraintSystem p) (S : GSt p) : Prop where
  rows : ∀ (i : Nat) (l : DenseLinExpr p), S.rows[i]? = some l → GEnt bs d l ∧ GCl d l
  sol : ∀ (x : VarId) (t : DenseLinExpr p), gSolFn S.sol x = some t → GAsg bs d x t ∧ GCl d t

/-! ### Scheduling-only writes

`setStatus`, `setWoken` and `addWatch` rebuild the record without touching `rows` or `sol`, so they
preserve the invariant by projection. -/

@[simp] theorem setStatus_rows (S : GSt p) (i : Nat) (v : UInt8) :
    (S.setStatus i v).rows = S.rows := by cases S; rfl
@[simp] theorem setStatus_sol (S : GSt p) (i : Nat) (v : UInt8) :
    (S.setStatus i v).sol = S.sol := by cases S; rfl
@[simp] theorem clearWoken_rows (S : GSt p) (i : Nat) : (S.clearWoken i).rows = S.rows := by
  cases S; rfl
@[simp] theorem clearWoken_sol (S : GSt p) (i : Nat) : (S.clearWoken i).sol = S.sol := by
  cases S; rfl
@[simp] theorem addWatch_rows (S : GSt p) (i : Nat) (ws : List VarId) :
    (S.addWatch i ws).rows = S.rows := by cases S; rfl
@[simp] theorem addWatch_sol (S : GSt p) (i : Nat) (ws : List VarId) :
    (S.addWatch i ws).sol = S.sol := by cases S; rfl
@[simp] theorem setRow_sol (S : GSt p) (i : Nat) (l : DenseLinExpr p) :
    (S.setRow i l).sol = S.sol := by cases S; rfl
@[simp] theorem setRow_rows (S : GSt p) (i : Nat) (l : DenseLinExpr p) :
    (S.setRow i l).rows = S.rows.setIfInBounds i l := by cases S; rfl
@[simp] theorem setPending_sol (S : GSt p) (i : Nat) (l : DenseLinExpr p) :
    (S.setPending i l).sol = S.sol := by cases S; rfl
@[simp] theorem setPending_rows (S : GSt p) (i : Nat) (l : DenseLinExpr p) :
    (S.setPending i l).rows = S.rows.setIfInBounds i l := by cases S; rfl

theorem GInv.setStatus {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (i : Nat) (v : UInt8) : GInv bs d (S.setStatus i v) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.clearWoken {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (i : Nat) : GInv bs d (S.clearWoken i) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.addWatch {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (i : Nat) (ws : List VarId) : GInv bs d (S.addWatch i ws) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.setRow {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (i : Nat) (l : DenseLinExpr p) (hl : GEnt bs d l ∧ GCl d l) :
    GInv bs d (S.setRow i l) := by
  refine ⟨?_, by simpa using h.sol⟩
  intro j l' hj
  rw [setRow_rows] at hj
  rcases gRows_set S.rows i l j l' hj with rfl | hj'
  · exact hl
  · exact h.rows j l' hj'

theorem GInv.setPending {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (i : Nat) (l : DenseLinExpr p) (hl : GEnt bs d l ∧ GCl d l) :
    GInv bs d (S.setPending i l) := by
  refine ⟨?_, by simpa using h.sol⟩
  intro j l' hj
  rw [setPending_rows] at hj
  rcases gRows_set S.rows i l j l' hj with rfl | hj'
  · exact hl
  · exact h.rows j l' hj'


/-! ### Solution-map writes -/

@[simp] theorem setSol_rows (S : GSt p) (y : VarId) (v : Option (DenseLinExpr p)) :
    (S.setSol y v).rows = S.rows := by cases S; rfl
@[simp] theorem setSol_sol (S : GSt p) (y : VarId) (v : Option (DenseLinExpr p)) :
    (S.setSol y v).sol = S.sol.setIfInBounds y.index v := by cases S; rfl
@[simp] theorem pushRev_rows (S : GSt p) (t : DenseLinExpr p) (y : VarId) :
    (S.pushRev t y).rows = S.rows := by cases S; rfl
@[simp] theorem pushRev_sol (S : GSt p) (t : DenseLinExpr p) (y : VarId) :
    (S.pushRev t y).sol = S.sol := by cases S; rfl
@[simp] theorem clearRev_rows (S : GSt p) (x : VarId) : (S.clearRev x).rows = S.rows := by
  cases S; rfl
@[simp] theorem clearRev_sol (S : GSt p) (x : VarId) : (S.clearRev x).sol = S.sol := by
  cases S; rfl
@[simp] theorem fireWatch_rows (S : GSt p) (x : VarId) : (S.fireWatch x).rows = S.rows := by
  cases S; rfl
@[simp] theorem fireWatch_sol (S : GSt p) (x : VarId) : (S.fireWatch x).sol = S.sol := by
  cases S; rfl
@[simp] theorem pushOrder_rows (S : GSt p) (x : VarId) : (S.pushOrder x).rows = S.rows := by
  cases S; rfl
@[simp] theorem pushOrder_sol (S : GSt p) (x : VarId) : (S.pushOrder x).sol = S.sol := by
  cases S; rfl

theorem GInv.pushRev {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (t : DenseLinExpr p) (y : VarId) : GInv bs d (S.pushRev t y) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.clearRev {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (x : VarId) : GInv bs d (S.clearRev x) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.fireWatch {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (x : VarId) : GInv bs d (S.fireWatch x) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.pushOrder {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (x : VarId) : GInv bs d (S.pushOrder x) :=
  ⟨by simpa using h.rows, by simpa using h.sol⟩

theorem GInv.setSol {bs : BusSemantics p} {d : DenseConstraintSystem p} {S : GSt p}
    (h : GInv bs d S) (y : VarId) (t : DenseLinExpr p) (ht : GAsg bs d y t ∧ GCl d t) :
    GInv bs d (S.setSol y (some t)) := by
  refine ⟨by simpa using h.rows, ?_⟩
  intro x u hx
  rw [setSol_sol] at hx
  rcases gSolFn_set S.sol y.index (some t) x with ⟨hix, hset⟩ | hset
  · rw [hset] at hx
    have hu : t = u := Option.some.inj hx
    have hxy : y = x := by cases y; cases x; simp_all
    subst hu; subst hxy
    exact ht
  · rw [hset] at hx; exact h.sol x u hx

/-! ### Developing a row -/

/-- The stored solutions are all true at any satisfying assignment, so substituting them into a row
    preserves its value. -/
theorem gDevelop_ok (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (S : GSt p) (h : GInv bs d S) (r : DenseLinExpr p) (hr : GEnt bs d r ∧ GCl d r) :
    GEnt bs d (gDevelop ops S.sol r) ∧ GCl d (gDevelop ops S.sol r) := by
  unfold gDevelop
  split
  · refine ⟨?_, ?_⟩
    · intro denv hsat
      rw [denseLinSubstFWith_eq, denseLinSubstF_eval]
      have henv : denseLinEnv (gSolFn S.sol) denv = denv := by
        funext i
        cases hi : gSolFn S.sol i with
        | none => simp [denseLinEnv, hi]
        | some row => simp [denseLinEnv, hi, (h.sol i row hi).1 denv hsat]
      rw [henv]
      exact hr.1 denv hsat
    · rw [denseLinSubstFWith_eq]
      exact denseLinSubstF_terms_closed r _ (· ∈ d.occ) hr.2
        (fun i row hrow => (h.sol i row hrow).2)
  · exact hr

/-! ### The adoption step -/

theorem gSubst1_eq (ops : DenseZModOps p) (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p) :
    gSubst1 ops s x t = denseLinSubst s x t := by
  simp only [gSubst1, denseLinSubstFWith_eq, denseLinSubst]

theorem gRewriteStored_inv (ops : DenseZModOps p) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (x : VarId) (t : DenseLinExpr p) (ys : Array VarId)
    (ht : GAsg bs d x t ∧ GCl d t) :
    ∀ (k : Nat) (S : GSt p), GInv bs d S → GInv bs d (gRewriteStored ops x t ys k S) := by
  intro k
  induction k with
  | zero => intro S h; exact h
  | succ k ih =>
      intro S h
      rw [gRewriteStored]
      cases hy : ys[ys.size - (k + 1)]? with
      | none => simpa using ih S h
      | some y =>
          dsimp only
          cases hs : gSolFn S.sol y with
          | none => simpa using ih S h
          | some s =>
              dsimp only
              by_cases hm : s.mentions x
              · rw [if_pos hm]
                refine ih _ ((h.setSol y (gSubst1 ops s x t) ?_).pushRev t y)
                have hsy := h.sol y s hs
                refine ⟨?_, ?_⟩
                · intro denv hsat
                  rw [gSubst1_eq, denseLinSubst_eval s x t denv (ht.1 denv hsat)]
                  exact hsy.1 denv hsat
                · rw [gSubst1_eq]
                  exact denseLinSubst_terms_closed s x t (· ∈ d.occ) hsy.2 ht.2
              · rw [if_neg hm]
                exact ih S h

theorem gAdopt_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (S : GSt p) (h : GInv bs d S) (i : Nat) (x : VarId) (t : DenseLinExpr p)
    (ht : GAsg bs d x t ∧ GCl d t) : GInv bs d (gAdopt ops S i x t) := by
  rw [gAdopt]
  exact ((((gRewriteStored_inv ops bs d x t _ ht _ _ (h.clearRev x)).setSol x t
    ht).pushRev t x).fireWatch x).pushOrder x |>.setStatus i 2

/-! ### Taking a pivot -/

/-- `denseSparseSolveAt` always solves for the variable it was asked about. -/
theorem denseSparseSolveAt_fst (l : DenseLinExpr p) (y z : VarId) (t : DenseLinExpr p)
    (h : denseSparseSolveAt l y = some (z, t)) : z = y := by
  unfold denseSparseSolveAt at h
  split_ifs at h <;> simp_all

theorem gPick_solveAt (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (l : DenseLinExpr p) : ∀ (fuel : Nat) (banned : List VarId) (x : VarId) (t : DenseLinExpr p),
      gPick ops occ prot l fuel banned = some (x, t) → denseSparseSolveAt l x = some (x, t) := by
  intro fuel
  induction fuel with
  | zero => intro banned x t h; simp [gPick] at h
  | succ fuel ih =>
      intro banned x t h
      cases hb : gBestGo ops occ prot l.terms.length banned l.terms none with
      | none => simp [gPick, hb] at h
      | some y =>
          cases hs : denseSparseSolveAtWith ops l y with
          | none =>
              simp only [gPick, hb, hs] at h
              exact ih (y :: banned) x t h
          | some q =>
              simp only [gPick, hb, hs, Option.some.injEq] at h
              rw [denseSparseSolveAtWith_eq] at hs
              subst h
              have hxy : x = y := denseSparseSolveAt_fst l y x t hs
              subst hxy
              exact hs

/-- Whichever phase of the ladder-preferring pick returns, the result came from
    `denseSparseSolveAt`. -/
theorem gPickLadder_solveAt (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (l : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p)
    (h : gPickLadder ops occ prot l = some (x, t)) :
    denseSparseSolveAt l x = some (x, t) := by
  unfold gPickLadder at h
  split at h
  · exact gPick_solveAt ops occ prot l _ _ x t h
  · split at h
    · rename_i xt heq
      injection h with hxt
      subst hxt
      exact gPick_solveAt ops occ prot l _ _ x t heq
    · exact gPick_solveAt ops occ prot l _ _ x t h

theorem gTake_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) (S : GSt p) (h : GInv bs d S) (i : Nat)
    (l : DenseLinExpr p) (hl : GEnt bs d l ∧ GCl d l) :
    GInv bs d (gTake ops occ prot S i l) := by
  rw [gTake]
  split
  · exact h.setStatus i 2
  · cases hp : gPickLadder ops occ prot l with
    | none => simpa using h.setPending i l hl
    | some q =>
        obtain ⟨x, t⟩ := q
        dsimp only
        have hsolve := gPickLadder_solveAt ops occ prot l x t hp
        refine gAdopt_inv ops bs d S h i x t ⟨?_, ?_⟩
        · intro denv hsat
          exact denseSparseSolveAt_sound l x x t hsolve denv (hl.1 denv hsat)
        · intro z hz
          exact hl.2 z (denseSparseSolveAt_terms l x x t hsolve z hz)


/-! ## The schedulers

Both are plain recursions over the state, and the invariant is preserved by every step regardless of
the order they pick — which is exactly why the buckets, the watch lists and `occ`/`prot` need no
correctness argument. -/

theorem gVisit_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) (cs : Array (DenseExpr p))
    (hcs : ∀ (j : Nat) (c : DenseExpr p), cs[j]? = some c → c ∈ d.algebraicConstraints)
    (S : GSt p) (h : GInv bs d S) (i : Nat) : GInv bs d (gVisit ops occ prot cs S i) := by
  rw [gVisit]
  split
  · cases hr : S.rows[i]? with
    | none => simpa using h
    | some r =>
        dsimp only
        exact gTake_inv ops bs d occ prot S h i _ (gDevelop_ok ops bs d S h r (h.rows i r hr))
  · split
    · cases hc : cs[i]? with
      | none => simpa using h.clearWoken i
      | some c =>
          dsimp only
          have hcm : c ∈ d.algebraicConstraints := hcs i c hc
          have h' : GInv bs d (S.clearWoken i) := h.clearWoken i
          cases hg : gRoot ops (S.clearWoken i).sol c with
          | blocked ws => simpa using h'.addWatch i ws
          | row l =>
              dsimp only
              refine gTake_inv ops bs d occ prot _ h' i l ⟨?_, ?_⟩
              · intro denv hsat
                have hσ : ∀ (j : VarId) (t : DenseLinExpr p),
                    gSolFn (S.clearWoken i).sol j = some t → denv j = t.eval denv :=
                  fun j t hj => (h'.sol j t hj).1 denv hsat
                rw [← gRoot_eval ops _ denv hσ c l hg]
                exact hsat.1 c hcm
              · refine gRoot_terms ops _ (· ∈ d.occ)
                  (fun j t hj => (h'.sol j t hj).2) c l hg ?_
                intro z hz
                exact DenseConstraintSystem.mem_occ_of_constraint hcm hz
    · exact h

theorem gBuildGo_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (cs : Array (DenseExpr p))
    (hcs : ∀ (j : Nat) (c : DenseExpr p), cs[j]? = some c → c ∈ d.algebraicConstraints) :
    ∀ (k : Nat) (S : GSt p), GInv bs d S → GInv bs d (gBuildGo ops cs k S) := by
  intro k
  induction k with
  | zero => intro S h; exact h
  | succ k ih =>
      intro S h
      rw [gBuildGo]
      refine ih _ ?_
      cases hc : cs[cs.size - (k + 1)]? with
      | none => simpa using h
      | some c =>
          dsimp only
          have hcm : c ∈ d.algebraicConstraints := hcs _ c hc
          cases hg : gRoot ops S.sol c with
          | blocked ws => simpa using h.addWatch _ ws
          | row l =>
              have hl : GEnt bs d l ∧ GCl d l := by
                refine ⟨?_, ?_⟩
                · intro denv hsat
                  have hσ : ∀ (j : VarId) (t : DenseLinExpr p),
                      gSolFn S.sol j = some t → denv j = t.eval denv :=
                    fun j t hj => (h.sol j t hj).1 denv hsat
                  rw [← gRoot_eval ops _ denv hσ c l hg]
                  exact hsat.1 c hcm
                · refine gRoot_terms ops _ (· ∈ d.occ) (fun j t hj => (h.sol j t hj).2) c l hg ?_
                  intro z hz
                  exact DenseConstraintSystem.mem_occ_of_constraint hcm hz
              dsimp only
              split
              · exact h.setStatus _ 2
              · exact h.setPending _ l hl

theorem gSweepGo_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) (cs : Array (DenseExpr p))
    (hcs : ∀ (j : Nat) (c : DenseExpr p), cs[j]? = some c → c ∈ d.algebraicConstraints) :
    ∀ (k : Nat) (S : GSt p), GInv bs d S → GInv bs d (gSweepGo ops occ prot cs k S) := by
  intro k
  induction k with
  | zero => intro S h; exact h
  | succ k ih =>
      intro S h
      rw [gSweepGo]
      exact ih _ (gVisit_inv ops bs d occ prot cs hcs S h _)

theorem gDrainAt_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) (S : GSt p) (q : GQueue) (prog : Bool) (b i : Nat)
    (h : GInv bs d S) : GInv bs d (gDrainAt ops occ prot S q prog b i).1 := by
  rw [gDrainAt]
  split
  · exact h
  · cases hr : S.rows[i]? with
    | none => simpa using h
    | some r =>
        dsimp only
        have hl := gDevelop_ok ops bs d S h r (h.rows i r hr)
        split
        · exact h.setStatus i 2
        · split
          · exact h.setRow i _ hl
          · exact gTake_inv ops bs d occ prot S h i _ hl

theorem gDrainStep_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) (S : GSt p) (q : GQueue) (prog : Bool)
    (h : GInv bs d S) : GInv bs d (gDrainStep ops occ prot S q prog).1 := by
  rw [gDrainStep]
  split
  · exact h
  · split
    · exact h
    · exact gDrainAt_inv ops bs d occ prot S _ prog _ _ h

theorem gDrainGo_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) :
    ∀ (fuel : Nat) (S : GSt p) (q : GQueue) (prog : Bool), GInv bs d S →
      GInv bs d (gDrainGo ops occ prot fuel S q prog).1 := by
  intro fuel
  induction fuel with
  | zero => intro S q prog h; exact h
  | succ fuel ih =>
      intro S q prog h
      rw [gDrainGo]
      cases hb : q.next (gMaxBucket + 1) with
      | none => simpa using h
      | some b =>
          dsimp only
          have hs := gDrainStep_inv ops bs d occ prot S q prog h
          cases hst : gDrainStep ops occ prot S q prog with
          | mk S1 rest =>
              cases rest with
              | mk q1 prog1 =>
                  rw [hst] at hs
                  dsimp only
                  exact ih S1 q1 prog1 hs

theorem gWakeGo_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (cs : Array (DenseExpr p))
    (hcs : ∀ (j : Nat) (c : DenseExpr p), cs[j]? = some c → c ∈ d.algebraicConstraints) :
    ∀ (k : Nat) (S : GSt p) (q : GQueue) (prog : Bool), GInv bs d S →
      GInv bs d (gWakeGo ops cs k S q prog).1 := by
  intro k
  induction k with
  | zero => intro S q prog h; exact h
  | succ k ih =>
      intro S q prog h
      rw [gWakeGo]
      split
      · cases hc : cs[cs.size - (k + 1)]? with
        | none => simpa using ih _ _ _ (h.clearWoken _)
        | some c =>
            dsimp only
            have hcm : c ∈ d.algebraicConstraints := hcs _ c hc
            have h' : GInv bs d (S.clearWoken (cs.size - (k + 1))) := h.clearWoken _
            cases hg : gRoot ops (S.clearWoken (cs.size - (k + 1))).sol c with
            | blocked ws => simpa using ih _ _ _ (h'.addWatch _ ws)
            | row l =>
                have hl : GEnt bs d l ∧ GCl d l := by
                  refine ⟨?_, ?_⟩
                  · intro denv hsat
                    have hσ : ∀ (j : VarId) (t : DenseLinExpr p),
                        gSolFn (S.clearWoken (cs.size - (k + 1))).sol j = some t →
                        denv j = t.eval denv :=
                      fun j t hj => (h'.sol j t hj).1 denv hsat
                    rw [← gRoot_eval ops _ denv hσ c l hg]
                    exact hsat.1 c hcm
                  · refine gRoot_terms ops _ (· ∈ d.occ) (fun j t hj => (h'.sol j t hj).2) c l hg ?_
                    intro z hz
                    exact DenseConstraintSystem.mem_occ_of_constraint hcm hz
                dsimp only
                split
                · exact ih _ _ _ (h'.setStatus _ 2)
                · exact ih _ _ _ (h'.setPending _ l hl)
      · exact ih _ _ _ h

theorem gRoundsGo_inv (ops : DenseZModOps p) (bs : BusSemantics p) (d : DenseConstraintSystem p)
    (occ : Array Nat) (prot : Array Bool) (cs : Array (DenseExpr p))
    (hcs : ∀ (j : Nat) (c : DenseExpr p), cs[j]? = some c → c ∈ d.algebraicConstraints) :
    ∀ (round : Nat) (S : GSt p) (q : GQueue), GInv bs d S →
      GInv bs d (gRoundsGo ops occ prot cs round S q) := by
  intro round
  induction round with
  | zero => intro S q h; exact h
  | succ round ih =>
      intro S q h
      rw [gRoundsGo]
      have hd := gDrainGo_inv ops bs d occ prot ((gMaxBucket + 2) * cs.size + 8) S q false h
      cases hdd : gDrainGo ops occ prot ((gMaxBucket + 2) * cs.size + 8) S q false with
      | mk S1 rest1 =>
          cases rest1 with
          | mk q1 prog1 =>
              rw [hdd] at hd
              cases hww : gWakeGo ops cs cs.size S1 q1 false with
              | mk S2 rest2 =>
                  cases rest2 with
                  | mk q2 prog2 =>
                      have hw := gWakeGo_inv ops bs d cs hcs cs.size S1 q1 false hd
                      rw [hww] at hw
                      simp only [hww]
                      split
                      · exact ih _ _ hw
                      · exact hw

theorem GSt_empty_inv (bs : BusSemantics p) (d : DenseConstraintSystem p) (nc nv : Nat) :
    GInv bs d (GSt.empty nc nv : GSt p) := by
  constructor
  · intro i l hi
    rw [GSt.empty] at hi
    rw [gRows_replicate nc _ i l hi]
    refine ⟨?_, GCl_nil d _⟩
    intro denv _
    simp [DenseLinExpr.eval, zmodZeroP_eq]
  · intro x t hx
    rw [GSt.empty] at hx
    unfold gSolFn at hx
    by_cases hlt : x.index < nv
    · rw [show (Array.replicate nv (none : Option (DenseLinExpr p)))[x.index]? = some none by
        simp [hlt]] at hx
      exact absurd hx (by simp)
    · rw [show (Array.replicate nv (none : Option (DenseLinExpr p)))[x.index]? = none by
        simp [hlt]] at hx
      exact absurd hx (by simp)

/-! ## The solved map -/

theorem gSolveSystem_inv (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    GInv bs d (gSolveSystem bs d) := by
  have hcs : ∀ (j : Nat) (c : DenseExpr p),
      d.algebraicConstraints.toArray[j]? = some c → c ∈ d.algebraicConstraints := by
    intro j c hj
    rw [List.getElem?_toArray] at hj
    exact List.mem_of_getElem? hj
  rw [gSolveSystem]
  cases hp : gPrepare bs d with
  | mk occ prot =>
      dsimp only
      split
      · rw [gRun]
        exact gSweepGo_inv _ bs d occ prot _ hcs _ _
          (gSweepGo_inv _ bs d occ prot _ hcs _ _
            (gBuildGo_inv _ bs d _ hcs _ _ (GSt_empty_inv bs d _ _)))
      · rw [gRunFill]
        exact gRoundsGo_inv _ bs d occ prot _ hcs _ _ _
          (gBuildGo_inv _ bs d _ hcs _ _ (GSt_empty_inv bs d _ _))

theorem gOutFn_set (out : Array (Option (DenseExpr p))) (i : Nat) (v : Option (DenseExpr p))
    (x : VarId) :
    (i = x.index ∧ gOutFn (out.setIfInBounds i v) x = v) ∨
      gOutFn (out.setIfInBounds i v) x = gOutFn out x := by
  unfold gOutFn
  by_cases hx : i = x.index
  · subst hx
    by_cases hi : x.index < out.size
    · exact Or.inl ⟨rfl, by simp [hi]⟩
    · exact Or.inr (by
        simp [hi])
  · right; simp [hx]

/-- Every entry the output array carries is a stored solution's expression. -/
theorem gOutGo_spec (S : GSt p) :
    ∀ (k : Nat) (out : Array (Option (DenseExpr p))),
      (∀ (i : VarId) (e : DenseExpr p), gOutFn out i = some e →
        ∃ l, gSolFn S.sol i = some l ∧ e = l.toExpr) →
      ∀ (i : VarId) (e : DenseExpr p), gOutFn (gOutGo S k out) i = some e →
        ∃ l, gSolFn S.sol i = some l ∧ e = l.toExpr := by
  intro k
  induction k with
  | zero => intro out hout i e h; exact hout i e h
  | succ k ih =>
      intro out hout i e h
      rw [gOutGo] at h
      refine ih _ ?_ i e h
      cases hx : S.order[S.order.size - (k + 1)]? with
      | none => simpa [hx] using hout
      | some x =>
          dsimp only
          cases hs : gSolFn S.sol x with
          | none => simpa using hout
          | some l =>
              dsimp only
              intro j e' hj
              rcases gOutFn_set out x.index (some l.toExpr) j with ⟨hix, hset⟩ | hset
              · rw [hset] at hj
                have he : l.toExpr = e' := Option.some.inj hj
                have hxj : x = j := by cases x; cases j; simp_all
                subst hxj; subst he
                exact ⟨l, hs, rfl⟩
              · rw [hset] at hj
                exact hout j e' hj

theorem gOutOf_spec (S : GSt p) (i : VarId) (e : DenseExpr p) (h : gOutFn (gOutOf S) i = some e) :
    ∃ l, gSolFn S.sol i = some l ∧ e = l.toExpr := by
  refine gOutGo_spec S S.order.size _ ?_ i e h
  intro j e' hj
  unfold gOutFn at hj
  by_cases hlt : j.index < S.sol.size
  · rw [show (Array.replicate S.sol.size (none : Option (DenseExpr p)))[j.index]? = some none by
      simp [hlt]] at hj
    exact absurd hj (by simp)
  · rw [show (Array.replicate S.sol.size (none : Option (DenseExpr p)))[j.index]? = none by
      simp [hlt]] at hj
    exact absurd hj (by simp)

/-- The two facts the spec asks of a substitution pass: the map is entailed and closed. -/
theorem denseGaussElimF_map (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    (∀ denv, d.satisfies bs denv → ∀ (i : VarId) (e : DenseExpr p),
        gOutFn (gOutOf (gSolveSystem bs d)) i = some e → denv i = e.eval denv) ∧
    (∀ (i : VarId) (e : DenseExpr p), gOutFn (gOutOf (gSolveSystem bs d)) i = some e →
        ∀ z ∈ e.vars, z ∈ d.occ) := by
  have hinv := gSolveSystem_inv bs d
  refine ⟨?_, ?_⟩
  · intro denv hsat i e he
    obtain ⟨l, hl, rfl⟩ := gOutOf_spec _ i e he
    rw [DenseLinExpr.toExpr_eval]
    exact (hinv.sol i l hl).1 denv hsat
  · intro i e he z hz
    obtain ⟨l, hl, rfl⟩ := gOutOf_spec _ i e he
    exact (hinv.sol i l hl).2 z (DenseLinExpr.toExpr_vars l z hz)

/-! ## The pass -/

theorem denseGaussElimF_eq (bs : BusSemantics p) (d : DenseConstraintSystem p) :
    denseGaussElimF bs d =
      if (gSolveSystem bs d).order.isEmpty then d
      else d.substF (gOutFn (gOutOf (gSolveSystem bs d))) := rfl

theorem denseGaussElimF_covered (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) : (denseGaussElimF bs d).CoveredBy reg := by
  rw [denseGaussElimF_eq]
  split_ifs with hempty
  · exact hcov
  · refine DenseConstraintSystem.substF_covered hcov ?_
    intro i _ t hti z hz
    exact DenseConstraintSystem.occ_valid hcov z ((denseGaussElimF_map bs d).2 i t hti z hz)

/-- **Correctness of `denseGaussElimF`.** The empty-map branch is the identity; the substitution
    branch is `substF_denseCorrect`, fed the entailment and occurrence closure of the solved map. -/
theorem denseGaussElimF_correct (reg : VarRegistry) (bs : BusSemantics p)
    (d : DenseConstraintSystem p) : DensePassCorrect reg.isInput d (denseGaussElimF bs d) [] bs := by
  have hmap := denseGaussElimF_map bs d
  rw [denseGaussElimF_eq]
  split_ifs with hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DenseConstraintSystem.substF_denseCorrect d _ bs reg.isInput
      (fun denv hsat i t hti => hmap.1 denv hsat i t hti)
      (fun i t hti z hz => hmap.2 i t hti z hz)

/-- The wired dense Gauss-elimination pass (transform `denseGaussElimF`, `Gauss.lean`). -/
def denseGaussElimFPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun bs _ d => denseGaussElimF bs d)
    (fun _ _ _ => [])
    (fun reg bs _ d hcov => denseGaussElimF_covered reg bs d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => denseGaussElimF_correct reg bs d)

end ApcOptimizer.Dense
