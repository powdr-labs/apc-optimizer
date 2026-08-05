import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.RootPairUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DropPasses

set_option autoImplicit false

/-! # Witness re-encoding — correctness.

The full `DensePassCorrect` proof for the `Reencode` pass over dense environments `VarId → ZMod p`:
structure lemmas, the transport core `DenseConstraintSystem.reencode_correct_D`, the capstone
`denseCheckReencode_sound`, and the step/loop/pass assembly. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- On the keys, `denseEnvExt` agrees with `denseEnvOfFast`. -/
theorem denseEnvExt_eq_envOfFast_of_mem (pairs : List (VarId × ZMod p)) (denv : VarId → ZMod p)
    (y : VarId) (h : y ∈ pairs.map Prod.fst) : denseEnvExt pairs denv y = denseEnvOfFast pairs y := by
  induction pairs with
  | nil => simp at h
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [denseEnvExt, denseEnvOfFast]
    by_cases hyx : y = x
    · rw [if_pos hyx, if_pos (by simp [hyx])]
    · rw [if_neg hyx, if_neg (by simpa using hyx)]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hyx
      · exact h

/-- Off the keys, `denseEnvExt` is `denv`. -/
theorem denseEnvExt_eq_env_of_notmem (pairs : List (VarId × ZMod p)) (denv : VarId → ZMod p)
    (y : VarId) (h : y ∉ pairs.map Prod.fst) : denseEnvExt pairs denv y = denv y := by
  induction pairs with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨x, v⟩ := t
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [denseEnvExt, if_neg h.1]
    exact ih h.2

theorem denseMentions_false_not_mem_vars (i : VarId) (e : DenseExpr p)
    (h : e.mentions i = false) : i ∉ e.vars := by
  induction e with
  | const n => simp [DenseExpr.vars]
  | var j =>
      simp only [DenseExpr.mentions] at h
      simp only [DenseExpr.vars, List.mem_singleton]
      intro hij
      subst hij
      simp at h
  | add a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx
  | mul a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (hx | hx)
      · exact iha h.1 hx
      · exact ihb h.2 hx

theorem DenseExpr.evalWith_eq (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (denv : VarId → ZMod p) (e : DenseExpr p) : e.evalWith add mul denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp only [DenseExpr.evalWith, DenseExpr.eval, hadd, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.evalWith, DenseExpr.eval, hmul, iha, ihb]

theorem DenseExpr.evalFast_eq (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.evalFast denv = e.eval denv :=
  DenseExpr.evalWith_eq zmodAdd zmodMul (fun _ _ => zmodAdd_eq _ _) (fun _ _ => zmodMul_eq _ _)
    denv e

theorem denseBoolConstraint_eval_of_bool (b : VarId) (denv : VarId → ZMod p)
    (h : denv b = 0 ∨ denv b = 1) : (denseBoolConstraint b).eval denv = 0 := by
  show denv b * (denv b + (-1)) = 0
  rcases h with h | h <;> rw [h] <;> ring

theorem dense_bool_of_boolConstraint_eval [Fact p.Prime] (b : VarId) (denv : VarId → ZMod p)
    (h : (denseBoolConstraint b).eval denv = 0) : denv b = 0 ∨ denv b = 1 := by
  have h' : denv b * (denv b + (-1)) = 0 := h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · right
    linear_combination h1

/-- Every enumerated assignment has the domains' keys, in order. -/
theorem denseAssignments_keys (doms : List (VarId × List (ZMod p)))
    (a : List (VarId × ZMod p)) (h : a ∈ denseAssignments doms) :
    a.map Prod.fst = doms.map Prod.fst := by
  induction doms generalizing a with
  | nil =>
      simp only [denseAssignments, List.mem_singleton] at h
      subst h
      rfl
  | cons xd rest ih =>
    obtain ⟨x, d⟩ := xd
    simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp [ih a' ha']

/-- Every enumerated assignment's value at a (distinct-keyed) domain entry lies in that domain. -/
theorem denseEnvOf_mem_of_assignments (doms : List (VarId × List (ZMod p)))
    (hnd : (doms.map Prod.fst).Nodup) (a : List (VarId × ZMod p))
    (h : a ∈ denseAssignments doms) : ∀ xd ∈ doms, denseEnvOfFast a xd.1 ∈ xd.2 := by
  induction doms generalizing a with
  | nil => simp
  | cons xd0 rest ih =>
    obtain ⟨x, d⟩ := xd0
    simp only [denseAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a', ha', v, hv, rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons] at hnd
    intro yd hyd
    rcases List.mem_cons.1 hyd with rfl | hyd
    · rw [denseEnvOfFast, if_pos (show (x == x) = true by simp)]
      exact hv
    · have hne : yd.1 ≠ x := by
        intro heq
        exact hnd.1 (heq ▸ List.mem_map.2 ⟨yd, hyd, rfl⟩)
      have hbf : (yd.1 == x) = false := beq_eq_false_iff_ne.mpr hne
      rw [denseEnvOfFast, if_neg (by simp [hbf])]
      exact ih hnd.2 a' ha' yd hyd

/-- `denseEnvOfFast` of a zipped image list reads off the image function. -/
theorem denseEnvOf_zipimg (xs : List VarId) (g : VarId → ZMod p) (y : VarId) (hy : y ∈ xs) :
    denseEnvOfFast (xs.map (fun x => (x, g x))) y = g y := by
  induction xs with
  | nil => simp at hy
  | cons x rest ih =>
    simp only [List.map_cons, denseEnvOfFast]
    by_cases hyx : y = x
    · rw [if_pos (by simp [hyx]), hyx]
    · rw [if_neg (by simp [hyx])]
      exact ih (by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h hyx
        · exact h)

/-- `denseEnvF` at any variable is the evaluation of the substituted variable expression. -/
theorem denseEnvF_eq_varSubst (σ : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p)
    (y : VarId) : denseEnvF σ denv y = ((DenseExpr.var y).substF σ).eval denv := by
  show (match σ y with | some t => t.eval denv | none => denv y)
    = ((match σ y with | some t => t | none => .var y) : DenseExpr p).eval denv
  cases σ y <;> rfl

/-- Expression-level agreement from pointwise environment agreement. -/
theorem denseSubstF_eval_agree (σ : VarId → Option (DenseExpr p)) (denv₀ denv₁ : VarId → ZMod p)
    (e : DenseExpr p) (h : ∀ y ∈ e.vars, denseEnvF σ denv₀ y = denv₁ y) :
    (e.substF σ).eval denv₀ = e.eval denv₁ := by
  rw [DenseExpr.eval_substF]
  exact DenseExpr.eval_congr e _ _ h

theorem denseContainsFast_of_mem (xs : List VarId) (y : VarId) (h : y ∈ xs) :
    denseContainsFast xs y = true := by
  induction xs with
  | nil => simp at h
  | cons x rest ih =>
    simp only [denseContainsFast, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (by simp)
    · exact Or.inr (ih h)

/-- Substituting a wholly-in-group expression (whose group variables `σfn` maps into the bits)
    yields an expression over the bits only. -/
theorem DenseExpr.substF_varsIn_bits (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) (hin : e.varsInF xs = true) :
    ∀ v ∈ (e.substF σfn).vars, v ∈ bits := by
  induction e with
  | const n => intro v hv; simp [DenseExpr.substF, DenseExpr.vars] at hv
  | var y =>
      intro v hv
      exact hσ y (denseContainsFast_sound xs y (by simpa [DenseExpr.varsInF] using hin)) v hv
  | add a b iha ihb =>
      rw [DenseExpr.varsInF, Bool.and_eq_true] at hin
      intro v hv
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv
  | mul a b iha ihb =>
      rw [DenseExpr.varsInF, Bool.and_eq_true] at hin
      intro v hv
      simp only [DenseExpr.substF, DenseExpr.vars, List.mem_append] at hv
      rcases hv with hv | hv
      · exact iha hin.1 v hv
      · exact ihb hin.2 v hv

/-- Interpolation candidate agreement: on a bit pattern that agrees with `denv₀` and off which the
    substitution map matches `denv₁`, the checked interpolation candidate evaluates as the
    original. -/
theorem denseGroupRewriteCand_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (e : DenseExpr p) (hin : e.varsInF xs = true)
    (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (denseGroupRewriteCand bits σfn patts e).eval denv₀ = e.eval denv₁ := by
  have hnotbits : ∀ y ∈ e.vars, y ∉ bits := by
    intro y hy hyb
    exact absurd hy (denseMentions_false_not_mem_vars y e (hfresh y hyb))
  have hsubstF : (e.substF σfn).eval denv₀ = e.eval denv₁ := by
    rw [DenseExpr.eval_substF]
    apply DenseExpr.eval_congr
    intro y hy
    exact hpoint y (hnotbits y hy)
  simp only [denseGroupRewriteCand]
  unfold denseCandSelect
  split
  · next hchk =>
    rw [Bool.and_eq_true] at hchk
    have hβ := of_decide_eq_true (List.all_eq_true.mp hchk.2 _
      (zip_map_self_mem (fun aβ => (e.substF σfn).evalFast (denseEnvOfFast aβ)) patts aβ haβ))
    have hchk1 := hchk.1
    simp only [DenseExpr.evalFast_eq] at hβ hchk1 ⊢
    have hcvars : ∀ v ∈ ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).vars, v ∈ bits :=
      denseVarsInF_sound bits _ hchk1
    have h₀β : ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).eval denv₀
        = ((denseInterpOfV patts (patts.map (fun aβ =>
          (e.substF σfn).eval (denseEnvOfFast aβ)))).fold).eval (denseEnvOfFast aβ) := by
      apply DenseExpr.eval_congr
      intro v hv
      exact hbitsagree v (hcvars v hv)
    rw [h₀β, hβ, DenseExpr.eval_substF]
    apply DenseExpr.eval_congr
    intro y hy
    have hyx : y ∈ xs := denseVarsInF_sound xs e hin y hy
    rw [denseEnvF_eq_varSubst]
    have hstep : ((DenseExpr.var y).substF σfn).eval (denseEnvOfFast aβ)
        = ((DenseExpr.var y).substF σfn).eval denv₀ := by
      apply DenseExpr.eval_congr
      intro v hv
      exact (hbitsagree v (hpolyvars y hyx v hv)).symm
    rw [hstep, ← denseEnvF_eq_varSubst]
    exact hpoint y (hnotbits y hy)
  · exact hsubstF

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else, agreeing pointwise with the original. -/
theorem denseGroupRewrite_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (e : DenseExpr p) (hfresh : ∀ b ∈ bits, e.mentions b = false) :
    (denseGroupRewrite xs bits σfn patts e).eval denv₀ = e.eval denv₁ := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [denseGroupRewrite]
      by_cases hyx : denseContainsFast xs y = true
      · rw [if_pos hyx]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.var y)
          (show (DenseExpr.var y).varsInF xs = true from hyx) hfresh
      · rw [if_neg hyx]
        have hyxs : y ∉ xs := fun h => hyx (denseContainsFast_of_mem xs y h)
        have hynb : y ∉ bits := by
          intro hyb
          have := hfresh y hyb
          simp [DenseExpr.mentions] at this
        have := hpoint y hynb
        unfold denseEnvF at this
        rw [hσnone y hyxs] at this
        show (DenseExpr.var y).eval denv₀ = (DenseExpr.var y).eval denv₁
        exact this
  | add a b iha ihb =>
      simp only [denseGroupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.add a b) hin hfresh
      · rw [if_neg hin]
        show ((denseGroupRewrite xs bits σfn patts a).eval denv₀)
          + ((denseGroupRewrite xs bits σfn patts b).eval denv₀) = a.eval denv₁ + b.eval denv₁
        rw [iha hfa, ihb hfb]
  | mul a b iha ihb =>
      simp only [denseGroupRewrite]
      have hfa : ∀ c ∈ bits, a.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.1
      have hfb : ∀ c ∈ bits, b.mentions c = false := by
        intro c hc
        have := hfresh c hc
        simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at this
        exact this.2
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]
        exact denseGroupRewriteCand_agree xs bits σfn patts denv₀ denv₁ aβ haβ hbitsagree
          hpolyvars hpoint (.mul a b) hin hfresh
      · rw [if_neg hin]
        show ((denseGroupRewrite xs bits σfn patts a).eval denv₀)
          * ((denseGroupRewrite xs bits σfn patts b).eval denv₀) = a.eval denv₁ * b.eval denv₁
        rw [iha hfa, ihb hfb]

/-- Bus-interaction-level agreement for the group rewrite, over the field-by-field inlined rewrite
    that `denseReencodeOut` produces (there is no dense `BusInteraction.mapExpr`). -/
theorem denseGroupRewrite_bi_agree (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσnone : ∀ y, y ∉ xs → σfn y = none)
    (denv₀ denv₁ : VarId → ZMod p) (aβ : List (VarId × ZMod p)) (haβ : aβ ∈ patts)
    (hbitsagree : ∀ b ∈ bits, denv₀ b = denseEnvOfFast aβ b)
    (hpolyvars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (hpoint : ∀ y, y ∉ bits → denseEnvF σfn denv₀ y = denv₁ y)
    (bi : BusInteraction (DenseExpr p))
    (hfreshM : ∀ b ∈ bits, bi.multiplicity.mentions b = false)
    (hfreshP : ∀ e ∈ bi.payload, ∀ b ∈ bits, e.mentions b = false) :
    denseBIEval { bi with
        multiplicity := denseGroupRewrite xs bits σfn patts bi.multiplicity,
        payload := bi.payload.map (denseGroupRewrite xs bits σfn patts) } denv₀
      = denseBIEval bi denv₁ := by
  unfold denseBIEval
  congr 1
  · exact denseGroupRewrite_agree xs bits σfn patts hσnone denv₀ denv₁ aβ haβ hbitsagree
      hpolyvars hpoint bi.multiplicity hfreshM
  · rw [List.map_map]
    refine List.map_congr_left (fun e he => ?_)
    simp only [Function.comp_apply]
    exact denseGroupRewrite_agree xs bits σfn patts hσnone denv₀ denv₁ aβ haβ hbitsagree
      hpolyvars hpoint e (hfreshP e he)

/-- A rewritten wholly-in-group expression is over the bits only. -/
theorem denseGroupRewriteCand_vars (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) (hin : e.varsInF xs = true) :
    ∀ v ∈ (denseGroupRewriteCand bits σfn patts e).vars, v ∈ bits := by
  intro v hv
  simp only [denseGroupRewriteCand] at hv
  unfold denseCandSelect at hv
  split at hv
  · next hchk =>
      rw [Bool.and_eq_true] at hchk
      exact denseVarsInF_sound bits _ hchk.1 v hv
  · exact DenseExpr.substF_varsIn_bits xs bits σfn hσ e hin v hv

/-- Every variable of a group-rewritten expression is either an original variable of `e` or a
    fresh bit. -/
theorem denseGroupRewrite_vars (xs bits : List VarId)
    (σfn : VarId → Option (DenseExpr p)) (patts : List (List (VarId × ZMod p)))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF σfn).vars, v ∈ bits)
    (e : DenseExpr p) :
    ∀ v ∈ (denseGroupRewrite xs bits σfn patts e).vars, v ∈ e.vars ∨ v ∈ bits := by
  induction e with
  | const n => simp [denseGroupRewrite, DenseExpr.vars]
  | var y =>
      simp only [denseGroupRewrite]
      by_cases hyx : denseContainsFast xs y = true
      · rw [if_pos hyx]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.var y)
          (show (DenseExpr.var y).varsInF xs = true from hyx) v hv)
      · rw [if_neg hyx]; intro v hv; exact Or.inl hv
  | add a b iha ihb =>
      simp only [denseGroupRewrite]
      by_cases hin : (DenseExpr.add a b).varsInF xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.add a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [DenseExpr.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
  | mul a b iha ihb =>
      simp only [denseGroupRewrite]
      by_cases hin : (DenseExpr.mul a b).varsInF xs = true
      · rw [if_pos hin]; intro v hv
        exact Or.inr (denseGroupRewriteCand_vars xs bits σfn patts hσ (.mul a b) hin v hv)
      · rw [if_neg hin]; intro v hv
        simp only [DenseExpr.vars, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · rcases iha v hv with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · rcases ihb v hv with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h

/-- Every variable of the re-encoded system is either an original variable of `d` or a fresh bit —
    proven by construction from the certified substitution, so the pass needs no scan. -/
theorem denseReencodeOut_vars_subset (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p))
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits) :
    ∀ v ∈ (denseReencodeOut d xs bits hm).occ, v ∈ d.occ ∨ v ∈ bits := by
  intro v hv
  have gr := denseGroupRewrite_vars xs bits (denseGroupSubst xs hm)
    (denseAssignments (denseBitBox bits)) hσ
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hv
  rcases hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · simp only [denseReencodeOut, List.mem_append] at hc
    rcases hc with hc | hc
    · rcases List.mem_map.1 hc with ⟨c0, hc0, rfl⟩
      rcases gr c0 v hcv with h | h
      · exact Or.inl (DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc0) h)
      · exact Or.inr h
    · rcases List.mem_map.1 hc with ⟨b, hb, rfl⟩
      right
      have hvb : v = b := by simpa [denseBoolConstraint, DenseExpr.vars] using hcv
      exact hvb ▸ hb
  · simp only [denseReencodeOut, List.mem_map] at hbi
    rcases hbi with ⟨bi0, hbi0, rfl⟩
    simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hbiv
    rcases hbiv with hmv | ⟨e, he, hev⟩
    · rcases gr bi0.multiplicity v hmv with h | h
      · refine Or.inl (DenseConstraintSystem.mem_occ_of_bi hbi0 ?_)
        simp only [denseBIVars, List.mem_append]; exact Or.inl h
      · exact Or.inr h
    · rcases List.mem_map.1 he with ⟨e0, he0, rfl⟩
      rcases gr e0 v hev with h | h
      · refine Or.inl (DenseConstraintSystem.mem_occ_of_bi hbi0 ?_)
        simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e0, he0, h⟩
      · exact Or.inr h

/-- A dense computation method reads only its variables. -/
theorem DenseComputationMethod.eval_congr (cm : DenseComputationMethod p) (e1 e2 : VarId → ZMod p) :
    (∀ v ∈ cm.vars, e1 v = e2 v) → cm.eval e1 = cm.eval e2 := by
  induction cm with
  | const c => intro _; rfl
  | quotientOrZero num den =>
      intro h
      have hn : num.eval e1 = num.eval e2 :=
        DenseExpr.eval_congr num _ _ (fun v hv => h v (List.mem_append_left _ hv))
      have hd : den.eval e1 = den.eval e2 :=
        DenseExpr.eval_congr den _ _ (fun v hv => h v (List.mem_append_right _ hv))
      show (if den.eval e1 = 0 then 0 else (den.eval e1)⁻¹ * num.eval e1)
         = (if den.eval e2 = 0 then 0 else (den.eval e2)⁻¹ * num.eval e2)
      rw [hn, hd]
  | ifEqZero cond thenM elseM iht ihe =>
      intro h
      have hc : cond.eval e1 = cond.eval e2 :=
        DenseExpr.eval_congr cond _ _ (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hv)))
      have ht := iht (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hv)))
      have he := ihe (fun v hv => h v (by
          simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hv))
      show (if cond.eval e1 = 0 then thenM.eval e1 else elseM.eval e1)
         = (if cond.eval e2 = 0 then thenM.eval e2 else elseM.eval e2)
      rw [hc, ht, he]

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`. -/
theorem denseMatchCM_eval (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) (denv : VarId → ZMod p) :
    (denseMatchCM xs imgFn thenM elseM).eval denv
    = if xs.all (fun x => decide (imgFn x = denv x)) then thenM.eval denv else elseM.eval denv := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      show (DenseComputationMethod.ifEqZero _ (denseMatchCM rest imgFn thenM elseM) elseM).eval denv = _
      rw [DenseComputationMethod.eval]
      by_cases hx : imgFn x = denv x
      · rw [if_pos (show (DenseExpr.add (.var x) (.const (-(imgFn x)))).eval denv = 0 by
              show denv x + -(imgFn x) = 0; rw [hx]; ring), ih, List.all_cons]
        simp [hx]
      · rw [if_neg (show (DenseExpr.add (.var x) (.const (-(imgFn x)))).eval denv ≠ 0 by
              show denv x + -(imgFn x) ≠ 0; intro h; exact hx (by linear_combination -h)),
            List.all_cons]
        simp [hx]

/-- Variables of `denseMatchCM` lie in `xs` together with those of the branches. -/
theorem denseMatchCM_vars (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) :
    ∀ v ∈ (denseMatchCM xs imgFn thenM elseM).vars, v ∈ xs ∨ v ∈ thenM.vars ∨ v ∈ elseM.vars := by
  induction xs with
  | nil => intro v hv; exact Or.inr (Or.inl hv)
  | cons x rest ih =>
      intro v hv
      simp only [denseMatchCM, DenseComputationMethod.vars, DenseExpr.vars, List.nil_append,
        List.append_assoc, List.mem_append, List.mem_singleton] at hv
      rcases hv with rfl | hv | hv
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih v hv with h | h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inr hv)

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
theorem denseBitCM_eval (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) (denv : VarId → ZMod p) :
    (denseBitCM patts xs hm b).eval denv
    = match patts.find? (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) with
      | some aβ => denseEnvOfFast aβ b
      | none => 0 := by
  induction patts with
  | nil => rfl
  | cons aβ rest ih =>
      show (denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b))
        (denseBitCM rest xs hm b)).eval denv = _
      rw [denseMatchCM_eval, List.find?_cons]
      by_cases hmatch : xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x)) = true
      · rw [if_pos hmatch, hmatch]; rfl
      · rw [if_neg hmatch]
        simp only [hmatch, ih]

/-- The derivation of bit `b` reads only group variables. -/
theorem denseBitCM_vars (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) :
    ∀ v ∈ (denseBitCM patts xs hm b).vars, v ∈ xs := by
  induction patts with
  | nil => intro v hv; simp [denseBitCM, DenseComputationMethod.vars] at hv
  | cons aβ rest ih =>
      intro v hv
      rcases denseMatchCM_vars xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b))
        (denseBitCM rest xs hm b) v hv with h | h | h
      · exact h
      · simp [DenseComputationMethod.vars] at h
      · exact ih v h

/-! ## Survivor enumeration -/

/-- Positional lookup at `y`'s first key position is exactly the `denseEnvOfFast` scan, on any
    assignment with the given keys. -/
theorem denseVarIx_lookup (keys : List VarId) (y : VarId) (i : Nat)
    (h : denseVarIx keys y = some i) (pt : List (VarId × ZMod p))
    (hpt : pt.map Prod.fst = keys) : denseLookupIx pt i = denseEnvOfFast pt y := by
  induction keys generalizing i pt with
  | nil => exact absurd h (by simp [denseVarIx])
  | cons x rest ih =>
    cases pt with
    | nil => exact absurd hpt (by simp)
    | cons xv pt' =>
      obtain ⟨x', v⟩ := xv
      simp only [List.map_cons, List.cons.injEq] at hpt
      obtain ⟨rfl, hpt'⟩ := hpt
      rw [denseVarIx] at h
      split_ifs at h with hfast
      · simp only [Option.some.injEq] at h
        subst h
        rw [denseLookupIx, denseEnvOfFast, if_pos hfast]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        rw [denseLookupIx, denseEnvOfFast, if_neg hfast]
        exact ih j hj pt' hpt'

/-- Compiled keyed evaluation agrees with the source's keyed-environment evaluation. -/
theorem denseCompileE_eval (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b)
    (keys : List VarId) (e : DenseExpr p) (ie : IExpr p) (h : denseCompileE keys e = some ie)
    (pt : List (VarId × ZMod p)) (hpt : pt.map Prod.fst = keys) :
    denseIExprEvalWith add mul pt ie = e.eval (denseEnvOfFast pt) := by
  induction e generalizing ie with
  | const n => simp only [denseCompileE, Option.some.injEq] at h; subst h; rfl
  | var y =>
      rw [denseCompileE, Option.map_eq_some_iff] at h
      obtain ⟨i, hi, rfl⟩ := h
      show denseIExprEvalWith add mul pt (.ix i) = denseEnvOfFast pt y
      rw [denseIExprEvalWith]
      exact denseVarIx_lookup keys y i hi pt hpt
  | add a b iha ihb =>
      rw [denseCompileE] at h
      cases ha : denseCompileE keys a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [ha, hb] at h; exact absurd h (by simp)
        | some ib =>
          rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          show add (denseIExprEvalWith add mul pt ia) (denseIExprEvalWith add mul pt ib)
            = a.eval (denseEnvOfFast pt) + b.eval (denseEnvOfFast pt)
          rw [hadd, iha ia ha, ihb ib hb]
  | mul a b iha ihb =>
      rw [denseCompileE] at h
      cases ha : denseCompileE keys a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [ha, hb] at h; exact absurd h (by simp)
        | some ib =>
          rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          show mul (denseIExprEvalWith add mul pt ia) (denseIExprEvalWith add mul pt ib)
            = a.eval (denseEnvOfFast pt) * b.eval (denseEnvOfFast pt)
          rw [hmul, iha ia ha, ihb ib hb]

/-- Compiled-list zero-check agrees with the source list's, keyed. -/
theorem denseCompileEs_all (add mul : ZMod p → ZMod p → ZMod p)
    (hadd : ∀ a b, add a b = a + b) (hmul : ∀ a b, mul a b = a * b) (keys : List VarId)
    (es : List (DenseExpr p)) (ces : List (IExpr p)) (h : denseCompileEs keys es = some ces)
    (pt : List (VarId × ZMod p)) (hpt : pt.map Prod.fst = keys) :
    ces.all (fun ie => decide (denseIExprEvalWith add mul pt ie = 0))
      = es.all (fun c => decide (c.eval (denseEnvOfFast pt) = 0)) := by
  induction es generalizing ces with
  | nil => simp only [denseCompileEs, Option.some.injEq] at h; subst h; rfl
  | cons e rest ih =>
    rw [denseCompileEs] at h
    cases he : denseCompileE keys e with
    | none => rw [he] at h; exact absurd h (by simp)
    | some ie =>
      cases hr : denseCompileEs keys rest with
      | none => rw [he, hr] at h; exact absurd h (by simp)
      | some irest =>
        rw [he, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [List.all_cons, List.all_cons, ih irest hr,
          denseCompileE_eval add mul hadd hmul keys e ie he pt hpt]

/-- `denseGroupSurvivorsE` computes the identical list to the direct `evalFast`/`denseEnvOfFast`
    filter — the index-compiled path is a pure speedup. -/
theorem denseGroupSurvivorsE_eq (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    denseGroupSurvivorsE es doms
      = (denseAssignments doms).filter
          (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0))) := by
  unfold denseGroupSurvivorsE
  split
  · rename_i ces hce
    refine List.filter_congr (fun a ha => ?_)
    have hkeys : a.map Prod.fst = doms.map Prod.fst := denseAssignments_keys doms a ha
    have hval : (fun c : DenseExpr p => decide (c.evalFast (denseEnvOfFast a) = 0))
        = (fun c : DenseExpr p => decide (c.eval (denseEnvOfFast a) = 0)) := by
      funext c; rw [DenseExpr.evalFast_eq]
    rw [hval]
    unfold denseSurvZeroCW
    exact denseCompileEs_all (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul
      (fun _ _ => rfl) (fun _ _ => rfl) (doms.map Prod.fst) es ces hce a hkeys
  · rfl

/-! ## The generic dense transport core

A witness transport principle producing `DensePassCorrect` directly from forward/backward transport
hypotheses. `out` replaces every expression by `grw`, keeps the constraints selected by `keep`, and
appends `newCs`; the fresh columns carry the derivations `dd`. Mentions neither bits nor groups. -/

theorem DenseConstraintSystem.reencode_correct_D (d out : DenseConstraintSystem p)
    (bs : BusSemantics p) (isInput : VarId → Bool)
    (grw : DenseExpr p → DenseExpr p) (keep : DenseExpr p → Bool)
    (newCs : List (DenseExpr p)) (dd : DenseDerivations p)
    (hout : out =
      { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
        busInteractions := d.busInteractions.map (fun bi =>
          { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) })
    (hfwd : ∀ denv, d.satisfies bs denv → ∃ denv',
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ newCs, c.eval denv' = 0) ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d out dd denv denv'))
    (hbwd : ∀ denv', out.satisfies bs denv' → ∃ denv,
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ d.algebraicConstraints, keep c = false → c.eval denv = 0))
    (hVars : ∀ i ∈ out.occ, isInput i = true → i ∈ d.occ) :
    DensePassCorrect isInput d out dd bs := by
  subst hout
  -- side-effect equality under bus-interaction agreement
  have hside : ∀ (denv denv' : VarId → ZMod p),
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      DenseConstraintSystem.sideEffects
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' = d.sideEffects bs denv := by
    intro denv denv' hB
    refine funext (fun message => congrArg (multiplicitySum message) ?_)
    show ((d.busInteractions.map (fun bi =>
        { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })).filter
        (fun bi => bs.isStateful bi.busId)).map _ = _
    rw [filter_map_busId_comm d.busInteractions
        (fun bi => { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })
        bs (fun _ => rfl), List.map_map]
    exact List.map_congr_left (fun bi hbi => by
      simp only [Function.comp_apply, hB bi (List.mem_of_mem_filter hbi)])
  -- admissible transfer under bus-interaction agreement
  have hdisc : ∀ (denv denv' : VarId → ZMod p),
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      (DenseConstraintSystem.admissible
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' ↔ d.admissible bs denv) := by
    intro denv denv' hB
    unfold DenseConstraintSystem.admissible
    have hmap : ((d.busInteractions.map (fun bi =>
          { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })).map
          (fun bi => denseBIEval bi denv'))
        = d.busInteractions.map (fun bi => denseBIEval bi denv) := by
      rw [List.map_map]
      exact List.map_congr_left (fun bi hbi => hB bi hbi)
    rw [hmap]
  -- recover `d.satisfies denv` from a satisfying output and the backward agreement
  have hsatd : ∀ (denv denv' : VarId → ZMod p),
      (∀ c ∈ d.algebraicConstraints, (grw c).eval denv' = c.eval denv) →
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw } denv' = denseBIEval bi denv) →
      (∀ c ∈ d.algebraicConstraints, keep c = false → c.eval denv = 0) →
      DenseConstraintSystem.satisfies
        { algebraicConstraints := ((d.algebraicConstraints.filter keep).map grw) ++ newCs,
          busInteractions := d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }) }
        bs denv' → d.satisfies bs denv := by
    intro denv denv' hA hB hdrop hsat'
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · by_cases hk : keep c = true
      · have hmem : grw c ∈ ((d.algebraicConstraints.filter keep).map grw) ++ newCs :=
          List.mem_append_left _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hk⟩, rfl⟩)
        have h1 := hsat'.1 _ hmem
        rw [hA c hc] at h1; exact h1
      · exact hdrop c hc (by simpa using hk)
    · show (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)
      have hmem : { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw }
          ∈ (d.busInteractions.map (fun bi =>
            { bi with multiplicity := grw bi.multiplicity, payload := bi.payload.map grw })) :=
        List.mem_map.2 ⟨bi, hbi, rfl⟩
      have h2 := hsat'.2 _ hmem
      rw [hB bi hbi] at h2
      exact h2
  refine ⟨?_, ?_, hVars, ?_⟩
  · -- Soundness: `out.implies d`.
    intro denv' hsat'
    obtain ⟨denv, hA, hB, hdrop⟩ := hbwd denv' hsat'
    refine ⟨denv, hsatd denv denv' hA hB hdrop hsat', ?_⟩
    rw [hside denv denv' hB]
  · -- Invariant preservation.
    intro hinv denv' hsat' bi' hbi'
    obtain ⟨denv, hA, hB, hdrop⟩ := hbwd denv' hsat'
    have hd := hsatd denv denv' hA hB hdrop hsat'
    obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
    show (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv').multiplicity ≠ 0 →
      bs.maintainsInvariants (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv')
    rw [hB bi0 hbi0]
    exact hinv denv hd bi0 hbi0
  · -- Completeness with derivations.
    intro denv hadm hsat
    obtain ⟨denv', hA, hB, hnew, hframe, hrec⟩ := hfwd denv hsat
    refine ⟨denv', ⟨fun c hc => ?_, fun bi hbi => ?_⟩, (hdisc denv denv' hB).2 hadm, ?_, hframe, hrec⟩
    · rcases List.mem_append.1 hc with h | h
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 h
        rw [hA c0 (List.mem_of_mem_filter hc0)]
        exact hsat.1 c0 (List.mem_of_mem_filter hc0)
      · exact hnew c h
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
      show (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv').multiplicity ≠ 0 →
        bs.accepts (denseBIEval { bi0 with multiplicity := grw bi0.multiplicity, payload := bi0.payload.map grw } denv')
      rw [hB bi0 hbi0]
      exact hsat.2 bi0 hbi0
    · rw [hside denv denv' hB]

/-- The method list built for the fresh bits supplies `g w` for a bit `w`, nothing otherwise. -/
theorem DenseDerivations.methodFor_map (bits : List VarId) (g : VarId → DenseComputationMethod p)
    (w : VarId) :
    DenseDerivations.methodFor (bits.map (fun b => (b, g b))) w
      = if w ∈ bits then some (g w) else none := by
  induction bits with
  | nil => simp [DenseDerivations.methodFor]
  | cons b rest ih =>
      simp only [List.map_cons, DenseDerivations.methodFor, ih, List.mem_cons]
      by_cases hw : w ∈ rest
      · simp [hw]
      · by_cases hbw : b = w
        · subst hbw; simp [hw]
        · have hwb : w ≠ b := fun h => hbw h.symm
          simp [hw, hbw, hwb, Option.orElse]

/-! ## The capstone: certificate soundness

Supplies the forward transport (with the input-column frame and the `DenseOutReconstructs`
obligation for the minted bits) and the backward transport to
`DenseConstraintSystem.reencode_correct_D`. The freshness / `isInput` facts about the minted bits
and the group columns enter as abstract hypotheses, discharged in the step/loop section below. -/

theorem denseCheckReencode_sound [Fact p.Prime] (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (isInput : VarId → Bool) (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (hxsInput : ∀ x ∈ xs, isInput x = true) (hxsOcc : ∀ x ∈ xs, x ∈ d.occ)
    (hxsB : ∀ x ∈ xs, x ∉ bits) (hbnInput : ∀ b ∈ bits, isInput b = false)
    (hchk : denseCheckReencode d xs bits hm = true) :
    DensePassCorrect isInput d (denseReencodeOut d xs bits hm)
      (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b))) bs := by
  unfold denseCheckReencode at hchk
  split at hchk
  · exact absurd hchk (by simp)
  rename_i doms hdoms
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨_hbox, _hm2⟩, _hprofit⟩, hnodup⟩, hvarsB⟩, hC5⟩, hC6⟩, hfreshB⟩ := hchk
  have hnodup' : bits.Nodup := of_decide_eq_true hnodup
  have hkeys : doms.map Prod.fst = xs := denseGroupDoms_fst (denseCoveredCsOf d xs) xs doms hdoms
  have hbitKeys : (denseBitBox (p := p) bits).map Prod.fst = bits := by
    unfold denseBitBox; rw [List.map_map]; simp [Function.comp_def]
  have hpolyVars : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars,
      v ∈ bits := by
    intro y hy v hv
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp (List.all_eq_true.mp hvarsB y hy) v hv)
  have hσnone : ∀ y, y ∉ xs → denseGroupSubst xs hm y = none := by
    intro y hy
    show (if denseContainsFast xs y = true then hm[y]? else none) = none
    rw [if_neg (fun h => hy (denseContainsFast_sound xs y h))]
  have hfreshCm : ∀ c ∈ d.algebraicConstraints, ∀ b ∈ bits, c.mentions b = false := by
    intro c hc b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    simpa using List.all_eq_true.mp h1.1 c hc
  have hfreshMm : ∀ bi ∈ d.busInteractions, ∀ b ∈ bits, bi.multiplicity.mentions b = false := by
    intro bi hbi b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using h2.1
  have hfreshPm : ∀ bi ∈ d.busInteractions, ∀ e ∈ bi.payload, ∀ b ∈ bits,
      e.mentions b = false := by
    intro bi hbi e he b hb
    have h1 := List.all_eq_true.mp hfreshB b hb
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 bi hbi
    rw [Bool.and_eq_true] at h2
    simpa using List.all_eq_true.mp h2.2 e he
  -- FORWARD (with the input frame and the `DenseOutReconstructs` obligation)
  have hfwd_D : ∀ denv, d.satisfies bs denv → ∃ denv',
      (∀ c ∈ d.algebraicConstraints,
        ((denseGroupRewrite xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with
            multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits)) bi.multiplicity,
            payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits))) } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ bits.map denseBoolConstraint, c.eval denv' = 0) ∧
      (∀ i, isInput i = true → denv' i = denv i) ∧
      (∀ inputVarIds, (∀ i ∈ d.occ, isInput i = true → i ∈ inputVarIds) →
        DenseOutReconstructs isInput inputVarIds d (denseReencodeOut d xs bits hm)
          (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)))
          denv denv') := by
    intro denv hsat
    have hallES : ∀ c ∈ denseCoveredCsOf d xs, c.eval denv = 0 := fun c hc =>
      hsat.1 c (List.mem_of_mem_filter hc)
    have hdsound := denseGroupDoms_sound denv (denseCoveredCsOf d xs) hallES xs doms hdoms
    have hamem : (doms.map (fun yd => (yd.1, denv yd.1))) ∈ denseAssignments doms :=
      mem_denseAssignments doms denv hdsound
    have hasurv : (doms.map (fun yd => (yd.1, denv yd.1)))
        ∈ denseGroupSurvivorsE (denseCoveredCsOf d xs) doms := by
      rw [denseGroupSurvivorsE_eq]
      refine List.mem_filter.2 ⟨hamem, ?_⟩
      rw [List.all_eq_true]
      intro c hc
      rw [decide_eq_true_iff, DenseExpr.evalFast_eq]
      have hcov := List.of_mem_filter hc
      rw [denseCoveredBy, Bool.and_eq_true] at hcov
      have hcvars : ∀ v ∈ c.vars, v ∈ doms.map Prod.fst := by
        rw [hkeys]; exact denseVarsInF_sound xs c hcov.2
      have heq : c.eval (denseEnvOfFast (doms.map (fun yd => (yd.1, denv yd.1)))) = c.eval denv :=
        DenseExpr.eval_congr c _ _ (fun v hv => denseEnvOfFast_map doms denv v (hcvars v hv))
      rw [heq]; exact hallES c hc
    have hC5' : (denseAssignments (denseBitBox bits)).any
        (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) = true := by
      rw [List.any_eq_true]
      obtain ⟨aβ, ha, hp⟩ := List.any_eq_true.1 (List.all_eq_true.mp hC5 _ hasurv)
      refine ⟨aβ, ha, ?_⟩
      rw [List.all_eq_true] at hp ⊢
      intro x hx
      have hsx : denseEnvOfFast (doms.map (fun yd => (yd.1, denv yd.1))) x = denv x :=
        denseEnvOfFast_map doms denv x (by rw [hkeys]; exact hx)
      have hpp := hp x hx
      rw [hsx] at hpp
      exact hpp
    cases hfindEnv : (denseAssignments (denseBitBox bits)).find?
        (fun aβ => xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x))) with
    | none =>
        exfalso
        rw [List.find?_eq_none] at hfindEnv
        obtain ⟨aβ0, ha0, hp0⟩ := List.any_eq_true.1 hC5'
        exact absurd hp0 (by simpa using hfindEnv aβ0 ha0)
    | some aβ =>
      have haβ : aβ ∈ denseAssignments (denseBitBox bits) := List.mem_of_find?_eq_some hfindEnv
      have hβpred : xs.all (fun x => decide (denseImgVal xs hm aβ x = denv x)) = true := by
        simpa using List.find?_some hfindEnv
      have hkeysβ : aβ.map Prod.fst = bits := by
        rw [denseAssignments_keys (denseBitBox bits) aβ haβ, hbitKeys]
      have henvxs : ∀ x ∈ xs, denseEnvExt aβ denv x = denv x := fun x hx =>
        denseEnvExt_eq_env_of_notmem aβ denv x (by rw [hkeysβ]; exact hxsB x hx)
      have hpoint : ∀ y, y ∉ bits →
          denseEnvF (denseGroupSubst xs hm) (denseEnvExt aβ denv) y = denv y := by
        intro y hyb
        by_cases hyx : y ∈ xs
        · rw [denseEnvF_eq_varSubst]
          have hagree : ((DenseExpr.var y).substF (denseGroupSubst xs hm)).eval (denseEnvExt aβ denv)
              = ((DenseExpr.var y).substF (denseGroupSubst xs hm)).eval (denseEnvOfFast aβ) := by
            apply DenseExpr.eval_congr
            intro v hv
            exact denseEnvExt_eq_envOfFast_of_mem aβ denv v (by rw [hkeysβ]; exact hpolyVars y hyx v hv)
          rw [hagree, ← DenseExpr.evalFast_eq]
          exact of_decide_eq_true (List.all_eq_true.mp hβpred y hyx)
        · unfold denseEnvF
          rw [hσnone y hyx]
          exact denseEnvExt_eq_env_of_notmem aβ denv y (by rw [hkeysβ]; exact hyb)
      have hbitsagree : ∀ b ∈ bits, denseEnvExt aβ denv b = denseEnvOfFast aβ b := fun b hb =>
        denseEnvExt_eq_envOfFast_of_mem aβ denv b (by rw [hkeysβ]; exact hb)
      refine ⟨denseEnvExt aβ denv, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        exact denseGroupRewrite_agree xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) hσnone (denseEnvExt aβ denv) denv aβ haβ
          hbitsagree hpolyVars hpoint c (hfreshCm c hc)
      · intro bi hbi
        exact denseGroupRewrite_bi_agree xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits)) hσnone (denseEnvExt aβ denv) denv aβ haβ
          hbitsagree hpolyVars hpoint bi (hfreshMm bi hbi) (hfreshPm bi hbi)
      · intro c hc
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
        apply denseBoolConstraint_eval_of_bool
        have hbk : b ∈ aβ.map Prod.fst := hkeysβ ▸ hb
        rw [denseEnvExt_eq_envOfFast_of_mem aβ denv b hbk]
        have hmem := denseEnvOf_mem_of_assignments (denseBitBox bits)
          (by rw [hbitKeys]; exact hnodup') aβ haβ
          (b, ([0, 1] : List (ZMod p))) (List.mem_map.2 ⟨b, hb, rfl⟩)
        simpa using hmem
      · intro i hii
        refine denseEnvExt_eq_env_of_notmem aβ denv i ?_
        rw [hkeysβ]
        intro hib
        rw [hbnInput i hib] at hii
        simp at hii
      · intro inputVarIds hcov1 i hiout hisF
        rw [DenseDerivations.methodFor_map bits
          (fun b => denseBitCM (denseAssignments (denseBitBox bits)) xs hm b) i]
        by_cases hib : i ∈ bits
        · rw [if_pos hib]
          refine ⟨fun j hj => hxsInput j (denseBitCM_vars _ xs hm i j hj), fun j hj => ?_, ?_⟩
          · exact hcov1 j (hxsOcc j (denseBitCM_vars _ xs hm i j hj))
              (hxsInput j (denseBitCM_vars _ xs hm i j hj))
          · have hval : (denseBitCM (denseAssignments (denseBitBox bits)) xs hm i).eval
                (denseEnvExt aβ denv) = denseEnvOfFast aβ i := by
              rw [DenseComputationMethod.eval_congr
                  (denseBitCM (denseAssignments (denseBitBox bits)) xs hm i)
                  (denseEnvExt aβ denv) denv
                  (fun v hv => henvxs v (denseBitCM_vars _ xs hm i v hv)),
                denseBitCM_eval, hfindEnv]
            rw [hval]
            exact (hbitsagree i hib).symm
        · rw [if_neg hib]
          refine ⟨?_, denseEnvExt_eq_env_of_notmem aβ denv i (by rw [hkeysβ]; exact hib)⟩
          rcases denseReencodeOut_vars_subset d xs bits hm hpolyVars i hiout with h | h
          · exact h
          · exact absurd h hib
  -- BACKWARD
  have hbwd : ∀ denv', (denseReencodeOut d xs bits hm).satisfies bs denv' → ∃ denv,
      (∀ c ∈ d.algebraicConstraints,
        ((denseGroupRewrite xs bits (denseGroupSubst xs hm)
          (denseAssignments (denseBitBox bits))) c).eval denv' = c.eval denv) ∧
      (∀ bi ∈ d.busInteractions,
        denseBIEval { bi with
            multiplicity := denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits)) bi.multiplicity,
            payload := bi.payload.map (denseGroupRewrite xs bits (denseGroupSubst xs hm)
              (denseAssignments (denseBitBox bits))) } denv' = denseBIEval bi denv) ∧
      (∀ c ∈ d.algebraicConstraints, (fun c => !denseCoveredBy xs c) c = false → c.eval denv = 0) := by
    intro denv' hsat'
    have hbool : ∀ b ∈ bits, denv' b = 0 ∨ denv' b = 1 := by
      intro b hb
      apply dense_bool_of_boolConstraint_eval
      exact hsat'.1 _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩))
    have haβmem : ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1)))
        ∈ denseAssignments (denseBitBox bits) := by
      apply mem_denseAssignments
      intro yd hyd
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hyd
      simpa using hbool b hb
    have hβenv : ∀ b ∈ bits,
        denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) b = denv' b := by
      intro b hb
      exact denseEnvOfFast_map (denseBitBox bits) denv' b (by rw [hbitKeys]; exact hb)
    have hkeysP : (xs.map (fun x =>
        (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))).map Prod.fst = xs := by
      rw [List.map_map]; simp [Function.comp_def]
    have hpoint : ∀ y, denseEnvF (denseGroupSubst xs hm) denv' y
        = denseEnvExt (xs.map (fun x =>
            (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv' y := by
      intro y
      by_cases hyx : y ∈ xs
      · rw [denseEnvF_eq_varSubst,
          denseEnvExt_eq_envOfFast_of_mem _ denv' y (by rw [hkeysP]; exact hyx),
          denseEnvOf_zipimg xs _ y hyx]
      · unfold denseEnvF
        rw [hσnone y hyx]
        exact (denseEnvExt_eq_env_of_notmem _ denv' y (by rw [hkeysP]; exact hyx)).symm
    have hexpr : ∀ e : DenseExpr p, (e.substF (denseGroupSubst xs hm)).eval denv'
        = e.eval (denseEnvExt (xs.map (fun x =>
            (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv') :=
      fun e => denseSubstF_eval_agree (denseGroupSubst xs hm) denv' _ e (fun y _ => hpoint y)
    have hbitsagree' : ∀ b ∈ bits,
        denv' b = denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) b :=
      fun b hb => (hβenv b hb).symm
    refine ⟨denseEnvExt (xs.map (fun x =>
        (x, ((DenseExpr.var x).substF (denseGroupSubst xs hm)).eval denv'))) denv', ?_, ?_, ?_⟩
    · intro c hc
      exact denseGroupRewrite_agree xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) hσnone denv' _
        ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) haβmem hbitsagree' hpolyVars
        (fun y _ => hpoint y) c (hfreshCm c hc)
    · intro bi hbi
      exact denseGroupRewrite_bi_agree xs bits (denseGroupSubst xs hm)
        (denseAssignments (denseBitBox bits)) hσnone denv' _
        ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))) haβmem hbitsagree' hpolyVars
        (fun y _ => hpoint y) bi (hfreshMm bi hbi) (hfreshPm bi hbi)
    · intro c hc hkc
      have hcov : denseCoveredBy xs c = true := by simpa using hkc
      have hcmem : c ∈ denseCoveredCsOf d xs := List.mem_filter.2 ⟨hc, hcov⟩
      have h6 := List.all_eq_true.mp (List.all_eq_true.mp hC6 _ haβmem) c hcmem
      rw [decide_eq_true_iff, DenseExpr.evalFast_eq] at h6
      have hcvars : ∀ v ∈ c.vars, v ∈ xs := by
        rw [denseCoveredBy, Bool.and_eq_true] at hcov
        exact denseVarsInF_sound xs c hcov.2
      have hagree : (c.substF (denseGroupSubst xs hm)).eval
            (denseEnvOfFast ((denseBitBox (p := p) bits).map (fun yd => (yd.1, denv' yd.1))))
          = (c.substF (denseGroupSubst xs hm)).eval denv' := by
        rw [DenseExpr.eval_substF, DenseExpr.eval_substF]
        apply DenseExpr.eval_congr
        intro y hy
        rw [denseEnvF_eq_varSubst, denseEnvF_eq_varSubst]
        apply DenseExpr.eval_congr
        intro v hv
        exact hβenv v (hpolyVars y (hcvars y hy) v hv)
      rw [← hexpr c, ← hagree]
      exact h6
  -- no new powdr-ID column: every output variable is a `d`-column or a (non-input) bit
  have hVars : ∀ i ∈ (denseReencodeOut d xs bits hm).occ, isInput i = true → i ∈ d.occ := by
    intro i hi hii
    rcases denseReencodeOut_vars_subset d xs bits hm hpolyVars i hi with h | h
    · exact h
    · rw [hbnInput i h] at hii; simp at hii
  exact DenseConstraintSystem.reencode_correct_D d (denseReencodeOut d xs bits hm) bs isInput
    (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits)))
    (fun c => !denseCoveredBy xs c)
    (bits.map denseBoolConstraint)
    (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)))
    rfl hfwd_D hbwd hVars


/-! ## Step / loop correctness, pass assembly

Each step is `DensePassCorrect` at its own output registry (reject branches by
`DensePassCorrect.refl`, the accept branch by the capstone `denseCheckReencode_sound`); the loop
composes them via `DensePassCorrect.andThen`, threading pointwise `isInput`-preservation to a
uniform final registry. `denseReencodePass` packages `denseReencodeF` through `ofExtending`. -/

theorem register_isInput_eq (reg : VarRegistry) (v : Variable) (hv : v.powdrId? = none)
    (i : VarId) : (reg.register v).1.isInput i = reg.isInput i := by
  by_cases hvalid : reg.Valid i
  · rw [VarRegistry.isInput, VarRegistry.isInput,
        (VarRegistry.register_extends reg v).resolve_eq hvalid]
  · have hge : reg.byId.size ≤ i.index := Nat.not_lt.mp hvalid
    have hreg : reg.isInput i = false := by
      show ((reg.byId[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_eq_none hge]; rfl
    rw [hreg]
    show (((reg.register v).1.byId[i.index]?).getD default).powdrId?.isSome = false
    unfold VarRegistry.register
    split
    · show ((reg.byId[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_eq_none hge]; rfl
    · show (((reg.byId.push v)[i.index]?).getD default).powdrId?.isSome = false
      rw [Array.getElem?_push]
      split
      · rw [Option.getD_some]; show (v.powdrId?).isSome = false; rw [hv]; rfl
      · rw [Array.getElem?_eq_none hge]; rfl

private def rbStep (fb : String) (acc : VarRegistry × List VarId) (j : Nat) :
    VarRegistry × List VarId :=
  let (r, bs) := acc
  let (r', i) := r.register ({ name := fb ++ "_" ++ toString j } : Variable)
  (r', bs ++ [i])

private theorem rbStep_eq (fb : String) (racc : VarRegistry) (bacc : List VarId) (j : Nat) :
    rbStep fb (racc, bacc) j
      = ((racc.register ({ name := fb ++ "_" ++ toString j } : Variable)).1,
         bacc ++ [(racc.register ({ name := fb ++ "_" ++ toString j } : Variable)).2]) := rfl

theorem registerBits_fold_inv (fb : String) (r0 : VarRegistry) :
    ∀ (l : List Nat) (racc : VarRegistry) (bacc : List VarId),
      r0.Extends racc → (∀ i, racc.isInput i = r0.isInput i) → (∀ b ∈ bacc, racc.Valid b) →
      r0.Extends (l.foldl (rbStep fb) (racc, bacc)).1
      ∧ (∀ i, (l.foldl (rbStep fb) (racc, bacc)).1.isInput i = r0.isInput i)
      ∧ (∀ b ∈ (l.foldl (rbStep fb) (racc, bacc)).2, (l.foldl (rbStep fb) (racc, bacc)).1.Valid b) := by
  intro l
  induction l with
  | nil => intro racc bacc hext hii hval; exact ⟨hext, hii, hval⟩
  | cons j rest ih =>
      intro racc bacc hext hii hval
      rw [List.foldl_cons, rbStep_eq]
      apply ih
      · exact hext.trans (VarRegistry.register_extends racc _)
      · intro i; rw [register_isInput_eq racc _ rfl i]; exact hii i
      · intro b hb
        rw [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact (VarRegistry.register_extends racc _).valid (hval b hb)
        · exact VarRegistry.register_valid racc _

theorem denseRegisterBits_props (reg : VarRegistry) (fb : String) (k : Nat) :
    reg.Extends (denseRegisterBits reg fb k).1
    ∧ (∀ i, (denseRegisterBits reg fb k).1.isInput i = reg.isInput i)
    ∧ (∀ b ∈ (denseRegisterBits reg fb k).2, (denseRegisterBits reg fb k).1.Valid b) :=
  registerBits_fold_inv fb reg (List.range k) reg [] (VarRegistry.Extends.refl reg)
    (fun _ => rfl) (by intro b hb; simp at hb)





theorem coveredBy_of_occ {r : VarRegistry} {d : DenseConstraintSystem p}
    (h : ∀ i ∈ d.occ, r.Valid i) : d.CoveredBy r := by
  grind [DenseConstraintSystem.CoveredBy, DenseExpr.CoveredBy, denseBICovered, denseBIVars,
    DenseConstraintSystem.mem_occ_of_constraint, DenseConstraintSystem.mem_occ_of_bi]

theorem csCoveredBy_mono {r r' : VarRegistry} (h : r.Extends r') {d : DenseConstraintSystem p}
    (hc : d.CoveredBy r) : d.CoveredBy r' :=
  ⟨fun e he => (hc.1 e he).mono h,
   fun bi hbi => ⟨(hc.2 bi hbi).1.mono h, fun e he => ((hc.2 bi hbi).2 e he).mono h⟩⟩

theorem denseCM_coveredBy_of_vars {r : VarRegistry} (cm : DenseComputationMethod p)
    (h : ∀ i ∈ cm.vars, r.Valid i) : cm.CoveredBy r := by
  induction cm with
  | const c => exact True.intro
  | quotientOrZero num den =>
      exact ⟨fun i hi => h i (List.mem_append_left _ hi),
             fun i hi => h i (List.mem_append_right _ hi)⟩
  | ifEqZero cond thenM elseM iht ihe =>
      refine ⟨fun i hi => h i ?_, iht (fun i hi => h i ?_), ihe (fun i hi => h i ?_)⟩
      · simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inl hi)
      · simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inl (Or.inr hi)
      · simp only [DenseComputationMethod.vars, List.mem_append]; exact Or.inr hi

theorem denseReencodeOut_covered (reg1 : VarRegistry) (d : DenseConstraintSystem p)
    (xs bits : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) (hcov1 : d.CoveredBy reg1)
    (hbits : ∀ b ∈ bits, reg1.Valid b)
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits) :
    (denseReencodeOut d xs bits hm).CoveredBy reg1 := by
  apply coveredBy_of_occ
  intro i hi
  rcases denseReencodeOut_vars_subset d xs bits hm hσ i hi with h | h
  · exact DenseConstraintSystem.occ_valid hcov1 i h
  · exact hbits i h

theorem denseBitCM_covered (reg1 : VarRegistry) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (hxsValid : ∀ x ∈ xs, reg1.Valid x)
    (hbits : ∀ b ∈ bits, reg1.Valid b) :
    DenseDerivations.CoveredBy reg1
      (bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b))) := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  exact ⟨hbits b hb, denseCM_coveredBy_of_vars _
    (fun i hi => hxsValid i (denseBitCM_vars _ xs hm b i hi))⟩


/-! ## Group variables occur in `d`, straight from the certificate

The cached step's `varSet` gate no longer witnesses `xs ⊆ d.occ` (the set is over-approximating),
so the accept case derives it from the certificate itself: `denseCheckReencode`'s domain lookup
returns, for every group variable, a covered constraint of `d` mentioning it. -/

private theorem DenseExpr.mentions_mem_vars {i : VarId} :
    ∀ {e : DenseExpr p}, e.mentions i = true → i ∈ e.vars := by
  intro e
  induction e with
  | const n => intro h; simp [DenseExpr.mentions] at h
  | var j =>
      intro h
      simp only [DenseExpr.mentions, beq_iff_eq] at h
      simp [DenseExpr.vars, h]
  | add a b iha ihb =>
      intro h
      rcases Bool.or_eq_true .. |>.mp h with h | h
      · exact List.mem_append_left _ (iha h)
      · exact List.mem_append_right _ (ihb h)
  | mul a b iha ihb =>
      intro h
      rcases Bool.or_eq_true .. |>.mp h with h | h
      · exact List.mem_append_left _ (iha h)
      · exact List.mem_append_right _ (ihb h)

private theorem denseFindDomainAlg_mentions {i : VarId} :
    ∀ {all : List (DenseExpr p)} {dm : List (ZMod p)},
      denseFindDomainAlg all i = some dm → ∃ c ∈ all, c.mentions i = true
  | [], dm, h => by simp [denseFindDomainAlg] at h
  | c :: rest, dm, h => by
      rw [denseFindDomainAlg] at h
      by_cases hm : c.mentions i = true
      · exact ⟨c, List.mem_cons_self .., hm⟩
      · rw [if_neg (by simpa using hm)] at h
        obtain ⟨c', hc', hm'⟩ := denseFindDomainAlg_mentions h
        exact ⟨c', List.mem_cons_of_mem _ hc', hm'⟩

private theorem denseGroupDoms_mentions {es : List (DenseExpr p)} :
    ∀ {xs : List VarId} {doms : List (VarId × List (ZMod p))},
      denseGroupDoms es xs = some doms → ∀ x ∈ xs, ∃ c ∈ es, c.mentions x = true
  | [], _, _, x, hx => absurd hx (by simp)
  | i :: rest, doms, h, x, hx => by
      rw [denseGroupDoms] at h
      cases hd : denseFindDomainAlg es i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some dm =>
          cases hr : denseGroupDoms es rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds =>
              rcases List.mem_cons.1 hx with rfl | hmem
              · exact denseFindDomainAlg_mentions hd
              · exact denseGroupDoms_mentions hr x hmem

theorem denseCheckReencode_xsOcc (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (hchk : denseCheckReencode d xs bits hm = true) :
    ∀ x ∈ xs, x ∈ d.occ := by
  intro x hx
  unfold denseCheckReencode at hchk
  cases hdoms : denseGroupDoms (denseCoveredCsOf d xs) xs with
  | none => rw [hdoms] at hchk; exact absurd hchk (by simp)
  | some doms =>
      obtain ⟨c, hc, hmn⟩ := denseGroupDoms_mentions hdoms x hx
      exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc)
        (DenseExpr.mentions_mem_vars hmn)

theorem denseCheckReencode_polyVars (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (hchk : denseCheckReencode d xs bits hm = true) :
    ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs hm)).vars, v ∈ bits := by
  grind [denseCheckReencode, List.contains_iff_mem]




set_option maxHeartbeats 1000000 in
theorem denseFilterConstraints_coveredBy {d : DenseConstraintSystem p} {reg : VarRegistry}
    {keep : DenseExpr p → Bool} (h : d.CoveredBy reg) :
    (d.filterConstraints keep).CoveredBy reg :=
  ⟨fun e he => h.1 e (List.mem_of_mem_filter he), h.2⟩

/-! ### The variable-superset invariant

`denseWorkStep` decides bit freshness from `state.varSet` rather than scanning the system. What
licenses that is `DenseWorkVarsOk`: every variable occurring in the working system is in `varSet`.
The seed satisfies it by construction (`varSet = ofList d.occ`), and an accept preserves it because
the rewritten system's variables are old variables or fresh bits
(`denseReencodeOut_vars_subset`), and the fresh bits are exactly what the state update inserts. -/

/-- Filtering constraints cannot introduce a variable. -/
theorem denseFilterConstraints_occ_sub (d : DenseConstraintSystem p)
    (keep : DenseExpr p → Bool) :
    ∀ v ∈ (d.filterConstraints keep).occ, v ∈ d.occ := by
  intro v hv
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.filterConstraints,
    List.mem_append, List.mem_flatMap] at hv
  rcases hv with ⟨c, hc, hcv⟩ | ⟨bi, hbi, hbiv⟩
  · exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_mem_filter hc) hcv
  · exact DenseConstraintSystem.mem_occ_of_bi hbi hbiv

/-- Freshness holds for any bit the system does not mention. -/
theorem denseFreshScan_of_notMemOcc (d : DenseConstraintSystem p) (bits : List VarId)
    (h : ∀ b ∈ bits, b ∉ d.occ) : denseFreshScan d bits = true := by
  have hb : ∀ (e : DenseExpr p), (∀ b ∈ bits, b ∉ e.vars) →
      e.mentionsAny (Std.HashSet.ofList bits) = false := by
    intro e he
    exact (DenseExpr.mentionsAny_ofList_false_iff bits e).2 (fun b hbm =>
      by
        cases hm : e.mentions b with
        | false => rfl
        | true => exact absurd (DenseExpr.mentions_mem_vars hm) (he b hbm))
  simp only [denseFreshScan, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨fun c hc => hb c (fun b hbm hv => h b hbm ?_), fun bi hbi => ⟨hb _ (fun b hbm hv =>
    h b hbm ?_), fun e he => hb e (fun b hbm hv => h b hbm ?_)⟩⟩
  · exact DenseConstraintSystem.mem_occ_of_constraint hc hv
  · exact DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append]; exact Or.inl hv)
  · exact DenseConstraintSystem.mem_occ_of_bi hbi (by
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨e, he, hv⟩)

/-! ### The bus-side index invariant

`denseWorkOut` rewrites the bus list only at the positions it is handed, so it needs those positions
to cover everywhere `denseBIRewriteGate` could fire. `DenseBusIdxOk` is what supplies that: the
`useBis` buckets list every position by each of its variables, and `foldBis` lists every position
carrying a variable-free composite node. Both hold at the seed by construction and are maintained by
the state update, which folds over the very list the splice consumed. -/

set_option maxHeartbeats 1000000 in




set_option maxHeartbeats 1000000 in


set_option maxHeartbeats 1000000 in

/-! ## The array engine

The engine of `Reencode.lean` keeps the system on stable array positions with `VarId`-keyed indexes.
Everything it computes off those indexes is *untrusted*: the certificate below is the audited
`denseCheckReencode` on the covered set the index gathered, and the accept's edits are re-derived
from each position's current content, so an index that over-reports costs a decision and never
soundness. Two facts carry the correctness: the gathered covered set *is* the filter
(`denseRncEs_eq`, from anchor completeness), and the written state's view *is*
`denseReencodeOut` of the old view with trivially-true constraints dropped (`denseRncWrite_view`) —
the same two facts the list engine established with `denseWorkView_check` and `denseWorkOut_view`. -/

/-! ### Expression predicate characterisations -/

theorem denseHasVar_iff (e : DenseExpr p) : e.hasVar = true ↔ e.vars ≠ [] := by
  induction e with
  | const n => simp [DenseExpr.hasVar, DenseExpr.vars]
  | var y => simp [DenseExpr.hasVar, DenseExpr.vars]
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.hasVar, DenseExpr.vars, Bool.or_eq_true, iha, ihb,
        ne_eq, List.append_eq_nil_iff, not_and_or]

theorem denseVarsInF_iff (xs : List VarId) (e : DenseExpr p) :
    e.varsInF xs = true ↔ ∀ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const n => simp [DenseExpr.varsInF, DenseExpr.vars]
  | var y =>
      simp only [DenseExpr.varsInF, DenseExpr.vars, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h v hv; rw [hv]; exact denseContainsFast_sound xs y h
      · intro h; exact denseContainsFast_of_mem xs y (h y rfl)
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.varsInF, DenseExpr.vars, Bool.and_eq_true, iha, ihb, List.mem_append]
      exact ⟨fun ⟨ha, hb⟩ v hv => hv.elim (ha v) (hb v),
        fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩⟩

theorem denseSharesVarIn_iff (xs : List VarId) (e : DenseExpr p) :
    e.sharesVarIn xs = true ↔ ∃ v ∈ e.vars, v ∈ xs := by
  induction e with
  | const n => simp [DenseExpr.sharesVarIn, DenseExpr.vars]
  | var y =>
      simp only [DenseExpr.sharesVarIn, DenseExpr.vars, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h; exact ⟨y, rfl, denseContainsFast_sound xs y h⟩
      · rintro ⟨v, hv, hx⟩; rw [hv] at hx; exact denseContainsFast_of_mem xs y hx
  | add a b iha ihb | mul a b iha ihb =>
      simp only [DenseExpr.sharesVarIn, DenseExpr.vars, Bool.or_eq_true, iha, ihb, List.mem_append]
      constructor
      · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
        · exact ⟨v, Or.inl hv, hx⟩
        · exact ⟨v, Or.inr hv, hx⟩
      · rintro ⟨v, hv | hv, hx⟩
        · exact Or.inl ⟨v, hv, hx⟩
        · exact Or.inr ⟨v, hv, hx⟩

/-! ### The capped variable arrays

`denseRncCapVars` stops at nine distinct variables, so it is exact below the cap; every consumer
either stays below it or falls back to the tree walk. -/

theorem denseRncCapGo_mono (cap : Nat) :
    ∀ (e : DenseExpr p) (acc : Array VarId),
      (∀ v ∈ acc, v ∈ denseRncCapGo cap e acc) ∧ acc.size ≤ (denseRncCapGo cap e acc).size := by
  intro e
  induction e with
  | const n => intro acc; exact ⟨fun v hv => hv, Nat.le_refl _⟩
  | var y =>
      intro acc
      rw [denseRncCapGo]
      split
      · exact ⟨fun v hv => hv, Nat.le_refl _⟩
      · exact ⟨fun v hv => by simp [hv], by simp⟩
  | add a b iha ihb | mul a b iha ihb =>
      intro acc
      rw [denseRncCapGo]
      obtain ⟨hma, hsa⟩ := iha acc
      split
      · exact ⟨hma, hsa⟩
      · obtain ⟨hmb, hsb⟩ := ihb (denseRncCapGo cap a acc)
        exact ⟨fun v hv => hmb v (hma v hv), Nat.le_trans hsa hsb⟩

theorem denseRncCapGo_sound (cap : Nat) :
    ∀ (e : DenseExpr p) (acc : Array VarId) (v : VarId),
      v ∈ denseRncCapGo cap e acc → v ∈ acc ∨ v ∈ e.vars := by
  intro e
  induction e with
  | const n => intro acc v hv; exact Or.inl hv
  | var y =>
      intro acc v hv
      rw [denseRncCapGo] at hv
      split at hv
      · exact Or.inl hv
      · rcases Array.mem_push.1 hv with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [DenseExpr.vars, h])
  | add a b iha ihb | mul a b iha ihb =>
      intro acc v hv
      rw [denseRncCapGo] at hv
      split at hv
      · rcases iha acc v hv with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [DenseExpr.vars, h])
      · rcases ihb _ v hv with h | h
        · rcases iha acc v h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (by simp [DenseExpr.vars, h'])
        · exact Or.inr (by simp [DenseExpr.vars, h])

/-- Below the cap the walk never bailed out, so every variable of the expression is present. -/
theorem denseRncCapGo_complete (cap : Nat) :
    ∀ (e : DenseExpr p) (acc : Array VarId),
      (denseRncCapGo cap e acc).size < cap → ∀ v ∈ e.vars, v ∈ denseRncCapGo cap e acc := by
  intro e
  induction e with
  | const n => intro acc _ v hv; simp [DenseExpr.vars] at hv
  | var y =>
      intro acc hlt v hv
      have hy : v = y := by simpa [DenseExpr.vars] using hv
      subst hy
      rw [denseRncCapGo] at hlt ⊢
      split at hlt
      · next hc =>
          rw [if_pos hc]
          have hc' : cap ≤ acc.size ∨ acc.contains v = true := by simpa using hc
          rcases hc' with h | h
          · omega
          · exact Array.mem_of_contains_eq_true h
      · next hc =>
          rw [if_neg hc]
          simp
  | add a b iha ihb | mul a b iha ihb =>
      intro acc hlt v hv
      rw [denseRncCapGo] at hlt ⊢
      split at hlt
      · next hsplit => rw [if_pos hsplit]; omega
      · next hsplit =>
        rw [if_neg hsplit]
        have hva : ∀ w ∈ a.vars, w ∈ denseRncCapGo cap a acc := iha acc (by omega)
        have hmono := (denseRncCapGo_mono cap b (denseRncCapGo cap a acc)).1
        rcases List.mem_append.1 (by simpa [DenseExpr.vars] using hv) with h | h
        · exact hmono v (hva v h)
        · exact ihb _ hlt v h

/-- The capped array is exact when it stayed below the cap. -/
theorem denseRncCapVars_mem_iff {c : DenseExpr p} (h : (denseRncCapVars c).size ≤ 8) (v : VarId) :
    v ∈ denseRncCapVars c ↔ v ∈ c.vars := by
  constructor
  · intro hv
    rcases denseRncCapGo_sound 9 c #[] v hv with h' | h'
    · simp at h'
    · exact h'
  · intro hv
    exact denseRncCapGo_complete 9 c #[] (by simpa [denseRncCapVars] using Nat.lt_succ_of_le h) v hv

theorem denseRncCapVars_size_pos_iff {c : DenseExpr p} (h : (denseRncCapVars c).size ≤ 8) :
    1 ≤ (denseRncCapVars c).size ↔ c.hasVar = true := by
  rw [denseHasVar_iff]
  constructor
  · intro hpos hnil
    have hmem : (denseRncCapVars c)[0] ∈ denseRncCapVars c := Array.getElem_mem (by omega)
    rw [denseRncCapVars_mem_iff h, hnil] at hmem
    simp at hmem
  · intro hne
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
    have hmem : v ∈ denseRncCapVars c := (denseRncCapVars_mem_iff h v).2 hv
    simpa using Array.size_pos_of_mem hmem

theorem denseRncSubset_eq {xs : List VarId} {c : DenseExpr p}
    (h : (denseRncCapVars c).size ≤ 8) :
    denseRncSubset xs (denseRncCapVars c) = c.varsInF xs := by
  unfold denseRncSubset
  cases hv : c.varsInF xs with
  | true =>
      have hall := (denseVarsInF_iff xs c).1 hv
      refine Array.all_eq_true'.2 (fun w hw => ?_)
      exact denseContainsFast_of_mem xs w (hall w ((denseRncCapVars_mem_iff h w).1 hw))
  | false =>
      have hnot : ¬ (∀ w ∈ c.vars, w ∈ xs) := fun hall => by
        rw [(denseVarsInF_iff xs c).2 hall] at hv; exact Bool.noConfusion hv
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      exact hnot (fun w hw => denseContainsFast_sound xs w
        (Array.all_eq_true'.1 hcon w ((denseRncCapVars_mem_iff h w).2 hw)))

/-- The array-level covered test is `denseCoveredBy`. -/
theorem denseRncCovered_eq (xs : List VarId) (c : DenseExpr p) :
    denseRncCovered xs (denseRncCapVars c) c = denseCoveredBy xs c := by
  unfold denseRncCovered
  split
  · next h =>
      rw [denseCoveredBy, denseRncSubset_eq h]
      cases hv : c.hasVar with
      | true => simp [(denseRncCapVars_size_pos_iff h).2 hv]
      | false =>
          have hz : ¬ (1 ≤ (denseRncCapVars c).size) := fun hpos => by
            rw [(denseRncCapVars_size_pos_iff h).1 hpos] at hv; exact Bool.noConfusion hv
          simp [hz]
  · rfl

/-- The array-level `sharesVarIn` test. -/
theorem denseRncShares_eq (xs : List VarId) (c : DenseExpr p) :
    denseRncShares xs (denseRncCapVars c) c = c.sharesVarIn xs := by
  unfold denseRncShares
  split
  · next h =>
      cases hs : c.sharesVarIn xs with
      | true =>
          obtain ⟨w, hw, hx⟩ := (denseSharesVarIn_iff xs c).1 hs
          exact Array.any_eq_true'.2
            ⟨w, (denseRncCapVars_mem_iff h w).2 hw, denseContainsFast_of_mem xs w hx⟩
      | false =>
          by_contra hcon
          rw [Bool.not_eq_false] at hcon
          obtain ⟨w, hw, hx⟩ := Array.any_eq_true'.1 hcon
          have := (denseSharesVarIn_iff xs c).2
            ⟨w, (denseRncCapVars_mem_iff h w).1 hw, denseContainsFast_sound xs w hx⟩
          rw [hs] at this
          exact Bool.noConfusion this
  · rfl

/-! ### State invariants

Each says the index over-approximates nothing it must find. All are maintained by the write and
consumed either by the covered gather or by the accept's edit list. -/

/-- `cvs` mirrors `cs` positionwise. -/
def DenseRncCvsOk (st : DenseRncState p) : Prop :=
  ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c → st.cvs[i]? = some (denseRncCapVars c)

/-- Every position is listed under its first variable. -/
def DenseRncAnchorOk (st : DenseRncState p) : Prop :=
  ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c →
    ∀ v ∈ denseRncAnchorVars c, i ∈ st.anchor.buckets.getD v []

/-- Every position is listed under each of its variables, and every foldable one is recorded. -/
def DenseRncUseOk (st : DenseRncState p) : Prop :=
  (∀ m, st.useCs = some m → ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c →
    ∀ v ∈ c.vars, i ∈ denseRncBGet m v) ∧
  (∀ s, st.foldCs = some s → ∀ (i : Nat) (c : DenseExpr p), st.cs[i]? = some c →
    denseRncHasFold c = true → s.contains i = true)

def DenseRncBusOk (st : DenseRncState p) : Prop :=
  (∀ m, st.useBis = some m → ∀ (i : Nat) (bi : BusInteraction (DenseExpr p)),
    st.bis[i]? = some bi → ∀ v ∈ denseBIVars bi, i ∈ denseRncBGet m v) ∧
  (∀ s, st.foldBis = some s → ∀ (i : Nat) (bi : BusInteraction (DenseExpr p)),
    st.bis[i]? = some bi → denseRncBiHasFold bi = true → s.contains i = true)

/-- Every live variable is `denseRncSeen` — what decides bit freshness in `O(|bits|)`. -/
def DenseRncVarsOk (st : DenseRncState p) : Prop :=
  ∀ v ∈ (denseRncView st).occ, denseRncSeen st v = true

/-! ### The gathered covered set is the filter -/

theorem denseCoveredIdxPos_map_snd (idx : DenseCovIndex) (arr : Array (DenseExpr p))
    (xs : List VarId) :
    (denseCoveredIdxPos idx arr xs).map Prod.snd
      = denseCoveredIdx idx arr (denseCoveredBy xs) xs := by
  unfold denseCoveredIdxPos denseCoveredIdx
  rw [List.map_filterMap]
  refine List.filterMap_congr (fun i _ => ?_)
  by_cases h : i < arr.size
  · simp only [dif_pos h]
    by_cases hq : denseCoveredBy xs arr[i] = true <;> simp [hq]
  · simp only [dif_neg h, Option.map_none]

/-- A constraint with a variable has a first capped variable, so it is anchored. -/
theorem denseRncAnchorVars_of_hasVar {c : DenseExpr p} (h : c.hasVar = true) :
    ∃ v, denseRncAnchorVars c = [v] ∧ v ∈ c.vars := by
  have hpos : 0 < (denseRncCapVars c).size := by
    by_cases hcap : (denseRncCapVars c).size ≤ 8
    · exact (denseRncCapVars_size_pos_iff hcap).2 h
    · omega
  refine ⟨(denseRncCapVars c)[0], ?_, ?_⟩
  · unfold denseRncAnchorVars
    rw [Array.getElem?_eq_getElem hpos]
  · rcases denseRncCapGo_sound 9 c #[] _ (Array.getElem_mem hpos) with h' | h'
    · simp at h'
    · exact h'

/-- The covered constraints the index gathers are exactly the covered constraints of the view. -/
theorem denseRncEs_eq {st : DenseRncState p} (hanchor : DenseRncAnchorOk st) (xs : List VarId) :
    (denseCoveredIdxPos st.anchor st.cs xs).map Prod.snd
      = denseCoveredCsOf (denseRncView st) xs := by
  rw [denseCoveredIdxPos_map_snd]
  have hcomplete : ∀ (i : Nat) (hi : i < st.cs.toList.length),
      denseCoveredBy xs st.cs.toList[i] = true → i ∈ denseCandidates st.anchor xs := by
    intro i hi hcov
    have hget : st.cs[i]? = some st.cs.toList[i] := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi]
    have hhv : (st.cs.toList[i]).hasVar = true := by
      rw [denseCoveredBy, Bool.and_eq_true] at hcov; exact hcov.1
    obtain ⟨v, hav, hvmem⟩ := denseRncAnchorVars_of_hasVar hhv
    have hvxs : v ∈ xs := by
      rw [denseCoveredBy, Bool.and_eq_true] at hcov
      exact (denseVarsInF_iff xs _).1 hcov.2 v hvmem
    exact denseMem_candidates st.anchor xs v i hvxs
      (hanchor i _ hget v (by rw [hav]; exact List.mem_singleton_self v))
  have hfilter := denseCoveredIdx_eq_filter_of_complete st.anchor st.cs.toList
    (denseCoveredBy xs) xs hcomplete
  rw [Array.toArray_toList] at hfilter
  rw [hfilter]
  show st.cs.toList.filter (denseCoveredBy xs) = _
  unfold denseCoveredCsOf denseRncView
  show _ = ((st.cs.filter (fun c => !denseIsZero c)).toList).filter (denseCoveredBy xs)
  rw [Array.toList_filter]
  exact (List.filter_filter_of st.cs.toList _ _
    (fun c _ hz => denseIsZero_not_covered (by simpa using hz))).symm

/-- The one-pass `(hasVar, hasConstFoldableNode)` walk computes both. -/
theorem denseRncFoldPair_eq (e : DenseExpr p) :
    denseRncFoldPair e = (e.hasVar, e.hasConstFoldableNode) := by
  induction e with
  | const n => rfl
  | var y => rfl
  | add a b iha ihb | mul a b iha ihb =>
      simp only [denseRncFoldPair, iha, ihb, DenseExpr.hasVar, DenseExpr.hasConstFoldableNode]

theorem denseRncHasFold_eq (e : DenseExpr p) : denseRncHasFold e = e.hasConstFoldableNode := by
  rw [denseRncHasFold, denseRncFoldPair_eq]

theorem denseRncBiHasFold_eq (bi : BusInteraction (DenseExpr p)) :
    denseRncBiHasFold bi = denseBiHasFold bi := by
  unfold denseRncBiHasFold denseBiHasFold
  rw [denseRncHasFold_eq]
  have : ∀ (l : List (DenseExpr p)), l.any denseRncHasFold
      = l.any (fun e => e.hasConstFoldableNode) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih => rw [List.any_cons, List.any_cons, denseRncHasFold_eq, ih]
  rw [this]

/-! ### The certificate

`denseRncCert` is the audited `denseCheckReencode` with two substitutions: the covered set comes from
the index (`denseRncEs_eq`) and freshness from `varSeen` (the invariant plus
`denseFreshScan_of_notMemOcc`). -/

theorem denseRncCert_sound {st : DenseRncState p} {xs : List VarId} {cd : DenseRncCand p}
    (hanchor : DenseRncAnchorOk st) (hvars : DenseRncVarsOk st)
    (hes : cd.es = (denseCoveredIdxPos st.anchor st.cs xs).map Prod.snd)
    (h : denseRncCert st xs cd = true) :
    denseCheckReencode (denseRncView st) xs cd.bits cd.hm.get = true := by
  rw [denseRncCert, Bool.and_eq_true] at h
  obtain ⟨hfresh, hchk⟩ := h
  refine denseCheckReencode_of_parts _ xs cd.bits cd.hm.get ?_ ?_
  · rw [denseCheckReencodeNoFresh_eq_Es, ← denseRncEs_eq hanchor xs, ← hes]
    exact hchk
  · refine denseFreshScan_of_notMemOcc _ cd.bits ?_
    intro b hb hmem
    have hseen := hvars b hmem
    have hnb := List.all_eq_true.mp hfresh b hb
    rw [hseen] at hnb
    exact Bool.noConfusion hnb

/-! ### Writing a list of positional edits into an array

The accept installs its edits by folding `Array.setIfInBounds` over distinct positions. These three
lemmas are what turn that fold into a positionwise map. -/

section ArrFold
variable {α : Type}

def denseArrSet (a : Array α) (q : Nat × α) : Array α := a.setIfInBounds q.1 q.2

theorem denseArrFold_size (l : List (Nat × α)) :
    ∀ (a : Array α), (l.foldl denseArrSet a).size = a.size := by
  induction l with
  | nil => intro a; rfl
  | cons q rest ih => intro a; rw [List.foldl_cons, ih]; simp [denseArrSet]

theorem denseArrFold_stable (l : List (Nat × α)) :
    ∀ (a : Array α) (j : Nat), j ∉ l.map Prod.fst → (l.foldl denseArrSet a)[j]? = a[j]? := by
  induction l with
  | nil => intro a j _; rfl
  | cons q rest ih =>
      intro a j hj
      simp only [List.map_cons, List.mem_cons, not_or] at hj
      rw [List.foldl_cons, ih _ j hj.2, denseArrSet,
        Array.getElem?_setIfInBounds_ne (fun h => hj.1 h.symm)]

theorem denseArrFold_hit (l : List (Nat × α)) :
    ∀ (a : Array α) (i : Nat) (x : α), (l.map Prod.fst).Nodup → (i, x) ∈ l → i < a.size →
      (l.foldl denseArrSet a)[i]? = some x := by
  induction l with
  | nil => intro a i x _ hmem _; simp at hmem
  | cons q rest ih =>
      intro a i x hnd hmem hlt
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hmem with heq | hmem'
      · subst heq
        rw [List.foldl_cons, denseArrFold_stable rest _ i hnd.1, denseArrSet,
          Array.getElem?_setIfInBounds_self_of_lt hlt]
      · rw [List.foldl_cons]
        exact ih _ i x hnd.2 hmem' (by rw [denseArrSet]; simpa using hlt)

end ArrFold

/-! ### The accept's write

`denseRncWrite` installs the constraint edits, the bus edits and the booleanity constraints. Each
setter touches one field at one position, so the fold is the positionwise `denseTombify` map — and
from there `denseTombify_filter` (the list engine's lemma) finishes the view. -/

theorem denseRncCsStep_cs (ctx : DenseRncCtx p) (st : DenseRncState p) (e : DenseRncCsEdit p) :
    (denseRncCsStep ctx st e).cs = st.cs.setIfInBounds e.pos (e.content ctx) := by
  cases e <;> rfl

theorem denseRncCsFold_cs (ctx : DenseRncCtx p) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p),
      (es.foldl (denseRncCsStep ctx) st).cs
        = (es.map (fun e => (e.pos, e.content ctx))).foldl denseArrSet st.cs := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih =>
      intro st
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, denseRncCsStep_cs]
      rfl

theorem denseRncBiFold_bis :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p),
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).bis = es.foldl denseArrSet st.bis := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih => intro st; rw [List.foldl_cons, ih, List.foldl_cons]; rfl

theorem denseRncCsFold_bis (ctx : DenseRncCtx p) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p),
      (es.foldl (denseRncCsStep ctx) st).bis = st.bis := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih => intro st; rw [List.foldl_cons, ih]; cases e <;> rfl

theorem denseRncBiFold_cs :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p),
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).cs = st.cs := by
  intro es
  induction es with
  | nil => intro st; rfl
  | cons e rest ih => intro st; rw [List.foldl_cons, ih]; rfl

theorem denseRncBoolFold_cs :
    ∀ (bits : List VarId) (st : DenseRncState p),
      (bits.foldl (fun st b => st.pushBool b) st).cs
        = st.cs ++ (bits.map (denseBoolConstraint (p := p))).toArray := by
  intro bits
  induction bits with
  | nil => intro st; simp
  | cons b rest ih =>
      intro st
      rw [List.foldl_cons, ih, List.map_cons]
      show (st.cs.push (denseBoolConstraint b)) ++ _ = _
      simp

theorem denseRncBoolFold_bis :
    ∀ (bits : List VarId) (st : DenseRncState p),
      (bits.foldl (fun st b => st.pushBool b) st).bis = st.bis := by
  intro bits
  induction bits with
  | nil => intro st; rfl
  | cons b rest ih => intro st; rw [List.foldl_cons, ih]; rfl

/-! ### What the edit builders produce

Three facts per builder: the positions are a sublist of the (duplicate-free) candidate list, each
edit installs the positionwise `denseTombify` (resp. the gated bus rewrite), and every position the
rewrite can change is listed. -/

theorem denseRncPosList_nodup (bs : Array (Array Nat)) (xs : List VarId) (extra : List Nat) :
    (denseRncPosList bs xs extra).Nodup :=
  Std.HashSet.distinct_toList.imp (fun {a b} h => by simpa using h)

theorem denseRncPosList_mem (bs : Array (Array Nat)) (xs : List VarId) (extra : List Nat)
    (i : Nat) (h : (∃ v ∈ xs, i ∈ denseRncBGet bs v) ∨ i ∈ extra) :
    i ∈ denseRncPosList bs xs extra := by
  rw [denseRncPosList, Std.HashSet.mem_toList, mem_foldl_insert]
  refine Or.inr ?_
  rw [List.mem_append]
  rcases h with ⟨v, hv, hi⟩ | hi
  · exact Or.inl (List.mem_flatMap.2 ⟨v, hv, by simpa using hi⟩)
  · exact Or.inr hi

section CsEdits
variable (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId) (cd : DenseRncCand p)

/-- The builder's per-position body, as a standalone function so the three lemmas share it. -/
private def csBody (i : Nat) (acc : List (DenseRncCsEdit p) × Bool) :
    List (DenseRncCsEdit p) × Bool :=
  match st.cs[i]?, st.cvs[i]? with
  | some c, some vs =>
    if denseRncCovered xs vs c then (.tomb i :: acc.1, acc.2)
    else if denseRncShares xs vs c || denseRncHasFold c then
      let c' := denseGroupRewrite xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get c
      let cv' := denseRncCapVars c'
      (.cst i c' cv' (denseRncFullVars c' cv') :: acc.1,
        acc.2 && decide (c'.degree ≤ ctx.dmaxC))
    else acc
  | _, _ => acc

private theorem csEdits_eq_foldr :
    (denseRncCsEdits ctx st xs cd).1
      = ((denseRncPosList (match st.useCs with | some m => m | none => #[]) xs
          (match st.foldCs with | some s => s | none => ∅).toList).foldr (csBody ctx st xs cd)
          ([], true)).1 := rfl

private theorem csBody_sublist (l : List Nat) :
    ((l.foldr (csBody ctx st xs cd) ([], true)).1.map DenseRncCsEdit.pos).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i rest ih =>
      rw [List.foldr_cons]
      cases hc : st.cs[i]? with
      | none => simpa only [csBody, hc] using ih.trans (List.sublist_cons_self i rest)
      | some c =>
        cases hvs : st.cvs[i]? with
        | none => simpa only [csBody, hc, hvs] using ih.trans (List.sublist_cons_self i rest)
        | some vs =>
          simp only [csBody, hc, hvs]
          by_cases hcov : denseRncCovered xs vs c = true
          · rw [if_pos hcov]
            simpa only [List.map_cons, DenseRncCsEdit.pos] using List.cons_sublist_cons.2 ih
          · rw [if_neg hcov]
            by_cases hg : denseRncShares xs vs c || denseRncHasFold c
            · rw [if_pos hg]
              simpa only [List.map_cons, DenseRncCsEdit.pos] using List.cons_sublist_cons.2 ih
            · rw [if_neg hg]
              exact ih.trans (List.sublist_cons_self i rest)

private theorem csBody_content (hcvs : DenseRncCvsOk st)
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) (l : List Nat) :
    ∀ e ∈ (l.foldr (csBody ctx st xs cd) ([], true)).1, ∃ c, st.cs[e.pos]? = some c ∧
      e.content ctx
        = denseTombify xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get c := by
  induction l with
  | nil => intro e he; simp at he
  | cons i rest ih =>
      intro e he
      rw [List.foldr_cons] at he
      cases hc : st.cs[i]? with
      | none => exact ih e (by simpa only [csBody, hc] using he)
      | some c =>
        have hvs : st.cvs[i]? = some (denseRncCapVars c) := hcvs i c hc
        simp only [csBody, hc, hvs] at he
        rw [denseRncCovered_eq] at he
        by_cases hcov : denseCoveredBy xs c = true
        · rw [if_pos hcov] at he
          rcases List.mem_cons.1 he with rfl | he'
          · exact ⟨c, by simpa [DenseRncCsEdit.pos] using hc,
              by simp [DenseRncCsEdit.content, hzero, denseTombify, hcov]⟩
          · exact ih e he'
        · rw [if_neg hcov] at he
          by_cases hg : denseRncShares xs (denseRncCapVars c) c || denseRncHasFold c
          · rw [if_pos hg] at he
            rcases List.mem_cons.1 he with rfl | he'
            · refine ⟨c, by simpa [DenseRncCsEdit.pos] using hc, ?_⟩
              have hcov' : denseCoveredBy xs c = false := by simpa using hcov
              simp only [DenseRncCsEdit.content, denseTombify, hcov', if_false,
                Bool.false_eq_true]
            · exact ih e he'
          · rw [if_neg hg] at he
            exact ih e he

private theorem csBody_complete (hcvs : DenseRncCvsOk st) (l : List Nat) (j : Nat)
    (c : DenseExpr p) (hj : j ∈ l) (hc : st.cs[j]? = some c)
    (hfires : denseCoveredBy xs c = true ∨ c.sharesVarIn xs = true ∨
      c.hasConstFoldableNode = true) :
    j ∈ (l.foldr (csBody ctx st xs cd) ([], true)).1.map DenseRncCsEdit.pos := by
  induction l with
  | nil => simp at hj
  | cons i rest ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hj with rfl | hj'
      · have hvs : st.cvs[j]? = some (denseRncCapVars c) := hcvs j c hc
        simp only [csBody, hc, hvs]
        rw [denseRncCovered_eq]
        by_cases hcov : denseCoveredBy xs c = true
        · rw [if_pos hcov]; simp [DenseRncCsEdit.pos]
        · rw [if_neg hcov, denseRncShares_eq, denseRncHasFold_eq]
          have hg : (c.sharesVarIn xs || c.hasConstFoldableNode) = true := by
            rcases hfires with h | h | h
            · exact absurd h hcov
            · simp [h]
            · simp [h]
          rw [if_pos hg]
          simp [DenseRncCsEdit.pos]
      · have hrec := ih hj'
        cases hc0 : st.cs[i]? with
        | none => simpa only [csBody, hc0] using hrec
        | some c0 =>
          cases hvs0 : st.cvs[i]? with
          | none => simpa only [csBody, hc0, hvs0] using hrec
          | some vs0 =>
            simp only [csBody, hc0, hvs0]
            by_cases hcov : denseRncCovered xs vs0 c0 = true
            · rw [if_pos hcov]; simpa using Or.inr hrec
            · rw [if_neg hcov]
              by_cases hg : denseRncShares xs vs0 c0 || denseRncHasFold c0
              · rw [if_pos hg]; simpa using Or.inr hrec
              · rw [if_neg hg]; exact hrec

end CsEdits

section BiEdits
variable (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId) (cd : DenseRncCand p)

private def biBody (i : Nat) (acc : List (Nat × BusInteraction (DenseExpr p)) × Bool) :
    List (Nat × BusInteraction (DenseExpr p)) × Bool :=
  match st.bis[i]? with
  | some bi =>
    if bi.multiplicity.sharesVarIn xs || denseRncHasFold bi.multiplicity
        || bi.payload.any (fun e => e.sharesVarIn xs || denseRncHasFold e) then
      let bi' : BusInteraction (DenseExpr p) :=
        { bi with
          multiplicity := denseGroupRewrite xs cd.bits (denseGroupSubst xs cd.hm.get)
            cd.patts.get bi.multiplicity,
          payload := bi.payload.map
            (denseGroupRewrite xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get) }
      ((i, bi') :: acc.1,
        acc.2 && decide (bi'.multiplicity.degree ≤ ctx.dmaxB)
          && bi'.payload.all (fun e => decide (e.degree ≤ ctx.dmaxB)))
    else acc
  | none => acc

private theorem biEdits_eq_foldr :
    (denseRncBiEdits ctx st xs cd).1
      = ((denseRncPosList (match st.useBis with | some m => m | none => #[]) xs
          (match st.foldBis with | some s => s | none => ∅).toList).foldr (biBody ctx st xs cd)
          ([], true)).1 := rfl

/-- The gate test the builder uses is `denseBiGateFires`. -/
private theorem biBody_fires (bi : BusInteraction (DenseExpr p)) :
    (bi.multiplicity.sharesVarIn xs || denseRncHasFold bi.multiplicity
      || bi.payload.any (fun e => e.sharesVarIn xs || denseRncHasFold e))
      = denseBiGateFires xs bi := by
  unfold denseBiGateFires
  rw [denseRncHasFold_eq]
  have hp : ∀ (l : List (DenseExpr p)),
      l.any (fun e => e.sharesVarIn xs || denseRncHasFold e)
        = l.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih => rw [List.any_cons, List.any_cons, denseRncHasFold_eq, ih]
  rw [hp]

private theorem biBody_sublist (l : List Nat) :
    ((l.foldr (biBody ctx st xs cd) ([], true)).1.map Prod.fst).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i rest ih =>
      rw [List.foldr_cons]
      cases hb : st.bis[i]? with
      | none => simpa only [biBody, hb] using ih.trans (List.sublist_cons_self i rest)
      | some bi =>
        simp only [biBody, hb]
        split
        · simpa only [List.map_cons] using List.cons_sublist_cons.2 ih
        · exact ih.trans (List.sublist_cons_self i rest)

private theorem biBody_content (l : List Nat) :
    ∀ q ∈ (l.foldr (biBody ctx st xs cd) ([], true)).1, ∃ bi, st.bis[q.1]? = some bi ∧
      q.2 = denseBIRewriteGate xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get bi := by
  induction l with
  | nil => intro q hq; simp at hq
  | cons i rest ih =>
      intro q hq
      rw [List.foldr_cons] at hq
      cases hb : st.bis[i]? with
      | none => exact ih q (by simpa only [biBody, hb] using hq)
      | some bi =>
        simp only [biBody, hb] at hq
        split at hq
        · next hgate =>
            rcases List.mem_cons.1 hq with rfl | hq'
            · refine ⟨bi, hb, ?_⟩
              have hgate' : (bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
                  || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode)) = true := by
                rw [biBody_fires (p := p) xs bi] at hgate
                simpa [denseBiGateFires] using hgate
              unfold denseBIRewriteGate
              rw [if_pos (by simpa using hgate')]
              simp only [denseGroupRewriteGate_eq]
            · exact ih q hq'
        · exact ih q hq

private theorem biBody_complete (l : List Nat) (j : Nat) (bi : BusInteraction (DenseExpr p))
    (hj : j ∈ l) (hb : st.bis[j]? = some bi) (hfires : denseBiGateFires xs bi = true) :
    j ∈ (l.foldr (biBody ctx st xs cd) ([], true)).1.map Prod.fst := by
  induction l with
  | nil => simp at hj
  | cons i rest ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hj with rfl | hj'
      · simp only [biBody, hb]
        rw [if_pos (by rw [biBody_fires]; exact hfires)]
        simp
      · have hrec := ih hj'
        cases hb0 : st.bis[i]? with
        | none => simpa only [biBody, hb0] using hrec
        | some bi0 =>
          simp only [biBody, hb0]
          split
          · simpa using Or.inr hrec
          · exact hrec

end BiEdits

/-! ### The write installs the positionwise `denseTombify` -/

theorem denseRncCsEdits_nodup (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : ((denseRncCsEdits ctx st xs cd).1.map DenseRncCsEdit.pos).Nodup := by
  rw [csEdits_eq_foldr]
  exact (denseRncPosList_nodup _ xs _).sublist (csBody_sublist ctx st xs cd _)

theorem denseRncBiEdits_nodup (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : ((denseRncBiEdits ctx st xs cd).1.map Prod.fst).Nodup := by
  rw [biEdits_eq_foldr]
  exact (denseRncPosList_nodup _ xs _).sublist (biBody_sublist ctx st xs cd _)

theorem denseRncCsEdits_complete {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf) :
    ∀ (j : Nat) (c : DenseExpr p), st.cs[j]? = some c →
      (denseCoveredBy xs c = true ∨ c.sharesVarIn xs = true ∨ c.hasConstFoldableNode = true) →
      j ∈ (denseRncCsEdits ctx st xs cd).1.map DenseRncCsEdit.pos := by
  intro j c hc hfires
  rw [csEdits_eq_foldr]
  refine csBody_complete ctx st xs cd hcvs _ j c ?_ hc hfires
  rw [hm, hs]
  refine denseRncPosList_mem _ _ _ j ?_
  rcases hfires with hcov | hsh | hfd
  · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs c).1 (denseCoveredBy_sharesVarIn hcov)
    exact Or.inl ⟨v, hx, huse.1 m hm j c hc v hv⟩
  · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs c).1 hsh
    exact Or.inl ⟨v, hx, huse.1 m hm j c hc v hv⟩
  · refine Or.inr ?_
    have hcontains := huse.2 sf hs j c hc (by rw [denseRncHasFold_eq]; exact hfd)
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
    exact hcontains

theorem denseRncBiEdits_complete {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hbus : DenseRncBusOk st) (hm : st.useBis = some m) (hs : st.foldBis = some sf) :
    ∀ (j : Nat) (bi : BusInteraction (DenseExpr p)), st.bis[j]? = some bi →
      denseBiGateFires xs bi = true → j ∈ (denseRncBiEdits ctx st xs cd).1.map Prod.fst := by
  intro j bi hb hfires
  rw [biEdits_eq_foldr]
  refine biBody_complete ctx st xs cd _ j bi ?_ hb hfires
  rw [hm, hs]
  refine denseRncPosList_mem _ _ _ j ?_
  rw [denseBiGateFires, Bool.or_eq_true, Bool.or_eq_true] at hfires
  rcases hfires with (hmul | hfd) | hpl
  · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs _).1 hmul
    exact Or.inl ⟨v, hx, hbus.1 m hm j bi hb v (by simp [denseBIVars, hv])⟩
  · refine Or.inr ?_
    have hcontains := hbus.2 sf hs j bi hb (by
      rw [denseRncBiHasFold_eq]; simp [denseBiHasFold, hfd])
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
    exact hcontains
  · rw [List.any_eq_true] at hpl
    obtain ⟨e, he, hor⟩ := hpl
    rw [Bool.or_eq_true] at hor
    rcases hor with hsh | hfd
    · obtain ⟨v, hv, hx⟩ := (denseSharesVarIn_iff xs e).1 hsh
      refine Or.inl ⟨v, hx, hbus.1 m hm j bi hb v ?_⟩
      simp only [denseBIVars, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨e, he, hv⟩
    · refine Or.inr ?_
      have hcontains := hbus.2 sf hs j bi hb (by
        rw [denseRncBiHasFold_eq]
        simp only [denseBiHasFold, Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨e, he, hfd⟩)
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
      exact hcontains

/-- The constraint array after the write: the positionwise tombify, then the booleanity
    constraints. -/
theorem denseRncWrite_cs_toList {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf) :
    (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1).cs.toList
      = st.cs.toList.map (denseTombify xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get)
        ++ cd.bits.map denseBoolConstraint := by
  set σ := denseGroupSubst xs cd.hm.get with hσ
  set patts := cd.patts.get with hpatts
  set es := (denseRncCsEdits ctx st xs cd).1 with hes
  have hcs : (denseRncWrite ctx st cd.bits es (denseRncBiEdits ctx st xs cd).1).cs
      = (es.map (fun e => (e.pos, e.content ctx))).foldl denseArrSet st.cs
        ++ (cd.bits.map (denseBoolConstraint (p := p))).toArray := by
    show ((cd.bits.foldl (fun st b => st.pushBool b)
      (((denseRncBiEdits ctx st xs cd).1).foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        (es.foldl (denseRncCsStep ctx) st))).domReset).cs = _
    show (cd.bits.foldl (fun st b => st.pushBool b)
      (((denseRncBiEdits ctx st xs cd).1).foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        (es.foldl (denseRncCsStep ctx) st))).cs = _
    rw [denseRncBoolFold_cs, denseRncBiFold_cs, denseRncCsFold_cs]
  rw [hcs]
  have hlen : ((es.map (fun e => (e.pos, e.content ctx))).foldl denseArrSet st.cs).size
      = st.cs.size := denseArrFold_size _ _
  rw [Array.toList_append, List.toList_toArray]
  refine congrArg (· ++ cd.bits.map denseBoolConstraint) ?_
  refine List.ext_getElem? (fun j => ?_)
  rw [Array.getElem?_toList, List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < st.cs.size
  · have hcget : st.cs[j]? = some st.cs[j] := Array.getElem?_eq_getElem hj
    rw [hcget, Option.map_some]
    by_cases hedit : j ∈ es.map DenseRncCsEdit.pos
    · obtain ⟨e, hemem, hepos⟩ := List.mem_map.1 hedit
      obtain ⟨c0, hc0, hcontent⟩ := csBody_content ctx st xs cd hcvs hzero _ e
        (by rwa [hes, csEdits_eq_foldr] at hemem)
      have hc0' : c0 = st.cs[j] := by rw [hepos] at hc0; rw [hcget] at hc0; exact (Option.some.inj hc0).symm
      subst hc0'
      have := denseArrFold_hit (es.map (fun e => (e.pos, e.content ctx))) st.cs e.pos
        (e.content ctx)
        (by simpa [List.map_map, Function.comp_def] using denseRncCsEdits_nodup ctx st xs cd)
        (List.mem_map.2 ⟨e, hemem, rfl⟩) (by rw [hepos]; exact hj)
      rw [hepos] at this
      rw [this, hcontent]
    · have hstable := denseArrFold_stable (es.map (fun e => (e.pos, e.content ctx))) st.cs j
        (by simpa [List.map_map, Function.comp_def] using hedit)
      rw [hstable, hcget]
      have hnf : ¬ (denseCoveredBy xs st.cs[j] = true ∨ st.cs[j].sharesVarIn xs = true ∨
          st.cs[j].hasConstFoldableNode = true) := fun hfires =>
        hedit (denseRncCsEdits_complete hcvs huse hm hs j st.cs[j] hcget hfires)
      rw [not_or, not_or] at hnf
      obtain ⟨h1, h2, h3⟩ := hnf
      simp only [denseTombify, Bool.not_eq_true] at *
      rw [if_neg (by simpa using h1),
        denseGroupRewrite_eq_self (by simpa using h2) (by simpa using h3)]
  · have hnone : st.cs[j]? = none := Array.getElem?_eq_none (by omega)
    rw [hnone, Option.map_none, Array.getElem?_eq_none (by omega)]

/-- The interaction array after the write: the positionwise gated rewrite. -/
theorem denseRncWrite_bis_toList {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m : Array (Array Nat)} {sf : Std.HashSet Nat}
    (hbus : DenseRncBusOk st) (hm : st.useBis = some m) (hs : st.foldBis = some sf) :
    (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1).bis.toList
      = st.bis.toList.map
          (denseBIRewriteGate xs cd.bits (denseGroupSubst xs cd.hm.get) cd.patts.get) := by
  set es := (denseRncBiEdits ctx st xs cd).1 with hes
  have hbis : (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1 es).bis
      = es.foldl denseArrSet st.bis := by
    show (cd.bits.foldl (fun st b => st.pushBool b)
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        ((denseRncCsEdits ctx st xs cd).1.foldl (denseRncCsStep ctx) st))).bis = _
    rw [denseRncBoolFold_bis, denseRncBiFold_bis, denseRncCsFold_bis]
  rw [hbis]
  refine List.ext_getElem? (fun j => ?_)
  rw [Array.getElem?_toList, List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < st.bis.size
  · have hbget : st.bis[j]? = some st.bis[j] := Array.getElem?_eq_getElem hj
    rw [hbget, Option.map_some]
    by_cases hedit : j ∈ es.map Prod.fst
    · obtain ⟨q, hqmem, hqpos⟩ := List.mem_map.1 hedit
      obtain ⟨bi0, hb0, hcontent⟩ := biBody_content ctx st xs cd _ q
        (by rwa [hes, biEdits_eq_foldr] at hqmem)
      have hb0' : bi0 = st.bis[j] := by
        rw [hqpos] at hb0; rw [hbget] at hb0; exact (Option.some.inj hb0).symm
      subst hb0'
      have := denseArrFold_hit es st.bis q.1 q.2 (denseRncBiEdits_nodup ctx st xs cd)
        (by simpa using hqmem) (by rw [hqpos]; exact hj)
      rw [hqpos] at this
      rw [this, hcontent]
    · rw [denseArrFold_stable es st.bis j (by simpa using hedit), hbget]
      have hnf : denseBiGateFires xs st.bis[j] = false := by
        cases hf : denseBiGateFires xs st.bis[j] with
        | false => rfl
        | true => exact absurd (denseRncBiEdits_complete hbus hm hs j st.bis[j] hbget hf) hedit
      unfold denseBIRewriteGate
      rw [if_neg (by simpa [denseBiGateFires] using hnf)]
  · have hsz : (es.foldl denseArrSet st.bis).size = st.bis.size := denseArrFold_size _ _
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega), Option.map_none]

/-- The written state's view is the re-encoded system with trivially-true constraints dropped —
    the array engine's counterpart of `denseWorkOut_view`. -/
theorem denseRncWrite_view {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m mB : Array (Array Nat)} {sf sfB : Std.HashSet Nat}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (hpatts : cd.patts.get = denseAssignments (denseBitBox cd.bits))
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st) (hbus : DenseRncBusOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf)
    (hmB : st.useBis = some mB) (hsB : st.foldBis = some sfB) :
    denseRncView (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1)
      = (denseReencodeOut (denseRncView st) xs cd.bits cd.hm.get).filterConstraints
          (fun c => !denseIsZero c) := by
  have hcsL := denseRncWrite_cs_toList (xs := xs) (cd := cd) hzero hcvs huse hm hs
  have hbisL := denseRncWrite_bis_toList (ctx := ctx) (xs := xs) (cd := cd) hbus hmB hsB
  rw [hpatts] at hcsL hbisL
  unfold denseRncView DenseConstraintSystem.filterConstraints denseReencodeOut
  dsimp only
  refine congrArg₂ DenseConstraintSystem.mk ?_ ?_
  · rw [Array.toList_filter, hcsL, List.filter_append, denseBoolConstraints_not_zero,
      List.filter_append, denseBoolConstraints_not_zero, Array.toList_filter, denseTombify_filter]
  · rw [hbisL, denseBIRewriteGate_eq]

/-! ### The indexes survive the write

Every setter writes one position of one array and only ever *adds* index entries, so each invariant
is preserved pointwise. The bundled `DenseRncOk` is what the loop threads. -/

structure DenseRncOk (st : DenseRncState p) : Prop where
  sizes : st.cvs.size = st.cs.size
  cvs : DenseRncCvsOk st
  anchor : DenseRncAnchorOk st
  use : DenseRncUseOk st
  bus : DenseRncBusOk st

theorem denseRncCapVars_const_zero : denseRncCapVars (DenseExpr.const 0 : DenseExpr p) = #[] := rfl

theorem denseRncCapVars_bool (b : VarId) :
    denseRncCapVars (denseBoolConstraint b : DenseExpr p) = #[b] := by
  simp [denseRncCapVars, denseRncCapGo, denseBoolConstraint]


/-- Growing an array does not change any existing entry. -/
theorem denseArrEnsure_getD {α : Type} (a : Array α) (i j : Nat) (d : α) :
    (denseArrEnsure a i d).getD j d = a.getD j d := by
  unfold denseArrEnsure
  split
  · rfl
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    by_cases hj : j < a.size
    · rw [Array.getElem?_append_left hj]
    · have hR : a[j]? = none := Array.getElem?_eq_none (by omega)
      have hL : ((a ++ Array.replicate (max (i + 1) (2 * a.size) - a.size) d)[j]?).getD d = d := by
        rw [Array.getElem?_append_right (by omega), Array.getElem?_replicate]
        split <;> rfl
      rw [hL, hR]
      rfl

theorem denseArrEnsure_size {α : Type} (a : Array α) (i : Nat) (d : α) :
    i < (denseArrEnsure a i d).size := by
  unfold denseArrEnsure
  split
  · omega
  · rw [Array.size_append, Array.size_replicate]
    omega

theorem denseRncBAdd_mono (m : Array (Array Nat)) (w : VarId) (i j : Nat) (v : VarId)
    (h : j ∈ denseRncBGet m v) : j ∈ denseRncBGet (denseRncBAdd m w i) v := by
  have hkeep : (denseArrEnsure m w.index #[]).getD v.index #[] = m.getD v.index #[] :=
    denseArrEnsure_getD m w.index v.index #[]
  unfold denseRncBGet denseRncBAdd at *
  rw [← hkeep] at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  rw [Array.getD_eq_getD_getElem?] at h
  by_cases hw : w.index = v.index
  · rw [if_pos hw]
    cases hget : (denseArrEnsure m w.index #[])[v.index]? with
    | none => rw [hget] at h; simp at h
    | some a =>
        rw [hget] at h
        simp only [Option.map_some, Option.getD_some] at h ⊢
        exact Array.mem_push.2 (Or.inl h)
  · rw [if_neg hw]
    exact h

theorem denseRncBAdd_self (m : Array (Array Nat)) (w : VarId) (i : Nat) :
    i ∈ denseRncBGet (denseRncBAdd m w i) w := by
  unfold denseRncBGet denseRncBAdd
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, if_pos rfl,
    Array.getElem?_eq_getElem (denseArrEnsure_size m w.index #[])]
  simp

theorem denseRncAnchorAdd_mono (idx : DenseCovIndex) (ks : List VarId) (i j : Nat) (v : VarId)
    (h : j ∈ idx.buckets.getD v []) : j ∈ (denseRncAnchorAdd idx ks i).buckets.getD v [] := by
  unfold denseRncAnchorAdd
  cases ks with
  | nil => exact h
  | cons w rest =>
      by_cases hw : v = w
      · subst hw
        show j ∈ (idx.buckets.insert v (i :: idx.buckets.getD v [])).getD v []
        rw [Std.HashMap.getD_insert_self]
        exact List.mem_cons_of_mem i h
      · show j ∈ (idx.buckets.insert w (i :: idx.buckets.getD w [])).getD v []
        rw [Std.HashMap.getD_insert, if_neg (by simpa using fun hh => hw hh.symm)]
        exact h

theorem denseRncAnchorAdd_self (idx : DenseCovIndex) (v : VarId) (rest : List VarId) (i : Nat) :
    i ∈ (denseRncAnchorAdd idx (v :: rest) i).buckets.getD v [] := by
  show i ∈ (idx.buckets.insert v (i :: idx.buckets.getD v [])).getD v []
  rw [Std.HashMap.getD_insert_self]
  exact List.mem_cons_self

theorem denseRncBFoldL_mono (i : Nat) :
    ∀ (vs : List VarId) (m : Array (Array Nat)) (v : VarId) (j : Nat), j ∈ denseRncBGet m v →
      j ∈ denseRncBGet (vs.foldl (fun m w => denseRncBAdd m w i) m) v := by
  intro vs
  induction vs with
  | nil => intro m v j h; exact h
  | cons w rest ih => intro m v j h; exact ih _ v j (denseRncBAdd_mono m w i j v h)

theorem denseRncBFoldL_self (i : Nat) :
    ∀ (vs : List VarId) (m : Array (Array Nat)) (v : VarId), v ∈ vs →
      i ∈ denseRncBGet (vs.foldl (fun m w => denseRncBAdd m w i) m) v := by
  intro vs
  induction vs with
  | nil => intro m v hv; simp at hv
  | cons w rest ih =>
      intro m v hv
      rcases List.mem_cons.1 hv with rfl | hv'
      · exact denseRncBFoldL_mono i rest _ v i (denseRncBAdd_self m v i)
      · exact ih _ v hv'

theorem denseRncFullVars_mem {c : DenseExpr p} {v : VarId} (h : v ∈ c.vars) :
    v ∈ denseRncFullVars c (denseRncCapVars c) := by
  unfold denseRncFullVars
  split
  · next hle => exact (denseRncCapVars_mem_iff hle v).2 h
  · rw [HashedDedup.hashedDedup_eq]
    simpa using List.mem_dedup.2 h

theorem denseRncSet_getElem?_ne {α : Type} (a : Array α) (i j : Nat) (x : α) (h : i ≠ j) :
    (a.setIfInBounds i x)[j]? = a[j]? := Array.getElem?_setIfInBounds_ne h

theorem denseRncSet_getElem?_self {α : Type} (a : Array α) (i : Nat) (x y : α)
    (h : (a.setIfInBounds i x)[i]? = some y) : i < a.size ∧ y = x := by
  by_cases hlt : i < a.size
  · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at h
    exact ⟨hlt, (Option.some.inj h).symm⟩
  · rw [Array.getElem?_eq_none (by rw [Array.size_setIfInBounds]; omega)] at h
    exact absurd h (by simp)

/-- The constraint write preserves every index invariant: it only ever adds bucket entries, and it
    keeps `cvs`, the anchor and the use index in step with the new content. -/
theorem denseRncOk_rewriteAt {st : DenseRncState p} {i : Nat} {c' : DenseExpr p}
    {cv' full : Array VarId} (h : DenseRncOk st) (hcv : cv' = denseRncCapVars c')
    (hfull : ∀ v ∈ c'.vars, v ∈ full) : DenseRncOk (st.rewriteAt i c' cv' full) := by
  have hcs : (st.rewriteAt i c' cv' full).cs = st.cs.setIfInBounds i c' := rfl
  have hcvs : (st.rewriteAt i c' cv' full).cvs = st.cvs.setIfInBounds i cv' := rfl
  have hanch : (st.rewriteAt i c' cv' full).anchor
      = denseRncAnchorAdd st.anchor (denseRncAnchorVars c') i := rfl
  have huse : (st.rewriteAt i c' cv' full).useCs
      = st.useCs.map (fun m => full.foldl (fun m v => denseRncBAdd m v i) m) := rfl
  have hfold : (st.rewriteAt i c' cv' full).foldCs
      = st.foldCs.map (fun s => if denseRncHasFold c' then s.insert i else s.erase i) := rfl
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hcs, hcvs, Array.size_setIfInBounds, Array.size_setIfInBounds]; exact h.sizes
  · intro j c hj
    rw [hcs] at hj
    rw [hcvs]
    by_cases hij : i = j
    · subst hij
      obtain ⟨hlt, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [h.sizes]; exact hlt), hcv]
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      rw [denseRncSet_getElem?_ne _ _ _ _ hij]
      exact h.cvs j c hj
  · intro j c hj v hv
    rw [hcs] at hj
    rw [hanch]
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      cases hav : denseRncAnchorVars c with
      | nil => rw [hav] at hv; simp at hv
      | cons w rest =>
          have hvw : v = w := by
            rw [hav] at hv
            rcases List.mem_cons.1 hv with h1 | h1
            · exact h1
            · exact absurd h1 (by
                unfold denseRncAnchorVars at hav
                split at hav <;> simp_all)
          subst hvw
          exact denseRncAnchorAdd_self st.anchor v rest i
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      exact denseRncAnchorAdd_mono _ _ i j v (h.anchor j c hj v hv)
  · intro m hm j c hj v hv
    rw [huse] at hm
    obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.1 hm
    rw [hcs] at hj
    have hfl : full.foldl (fun m v => denseRncBAdd m v i) m0
        = full.toList.foldl (fun m v => denseRncBAdd m v i) m0 := by
      conv_lhs => rw [← Array.toArray_toList (xs := full)]
      rw [List.foldl_toArray]
    rw [hfl]
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      exact denseRncBFoldL_self i full.toList m0 v (by simpa using hfull v hv)
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      exact denseRncBFoldL_mono i full.toList m0 v j (h.use.1 m0 hm0 j c hj v hv)
  · intro sf hsf j c hj hfd
    rw [hfold] at hsf
    obtain ⟨s0, hs0, rfl⟩ := Option.map_eq_some_iff.1 hsf
    rw [hcs] at hj
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hcc⟩ := denseRncSet_getElem?_self st.cs i c' c hj
      subst hcc
      rw [if_pos hfd]
      simp
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      have hmem := h.use.2 s0 hs0 j c hj hfd
      split
      · rw [Std.HashSet.contains_insert]; simp [hmem]
      · rw [Std.HashSet.contains_erase]; simp [hmem, hij]
  · exact h.bus

theorem denseRncHasFold_bool (b : VarId) :
    denseRncHasFold (denseBoolConstraint b : DenseExpr p) = false := rfl

theorem denseBoolConstraint_vars (b : VarId) :
    ∀ v ∈ (denseBoolConstraint b : DenseExpr p).vars, v = b := by
  intro v hv
  simpa [denseBoolConstraint, DenseExpr.vars] using hv

theorem denseRncAnchorVars_bool (b : VarId) :
    denseRncAnchorVars (denseBoolConstraint b : DenseExpr p) = [b] := by
  unfold denseRncAnchorVars
  rw [denseRncCapVars_bool]
  rfl

/-- Appending a booleanity constraint preserves every index invariant. -/
theorem denseRncOk_pushBool {st : DenseRncState p} (h : DenseRncOk st) (b : VarId) :
    DenseRncOk (st.pushBool b) := by
  have hcs : (st.pushBool b).cs = st.cs.push (denseBoolConstraint b) := rfl
  have hcvs : (st.pushBool b).cvs = st.cvs.push #[b] := rfl
  have hanch : (st.pushBool b).anchor = denseRncAnchorAdd st.anchor [b] st.cs.size := rfl
  have huse : (st.pushBool b).useCs = st.useCs.map (fun m => denseRncBAdd m b st.cs.size) := rfl
  have hfold : (st.pushBool b).foldCs = st.foldCs := rfl
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hcs, hcvs, Array.size_push, Array.size_push, h.sizes]
  · intro j c hj
    rw [hcs, Array.getElem?_push] at hj
    rw [hcvs, Array.getElem?_push, h.sizes]
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj ⊢
      rw [← Option.some.inj hj, denseRncCapVars_bool]
    · rw [if_neg heq] at hj ⊢
      exact h.cvs j c hj
  · intro j c hj v hv
    rw [hcs, Array.getElem?_push] at hj
    rw [hanch]
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj
      have hc : c = denseBoolConstraint b := (Option.some.inj hj).symm
      subst hc
      rw [denseRncAnchorVars_bool] at hv
      have hvb : v = b := by simpa using hv
      subst hvb
      subst heq
      exact denseRncAnchorAdd_self st.anchor v [] st.cs.size
    · rw [if_neg heq] at hj
      exact denseRncAnchorAdd_mono _ _ _ j v (h.anchor j c hj v hv)
  · intro m hm j c hj v hv
    rw [huse] at hm
    obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.1 hm
    rw [hcs, Array.getElem?_push] at hj
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj
      have hc : c = denseBoolConstraint b := (Option.some.inj hj).symm
      subst hc
      have hvb : v = b := denseBoolConstraint_vars b v hv
      subst hvb
      subst heq
      exact denseRncBAdd_self m0 v st.cs.size
    · rw [if_neg heq] at hj
      exact denseRncBAdd_mono m0 b st.cs.size j v (h.use.1 m0 hm0 j c hj v hv)
  · intro sf hsf j c hj hfd
    rw [hfold] at hsf
    rw [hcs, Array.getElem?_push] at hj
    by_cases heq : j = st.cs.size
    · rw [if_pos heq] at hj
      have hc : c = denseBoolConstraint b := (Option.some.inj hj).symm
      subst hc
      rw [denseRncHasFold_bool] at hfd
      exact absurd hfd (by simp)
    · rw [if_neg heq] at hj
      exact h.use.2 sf hsf j c hj hfd
  · exact h.bus

/-- The bus write preserves the invariants: the constraint side is untouched and the bus index only
    grows. -/
theorem denseRncOk_rewriteBiAt {st : DenseRncState p} (h : DenseRncOk st) (i : Nat)
    (bi' : BusInteraction (DenseExpr p)) : DenseRncOk (st.rewriteBiAt i bi') := by
  have hbis : (st.rewriteBiAt i bi').bis = st.bis.setIfInBounds i bi' := rfl
  have huse : (st.rewriteBiAt i bi').useBis
      = st.useBis.map (fun m => (denseBIVars bi').foldl (fun m v => denseRncBAdd m v i) m) := rfl
  have hfold : (st.rewriteBiAt i bi').foldBis
      = st.foldBis.map (fun s => if denseRncBiHasFold bi' then s.insert i else s.erase i) := rfl
  refine ⟨h.sizes, h.cvs, h.anchor, h.use, ⟨?_, ?_⟩⟩
  · intro m hm j bi hj v hv
    rw [huse] at hm
    obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.1 hm
    rw [hbis] at hj
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hbb⟩ := denseRncSet_getElem?_self st.bis i bi' bi hj
      subst hbb
      exact denseRncBFoldL_self i (denseBIVars bi) m0 v hv
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      exact denseRncBFoldL_mono i (denseBIVars bi') m0 v j (h.bus.1 m0 hm0 j bi hj v hv)
  · intro sf hsf j bi hj hfd
    rw [hfold] at hsf
    obtain ⟨s0, hs0, rfl⟩ := Option.map_eq_some_iff.1 hsf
    rw [hbis] at hj
    by_cases hij : i = j
    · subst hij
      obtain ⟨_, hbb⟩ := denseRncSet_getElem?_self st.bis i bi' bi hj
      subst hbb
      rw [if_pos hfd]
      simp
    · rw [denseRncSet_getElem?_ne _ _ _ _ hij] at hj
      have hmem := h.bus.2 s0 hs0 j bi hj hfd
      split
      · rw [Std.HashSet.contains_insert]; simp [hmem]
      · rw [Std.HashSet.contains_erase]; simp [hmem, hij]

theorem denseRncOk_domReset {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk st.domReset := ⟨h.sizes, h.cvs, h.anchor, h.use, h.bus⟩

/-- What the constraint-edit builder guarantees about each edit's payload. -/
def DenseRncEditOk : DenseRncCsEdit p → Prop
  | .tomb _ => True
  | .cst _ c' cv' full => cv' = denseRncCapVars c' ∧ ∀ v ∈ c'.vars, v ∈ full

theorem denseRncOk_csStep {ctx : DenseRncCtx p} {st : DenseRncState p} {e : DenseRncCsEdit p}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (h : DenseRncOk st) (he : DenseRncEditOk e) : DenseRncOk (denseRncCsStep ctx st e) := by
  cases e with
  | tomb i =>
      refine denseRncOk_rewriteAt h ?_ ?_
      · rw [hzero, denseRncCapVars_const_zero]
      · intro v hv; rw [hzero] at hv; simp [DenseExpr.vars] at hv
  | cst i c' cv' full => exact denseRncOk_rewriteAt h he.1 he.2

theorem denseRncOk_csFold {ctx : DenseRncCtx p}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p), DenseRncOk st →
      (∀ e ∈ es, DenseRncEditOk e) → DenseRncOk (es.foldl (denseRncCsStep ctx) st) := by
  intro es
  induction es with
  | nil => intro st h _; exact h
  | cons e rest ih =>
      intro st h he
      exact ih _ (denseRncOk_csStep hzero h (he e List.mem_cons_self))
        (fun e' he' => he e' (List.mem_cons_of_mem e he'))

theorem denseRncOk_biFold :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p), DenseRncOk st →
      DenseRncOk (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st) := by
  intro es
  induction es with
  | nil => intro st h; exact h
  | cons e rest ih => intro st h; exact ih _ (denseRncOk_rewriteBiAt h e.1 e.2)

theorem denseRncOk_boolFold :
    ∀ (bits : List VarId) (st : DenseRncState p), DenseRncOk st →
      DenseRncOk (bits.foldl (fun st b => st.pushBool b) st) := by
  intro bits
  induction bits with
  | nil => intro st h; exact h
  | cons b rest ih => intro st h; exact ih _ (denseRncOk_pushBool h b)

/-- The whole write preserves the index invariants. -/
theorem denseRncOk_write {ctx : DenseRncCtx p} {st : DenseRncState p} {bits : List VarId}
    {csEdits : List (DenseRncCsEdit p)} {biEdits : List (Nat × BusInteraction (DenseExpr p))}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) (h : DenseRncOk st)
    (he : ∀ e ∈ csEdits, DenseRncEditOk e) :
    DenseRncOk (denseRncWrite ctx st bits csEdits biEdits) :=
  denseRncOk_domReset (denseRncOk_boolFold bits _
    (denseRncOk_biFold biEdits _ (denseRncOk_csFold hzero csEdits st h he)))

/-- The builder's edits carry the payload the invariants need. -/
theorem denseRncCsEdits_editOk (ctx : DenseRncCtx p) (st : DenseRncState p) (xs : List VarId)
    (cd : DenseRncCand p) : ∀ e ∈ (denseRncCsEdits ctx st xs cd).1, DenseRncEditOk e := by
  rw [csEdits_eq_foldr]
  generalize (denseRncPosList (match st.useCs with | some m => m | none => #[]) xs
    (match st.foldCs with | some s => s | none => ∅).toList) = l
  induction l with
  | nil => intro e he; simp at he
  | cons i rest ih =>
      intro e he
      rw [List.foldr_cons] at he
      cases hc : st.cs[i]? with
      | none => exact ih e (by simpa only [csBody, hc] using he)
      | some c =>
        cases hvs : st.cvs[i]? with
        | none => exact ih e (by simpa only [csBody, hc, hvs] using he)
        | some vs =>
          simp only [csBody, hc, hvs] at he
          split at he
          · rcases List.mem_cons.1 he with rfl | he'
            · trivial
            · exact ih e he'
          · split at he
            · rcases List.mem_cons.1 he with rfl | he'
              · exact ⟨rfl, fun v hv => denseRncFullVars_mem hv⟩
              · exact ih e he'
            · exact ih e he

/-! ### The lazily built indexes are complete

Each builder walks the positions once; the two facts per builder are that it lists what it must and
that it only adds. -/

theorem denseRncUseGo_mono (cs : Array (DenseExpr p)) (cvs : Array (Array VarId)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Array (Array Nat)) (v : VarId) (j : Nat),
      j ∈ denseRncBGet acc v → j ∈ denseRncBGet (denseRncUseGo cs cvs i acc) v := by
  intro n
  induction n with
  | zero =>
      intro i hn acc v j hj
      rw [denseRncUseGo, dif_neg (by omega)]
      exact hj
  | succ n ih =>
      intro i hn acc v j hj
      rw [denseRncUseGo]
      split
      · next hlt =>
          refine ih (i + 1) (by omega) _ v j ?_
          have hfl : (denseRncFullVars cs[i] (cvs.getD i #[])).foldl
              (fun m w => denseRncBAdd m w i) acc
              = (denseRncFullVars cs[i] (cvs.getD i #[])).toList.foldl
                (fun m w => denseRncBAdd m w i) acc := by
            conv_lhs => rw [← Array.toArray_toList (xs := denseRncFullVars cs[i] (cvs.getD i #[]))]
            rw [List.foldl_toArray]
          rw [hfl]
          exact denseRncBFoldL_mono i _ acc v j hj
      · exact hj

theorem denseRncUseGo_complete (cs : Array (DenseExpr p)) (cvs : Array (Array VarId))
    (hcvs : ∀ (k : Nat) (c : DenseExpr p), cs[k]? = some c → cvs[k]? = some (denseRncCapVars c)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Array (Array Nat)) (j : Nat) (c : DenseExpr p),
      i ≤ j → cs[j]? = some c →
      ∀ v ∈ c.vars, j ∈ denseRncBGet (denseRncUseGo cs cvs i acc) v := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j c hij hj v hv
      have hjlt : j < cs.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      omega
  | succ n ih =>
      intro i hn acc j c hij hj v hv
      have hjlt : j < cs.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      rw [denseRncUseGo]
      split
      · next hlt =>
          by_cases heq : i = j
          · subst heq
            have hc : cs[i] = c := by
              rw [Array.getElem?_eq_getElem hlt] at hj
              exact Option.some.inj hj
            refine denseRncUseGo_mono cs cvs (n + 1) (i + 1) (by omega) _ v i ?_
            have hfl : (denseRncFullVars cs[i] (cvs.getD i #[])).foldl
                (fun m w => denseRncBAdd m w i) acc
                = (denseRncFullVars cs[i] (cvs.getD i #[])).toList.foldl
                  (fun m w => denseRncBAdd m w i) acc := by
              conv_lhs =>
                rw [← Array.toArray_toList (xs := denseRncFullVars cs[i] (cvs.getD i #[]))]
              rw [List.foldl_toArray]
            rw [hfl]
            refine denseRncBFoldL_self i _ acc v ?_
            have hcv : cvs.getD i #[] = denseRncCapVars cs[i] := by
              have hh := hcvs i cs[i] (by rw [Array.getElem?_eq_getElem hlt])
              rw [Array.getD_eq_getD_getElem?, hh]
              rfl
            rw [hcv, hc]
            simpa using denseRncFullVars_mem hv
          · exact ih (i + 1) (by omega) _ j c (by omega) hj v hv
      · omega

theorem denseRncUseBisGo_mono (bis : Array (BusInteraction (DenseExpr p))) :
    ∀ (n i : Nat), bis.size - i ≤ n → ∀ (acc : Array (Array Nat)) (v : VarId) (j : Nat),
      j ∈ denseRncBGet acc v → j ∈ denseRncBGet (denseRncUseBisGo bis i acc) v := by
  intro n
  induction n with
  | zero =>
      intro i hn acc v j hj
      rw [denseRncUseBisGo, dif_neg (by omega)]
      exact hj
  | succ n ih =>
      intro i hn acc v j hj
      rw [denseRncUseBisGo]
      split
      · next hlt => exact ih (i + 1) (by omega) _ v j (denseRncBFoldL_mono i _ acc v j hj)
      · exact hj

theorem denseRncUseBisGo_complete (bis : Array (BusInteraction (DenseExpr p))) :
    ∀ (n i : Nat), bis.size - i ≤ n → ∀ (acc : Array (Array Nat)) (j : Nat)
      (bi : BusInteraction (DenseExpr p)), i ≤ j → bis[j]? = some bi →
      ∀ v ∈ denseBIVars bi, j ∈ denseRncBGet (denseRncUseBisGo bis i acc) v := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j bi hij hj v hv
      have hjlt : j < bis.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      omega
  | succ n ih =>
      intro i hn acc j bi hij hj v hv
      have hjlt : j < bis.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      rw [denseRncUseBisGo]
      split
      · next hlt =>
          by_cases heq : i = j
          · subst heq
            have hc : bis[i] = bi := by
              rw [Array.getElem?_eq_getElem hlt] at hj
              exact Option.some.inj hj
            refine denseRncUseBisGo_mono bis (n + 1) (i + 1) (by omega) _ v i ?_
            rw [hc]
            exact denseRncBFoldL_self i _ acc v hv
          · exact ih (i + 1) (by omega) _ j bi (by omega) hj v hv
      · omega

theorem denseRncFoldCsGo_mono (cs : Array (DenseExpr p)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Std.HashSet Nat) (j : Nat), acc.contains j = true →
      (denseRncFoldCsGo cs i acc).contains j = true := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j hj
      rw [denseRncFoldCsGo, dif_neg (by omega)]
      exact hj
  | succ n ih =>
      intro i hn acc j hj
      rw [denseRncFoldCsGo]
      split
      · next hlt =>
          refine ih (i + 1) (by omega) _ j ?_
          split
          · rw [Std.HashSet.contains_insert]; simp [hj]
          · exact hj
      · exact hj

theorem denseRncFoldCsGo_complete (cs : Array (DenseExpr p)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Std.HashSet Nat) (j : Nat) (c : DenseExpr p),
      i ≤ j → cs[j]? = some c → denseRncHasFold c = true →
      (denseRncFoldCsGo cs i acc).contains j = true := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j c hij hj _
      have hjlt : j < cs.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      omega
  | succ n ih =>
      intro i hn acc j c hij hj hfd
      have hjlt : j < cs.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      rw [denseRncFoldCsGo]
      split
      · next hlt =>
          by_cases heq : i = j
          · subst heq
            have hc : cs[i] = c := by
              rw [Array.getElem?_eq_getElem hlt] at hj
              exact Option.some.inj hj
            rw [hc, if_pos hfd]
            refine denseRncFoldCsGo_mono cs (n + 1) (i + 1) (by omega) _ i ?_
            rw [Std.HashSet.contains_insert]; simp
          · exact ih (i + 1) (by omega) _ j c (by omega) hj hfd
      · omega

theorem denseRncFoldBisGo_mono (bis : Array (BusInteraction (DenseExpr p))) :
    ∀ (n i : Nat), bis.size - i ≤ n → ∀ (acc : Std.HashSet Nat) (j : Nat), acc.contains j = true →
      (denseRncFoldBisGo bis i acc).contains j = true := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j hj
      rw [denseRncFoldBisGo, dif_neg (by omega)]
      exact hj
  | succ n ih =>
      intro i hn acc j hj
      rw [denseRncFoldBisGo]
      split
      · next hlt =>
          refine ih (i + 1) (by omega) _ j ?_
          split
          · rw [Std.HashSet.contains_insert]; simp [hj]
          · exact hj
      · exact hj

theorem denseRncFoldBisGo_complete (bis : Array (BusInteraction (DenseExpr p))) :
    ∀ (n i : Nat), bis.size - i ≤ n → ∀ (acc : Std.HashSet Nat) (j : Nat)
      (bi : BusInteraction (DenseExpr p)), i ≤ j → bis[j]? = some bi →
      denseRncBiHasFold bi = true → (denseRncFoldBisGo bis i acc).contains j = true := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j bi hij hj _
      have hjlt : j < bis.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      omega
  | succ n ih =>
      intro i hn acc j bi hij hj hfd
      have hjlt : j < bis.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      rw [denseRncFoldBisGo]
      split
      · next hlt =>
          by_cases heq : i = j
          · subst heq
            have hc : bis[i] = bi := by
              rw [Array.getElem?_eq_getElem hlt] at hj
              exact Option.some.inj hj
            rw [hc, if_pos hfd]
            refine denseRncFoldBisGo_mono bis (n + 1) (i + 1) (by omega) _ i ?_
            rw [Std.HashSet.contains_insert]; simp
          · exact ih (i + 1) (by omega) _ j bi (by omega) hj hfd
      · omega

theorem denseRncOk_ensureUse {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk (denseRncEnsureUse st) ∧ (denseRncEnsureUse st).useCs.isSome = true := by
  unfold denseRncEnsureUse
  split
  · next hsome => exact ⟨h, by rw [hsome]; rfl⟩
  · refine ⟨⟨h.sizes, h.cvs, h.anchor, ⟨?_, h.use.2⟩, h.bus⟩, rfl⟩
    intro m hm j c hj v hv
    have hm' : m = denseRncUseGo st.cs st.cvs 0 (Array.replicate st.nVar #[]) :=
      Option.some.inj hm.symm ▸ rfl
    subst hm'
    exact denseRncUseGo_complete st.cs st.cvs h.cvs st.cs.size 0 (by omega) _ j c
      (Nat.zero_le j) hj v hv

theorem denseRncOk_ensureUseBis {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk (denseRncEnsureUseBis st) ∧ (denseRncEnsureUseBis st).useBis.isSome = true := by
  unfold denseRncEnsureUseBis
  split
  · next hsome => exact ⟨h, by rw [hsome]; rfl⟩
  · refine ⟨⟨h.sizes, h.cvs, h.anchor, h.use, ⟨?_, h.bus.2⟩⟩, rfl⟩
    intro m hm j bi hj v hv
    have hm' : m = denseRncUseBisGo st.bis 0 (Array.replicate st.nVar #[]) :=
      Option.some.inj hm.symm ▸ rfl
    subst hm'
    exact denseRncUseBisGo_complete st.bis st.bis.size 0 (by omega) _ j bi (Nat.zero_le j) hj v hv

theorem denseRncOk_ensureFoldCs {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk (denseRncEnsureFoldCs st) ∧ (denseRncEnsureFoldCs st).foldCs.isSome = true := by
  unfold denseRncEnsureFoldCs
  split
  · next hsome => exact ⟨h, by rw [hsome]; rfl⟩
  · refine ⟨⟨h.sizes, h.cvs, h.anchor, ⟨h.use.1, ?_⟩, h.bus⟩, rfl⟩
    intro sf hsf j c hj hfd
    have hsf' : sf = denseRncFoldCsGo st.cs 0 ∅ := Option.some.inj hsf.symm ▸ rfl
    subst hsf'
    exact denseRncFoldCsGo_complete st.cs st.cs.size 0 (by omega) ∅ j c (Nat.zero_le j) hj hfd

theorem denseRncOk_ensureFoldBis {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk (denseRncEnsureFoldBis st) ∧ (denseRncEnsureFoldBis st).foldBis.isSome = true := by
  unfold denseRncEnsureFoldBis
  split
  · next hsome => exact ⟨h, by rw [hsome]; rfl⟩
  · refine ⟨⟨h.sizes, h.cvs, h.anchor, h.use, ⟨h.bus.1, ?_⟩⟩, rfl⟩
    intro sf hsf j bi hj hfd
    have hsf' : sf = denseRncFoldBisGo st.bis 0 ∅ := Option.some.inj hsf.symm ▸ rfl
    subst hsf'
    exact denseRncFoldBisGo_complete st.bis st.bis.size 0 (by omega) ∅ j bi (Nat.zero_le j) hj hfd

/-! ### The seed state

`denseRncScan` mirrors `cvs` on `cs` by construction, and the anchor builder lists every position
under its first variable. The remaining indexes start as `none`, so their invariants hold
vacuously. -/

theorem denseRncMark_size (m : Array Bool) (v : VarId) : (denseRncMark m v).size = m.size :=
  Array.size_setIfInBounds ..

theorem denseRncMark_mono {m : Array Bool} {v w : VarId} (h : denseRncGetB m v = true) :
    denseRncGetB (denseRncMark m w) v = true := by
  unfold denseRncGetB denseRncMark at *
  rw [Array.getD_eq_getD_getElem?] at h ⊢
  by_cases hvw : w.index = v.index
  · rw [hvw, Array.getElem?_setIfInBounds_self_of_lt (by
      by_contra hcon
      rw [Array.getElem?_eq_none (by omega)] at h
      exact absurd h (by simp))]
    rfl
  · rw [Array.getElem?_setIfInBounds_ne hvw]; exact h

theorem denseRncMark_self {m : Array Bool} {v : VarId} (h : v.index < m.size) :
    denseRncGetB (denseRncMark m v) v = true := by
  unfold denseRncGetB denseRncMark
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h]
  rfl

theorem denseRncFoldVars_size (c : DenseExpr p) :
    ∀ (m : Array Bool), (c.foldVars (fun m v => denseRncMark m v) m).size = m.size := by
  induction c with
  | const n => intro m; rfl
  | var y => intro m; exact denseRncMark_size m y
  | add a b iha ihb | mul a b iha ihb =>
      intro m
      show (b.foldVars _ (a.foldVars _ m)).size = m.size
      rw [ihb, iha]

theorem denseRncFoldVars_mono (c : DenseExpr p) :
    ∀ (m : Array Bool) (v : VarId), denseRncGetB m v = true →
      denseRncGetB (c.foldVars (fun m w => denseRncMark m w) m) v = true := by
  induction c with
  | const n => intro m v h; exact h
  | var y => intro m v h; exact denseRncMark_mono h
  | add a b iha ihb | mul a b iha ihb =>
      intro m v h
      show denseRncGetB (b.foldVars _ (a.foldVars _ m)) v = true
      exact ihb _ v (iha _ v h)

theorem denseRncFoldVars_mark (c : DenseExpr p) :
    ∀ (m : Array Bool) (v : VarId), v ∈ c.vars → v.index < m.size →
      denseRncGetB (c.foldVars (fun m w => denseRncMark m w) m) v = true := by
  induction c with
  | const n => intro m v hv; simp [DenseExpr.vars] at hv
  | var y =>
      intro m v hv hlt
      have : v = y := by simpa [DenseExpr.vars] using hv
      subst this
      exact denseRncMark_self hlt
  | add a b iha ihb | mul a b iha ihb =>
      intro m v hv hlt
      show denseRncGetB (b.foldVars _ (a.foldVars _ m)) v = true
      rcases List.mem_append.1 (by simpa [DenseExpr.vars] using hv) with h | h
      · exact denseRncFoldVars_mono b _ v (iha _ v h hlt)
      · exact ihb _ v h (by rw [denseRncFoldVars_size a m]; exact hlt)

theorem denseRncSeenCsGo_size (cs : Array (DenseExpr p)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Array Bool),
      (denseRncSeenCsGo cs i acc).size = acc.size := by
  intro n
  induction n with
  | zero => intro i hn acc; rw [denseRncSeenCsGo, dif_neg (by omega)]
  | succ n ih =>
      intro i hn acc
      rw [denseRncSeenCsGo]
      split
      · next hlt => rw [ih (i + 1) (by omega), denseRncFoldVars_size]
      · rfl

theorem denseRncSeenCsGo_mono (cs : Array (DenseExpr p)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Array Bool) (v : VarId), denseRncGetB acc v = true →
      denseRncGetB (denseRncSeenCsGo cs i acc) v = true := by
  intro n
  induction n with
  | zero => intro i hn acc v h; rw [denseRncSeenCsGo, dif_neg (by omega)]; exact h
  | succ n ih =>
      intro i hn acc v h
      rw [denseRncSeenCsGo]
      split
      · next hlt => exact ih (i + 1) (by omega) _ v (denseRncFoldVars_mono _ acc v h)
      · exact h

theorem denseRncSeenCsGo_mark (cs : Array (DenseExpr p)) :
    ∀ (n i : Nat), cs.size - i ≤ n → ∀ (acc : Array Bool) (j : Nat) (c : DenseExpr p),
      i ≤ j → cs[j]? = some c → ∀ v ∈ c.vars, v.index < acc.size →
      denseRncGetB (denseRncSeenCsGo cs i acc) v = true := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j c hij hj v hv _
      have hjlt : j < cs.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      omega
  | succ n ih =>
      intro i hn acc j c hij hj v hv hlt
      have hjlt : j < cs.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      rw [denseRncSeenCsGo]
      split
      · next hltc =>
          by_cases heq : i = j
          · subst heq
            have hc : cs[i] = c := by
              rw [Array.getElem?_eq_getElem hltc] at hj
              exact Option.some.inj hj
            refine denseRncSeenCsGo_mono cs (n + 1) (i + 1) (by omega) _ v ?_
            rw [hc]
            exact denseRncFoldVars_mark c acc v hv hlt
          · refine ih (i + 1) (by omega) _ j c (by omega) hj v hv ?_
            rw [denseRncFoldVars_size]
            exact hlt
      · omega

theorem denseRncSeenBisGo_mono (bis : Array (BusInteraction (DenseExpr p))) :
    ∀ (n i : Nat), bis.size - i ≤ n → ∀ (acc : Array Bool) (v : VarId), denseRncGetB acc v = true →
      denseRncGetB (denseRncSeenBisGo bis i acc) v = true := by
  intro n
  induction n with
  | zero => intro i hn acc v h; rw [denseRncSeenBisGo, dif_neg (by omega)]; exact h
  | succ n ih =>
      intro i hn acc v h
      rw [denseRncSeenBisGo]
      split
      · next hlt =>
          refine ih (i + 1) (by omega) _ v ?_
          have hstep : ∀ (l : List (DenseExpr p)) (m : Array Bool), denseRncGetB m v = true →
              denseRncGetB (l.foldl (fun m e => e.foldVars (fun m w => denseRncMark m w) m) m) v
                = true := by
            intro l
            induction l with
            | nil => intro m hm; exact hm
            | cons e rest ihl => intro m hm; exact ihl _ (denseRncFoldVars_mono e m v hm)
          exact hstep _ _ (denseRncFoldVars_mono _ acc v h)
      · exact h

/-- Every variable of the system is either an entry variable (bucketed by index) or a minted bit. -/
def DenseRncNVarOk (st : DenseRncState p) : Prop :=
  ∀ v ∈ (denseRncView st).occ, v.index < st.nVar ∨ st.minted.contains v = true

theorem denseRncPayloadFold_mark (l : List (DenseExpr p)) :
    ∀ (m : Array Bool) (v : VarId) (e : DenseExpr p), e ∈ l → v ∈ e.vars → v.index < m.size →
      denseRncGetB (l.foldl (fun m e => e.foldVars (fun m w => denseRncMark m w) m) m) v = true := by
  induction l with
  | nil => intro m v e he; simp at he
  | cons e0 rest ih =>
      intro m v e he hv hlt
      have hstep : ∀ (l' : List (DenseExpr p)) (m' : Array Bool), denseRncGetB m' v = true →
          denseRncGetB (l'.foldl (fun m e => e.foldVars (fun m w => denseRncMark m w) m) m') v
            = true := by
        intro l'
        induction l' with
        | nil => intro m' hm'; exact hm'
        | cons e1 rest1 ihl => intro m' hm'; exact ihl _ (denseRncFoldVars_mono e1 m' v hm')
      rcases List.mem_cons.1 he with rfl | he'
      · exact hstep rest _ (denseRncFoldVars_mark e m v hv hlt)
      · exact ih _ v e he' hv (by rw [denseRncFoldVars_size]; exact hlt)

theorem denseRncSeenBisGo_mark (bis : Array (BusInteraction (DenseExpr p))) :
    ∀ (n i : Nat), bis.size - i ≤ n → ∀ (acc : Array Bool) (j : Nat)
      (bi : BusInteraction (DenseExpr p)), i ≤ j → bis[j]? = some bi →
      ∀ v ∈ denseBIVars bi, v.index < acc.size →
      denseRncGetB (denseRncSeenBisGo bis i acc) v = true := by
  intro n
  induction n with
  | zero =>
      intro i hn acc j bi hij hj v hv _
      have hjlt : j < bis.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      omega
  | succ n ih =>
      intro i hn acc j bi hij hj v hv hlt
      have hjlt : j < bis.size := by
        by_contra hcon
        rw [Array.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      have hsz : ∀ (l' : List (DenseExpr p)) (m' : Array Bool),
          (l'.foldl (fun m e => e.foldVars (fun m w => denseRncMark m w) m) m').size = m'.size := by
        intro l'
        induction l' with
        | nil => intro m'; rfl
        | cons e1 rest1 ihl => intro m'; rw [List.foldl_cons, ihl, denseRncFoldVars_size]
      rw [denseRncSeenBisGo]
      split
      · next hltb =>
          by_cases heq : i = j
          · subst heq
            have hc : bis[i] = bi := by
              rw [Array.getElem?_eq_getElem hltb] at hj
              exact Option.some.inj hj
            refine denseRncSeenBisGo_mono bis (n + 1) (i + 1) (by omega) _ v ?_
            rw [hc]
            rw [denseBIVars, List.mem_append] at hv
            rcases hv with h | h
            · have hstep : ∀ (l' : List (DenseExpr p)) (m' : Array Bool),
                  denseRncGetB m' v = true →
                  denseRncGetB (l'.foldl
                    (fun m e => e.foldVars (fun m w => denseRncMark m w) m) m') v = true := by
                intro l'
                induction l' with
                | nil => intro m' hm'; exact hm'
                | cons e1 rest1 ihl => intro m' hm'; exact ihl _ (denseRncFoldVars_mono e1 m' v hm')
              exact hstep _ _ (denseRncFoldVars_mark bi.multiplicity acc v h hlt)
            · obtain ⟨e, he, hve⟩ := List.mem_flatMap.1 h
              exact denseRncPayloadFold_mark bi.payload _ v e he hve
                (by rw [denseRncFoldVars_size]; exact hlt)
          · refine ih (i + 1) (by omega) _ j bi (by omega) hj v hv ?_
            rw [hsz, denseRncFoldVars_size]
            exact hlt
      · omega

/-- `denseRncEnsureSeen` establishes the freshness invariant. -/
theorem denseRncVarsOk_ensureSeen {st : DenseRncState p} (hvo : DenseRncVarsOk st)
    (hnv : DenseRncNVarOk st) : DenseRncVarsOk (denseRncEnsureSeen st) := by
  unfold denseRncEnsureSeen
  split
  · exact hvo
  · next hnone =>
    intro v hv
    have hview : (denseRncView { st with varSeen := some (denseRncSeenBisGo st.bis 0
        (denseRncSeenCsGo st.cs 0 (Array.replicate st.nVar false))) }) = denseRncView st := rfl
    rw [hview] at hv
    rcases hnv v hv with hlt | hmint
    · refine Bool.or_eq_true_iff.2 (Or.inl ?_)
      show denseRncGetB (denseRncSeenBisGo st.bis 0
        (denseRncSeenCsGo st.cs 0 (Array.replicate st.nVar false))) v = true
      have hszcs : (denseRncSeenCsGo st.cs 0 (Array.replicate st.nVar false)).size = st.nVar := by
        rw [denseRncSeenCsGo_size st.cs st.cs.size 0 (by omega), Array.size_replicate]
      rw [DenseConstraintSystem.occ, List.mem_append] at hv
      rcases hv with hc | hb
      · obtain ⟨c, hcmem, hvc⟩ := List.mem_flatMap.1 hc
        have hcs : c ∈ st.cs := by
          have hmem : c ∈ (st.cs.filter (fun c => !denseIsZero c)) := by
            rw [Array.mem_def]
            simpa [denseRncView] using hcmem
          exact Array.mem_of_mem_filter hmem
        obtain ⟨jc, hjc⟩ := Array.mem_iff_getElem?.1 hcs
        refine denseRncSeenBisGo_mono st.bis st.bis.size 0 (by omega) _ v ?_
        exact denseRncSeenCsGo_mark st.cs st.cs.size 0 (by omega) _ jc c (Nat.zero_le jc) hjc v hvc
          (by rw [Array.size_replicate]; exact hlt)
      · obtain ⟨bi, hbimem, hvb⟩ := List.mem_flatMap.1 hb
        have hbis : bi ∈ st.bis := by
          rw [Array.mem_def]
          simpa [denseRncView] using hbimem
        obtain ⟨jb, hjb⟩ := Array.mem_iff_getElem?.1 hbis
        exact denseRncSeenBisGo_mark st.bis st.bis.size 0 (by omega) _ jb bi (Nat.zero_le jb) hjb
          v hvb (by rw [hszcs]; exact hlt)
    · exact Bool.or_eq_true_iff.2 (Or.inr hmint)

theorem denseRncScanFold (l : List (DenseExpr p)) :
    ∀ (a : Array (Array VarId)) (n : Nat),
      (l.foldl (fun (acc : Array (Array VarId) × Nat) c =>
        (acc.1.push (denseRncCapVars c), if denseIsZero c then acc.2 else acc.2 + 1)) (a, n)).1
        = a ++ (l.map denseRncCapVars).toArray := by
  induction l with
  | nil => intro a n; simp
  | cons c rest ih =>
      intro a n
      rw [List.foldl_cons, ih, List.map_cons]
      show a.push (denseRncCapVars c) ++ _ = _
      simp

theorem denseRncScan_cvs (cs : Array (DenseExpr p)) :
    (denseRncScan cs).1 = (cs.toList.map denseRncCapVars).toArray := by
  unfold denseRncScan
  conv_lhs => rw [← Array.toArray_toList (xs := cs)]
  rw [List.foldl_toArray, denseRncScanFold]
  simp

theorem denseRncScan_cvsOk (cs : Array (DenseExpr p)) :
    (∀ (i : Nat) (c : DenseExpr p), cs[i]? = some c →
      ((denseRncScan cs).1)[i]? = some (denseRncCapVars c)) ∧
    (denseRncScan cs).1.size = cs.size := by
  rw [denseRncScan_cvs]
  refine ⟨fun i c hi => ?_, by simp⟩
  rw [← Array.getElem?_toList, List.toList_toArray, List.getElem?_map, Array.getElem?_toList, hi]
  rfl

theorem denseRncAnchorFold_complete :
    ∀ (l : List (DenseExpr p × Nat)) (c : DenseExpr p) (i : Nat), (c, i) ∈ l →
      ∀ v ∈ denseRncAnchorVars c,
        i ∈ (l.foldr (fun ai idx => denseRncAnchorAdd idx (denseRncAnchorVars ai.1) ai.2)
          ⟨∅, []⟩).buckets.getD v [] := by
  intro l
  induction l with
  | nil => intro c i hi; simp at hi
  | cons ai rest ih =>
      intro c i hi v hv
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hi with heq | hmem
      · rw [← heq]
        cases hav : denseRncAnchorVars c with
        | nil => rw [hav] at hv; simp at hv
        | cons w tail =>
            have hvw : v = w := by
              rw [hav] at hv
              rcases List.mem_cons.1 hv with h1 | h1
              · exact h1
              · exact absurd h1 (by
                  unfold denseRncAnchorVars at hav
                  split at hav <;> simp_all)
            subst hvw
            exact denseRncAnchorAdd_self _ v tail i
      · exact denseRncAnchorAdd_mono _ _ _ i v (ih c i hmem v hv)

theorem denseRncAnchorBuild_complete (cs : List (DenseExpr p)) :
    ∀ (i : Nat) (c : DenseExpr p), cs[i]? = some c →
      ∀ v ∈ denseRncAnchorVars c, i ∈ (denseRncAnchorBuild cs).buckets.getD v [] := by
  intro i c hi v hv
  refine denseRncAnchorFold_complete cs.zipIdx c i ?_ v hv
  refine List.mem_of_getElem? (i := i) ?_
  rw [List.getElem?_zipIdx, hi]
  simp

theorem denseRncWrite_occ_sub {ctx : DenseRncCtx p} {st : DenseRncState p} {xs : List VarId}
    {cd : DenseRncCand p} {m mB : Array (Array Nat)} {sf sfB : Std.HashSet Nat}
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p))
    (hpatts : cd.patts.get = denseAssignments (denseBitBox cd.bits))
    (hcvs : DenseRncCvsOk st) (huse : DenseRncUseOk st) (hbus : DenseRncBusOk st)
    (hm : st.useCs = some m) (hs : st.foldCs = some sf)
    (hmB : st.useBis = some mB) (hsB : st.foldBis = some sfB)
    (hσ : ∀ y ∈ xs, ∀ v ∈ ((DenseExpr.var y).substF (denseGroupSubst xs cd.hm.get)).vars,
      v ∈ cd.bits) :
    ∀ v ∈ (denseRncView (denseRncWrite ctx st cd.bits (denseRncCsEdits ctx st xs cd).1
        (denseRncBiEdits ctx st xs cd).1)).occ,
      v ∈ (denseRncView st).occ ∨ v ∈ cd.bits := by
  intro v hv
  rw [denseRncWrite_view hzero hpatts hcvs huse hbus hm hs hmB hsB] at hv
  exact denseReencodeOut_vars_subset _ xs cd.bits cd.hm.get hσ v
    (denseFilterConstraints_occ_sub _ _ v hv)

/-! ### The bits' derivations

The engine reads each group variable's image at a pattern from the shared table; `denseBitCM`
re-evaluates the interpolation polynomial per (bit, pattern, variable). Same tree. -/

theorem denseRncMatchCM_eq (img : Array (ZMod p)) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) :
    ∀ (ys : List VarId) (j : Nat),
      (∀ (k : Nat) (y : VarId), ys[k]? = some y → img.getD (j + k) (zmodZeroP p) = imgFn y) →
      denseRncMatchCM img thenM elseM ys j = denseMatchCM ys imgFn thenM elseM := by
  intro ys
  induction ys with
  | nil => intro j _; rfl
  | cons y rest ih =>
      intro j hval
      have hy : img.getD j (zmodZeroP p) = imgFn y := by
        have h0 := hval 0 y rfl
        simpa using h0
      rw [denseRncMatchCM, denseMatchCM, hy, zmodNegP_eq,
        ih (j + 1) (fun k z hz => by
          have h1 := hval (k + 1) z (by simpa using hz)
          rw [show j + 1 + k = j + (k + 1) by omega]
          exact h1)]

theorem denseRncBitCM_eq {ctx : DenseRncCtx p} {cd : DenseRncCand p} {xs : List VarId} {b : VarId}
    (hzero : ctx.ops.zero = (0 : ZMod p))
    (himgs : cd.imgs.get = cd.pattsA.get.map (fun aβ =>
      (xs.toArray).map (fun x => ((cd.hm.get[x]?).getD (.var x)).evalFast (denseEnvOfFast aβ)))) :
    ∀ (n t : Nat), cd.pattsA.get.size - t ≤ n → denseRncBitCMGo ctx cd xs b t
      = denseBitCM (cd.pattsA.get.toList.drop t) xs cd.hm.get b := by
  intro n
  induction n with
  | zero =>
      intro t hn
      rw [denseRncBitCMGo, dif_neg (by omega),
        List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega), denseBitCM, hzero]
  | succ n ih =>
      intro t hn
      rw [denseRncBitCMGo]
      split
      · next hlt =>
          have hlt' : t < cd.pattsA.get.toList.length := by
            rw [Array.length_toList]
            exact hlt
          rw [List.drop_eq_getElem_cons hlt', denseBitCM, ih (t + 1) (by omega)]
          have hpt : cd.pattsA.get.toList[t] = cd.pattsA.get[t] := Array.getElem_toList ..
          rw [hpt]
          have hrow : cd.imgs.get.getD t #[]
              = (xs.toArray).map (fun x =>
                  ((cd.hm.get[x]?).getD (.var x)).evalFast (denseEnvOfFast cd.pattsA.get[t])) := by
            rw [himgs, Array.getD_eq_getD_getElem?, Array.getElem?_map,
              Array.getElem?_eq_getElem hlt]
            rfl
          rw [hrow]
          refine denseRncMatchCM_eq _ _ _ _ xs 0 (fun k y hk => ?_)
          have hklt : k < xs.length := by
            by_contra hcon
            rw [List.getElem?_eq_none (by omega)] at hk
            exact absurd hk (by simp)
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
            Array.getElem?_eq_getElem (by simpa using hklt)]
          have hxk : (xs.toArray)[k] = y := by
            have hg : xs[k]? = some xs[k] := List.getElem?_eq_getElem hklt
            rw [hg] at hk
            have hy : xs[k] = y := Option.some.inj hk
            simpa using hy
          simp only [Nat.zero_add, hxk, denseImgVal, DenseExpr.substF]
          have hσ : denseGroupSubst xs cd.hm.get y = cd.hm.get[y]? := by
            unfold denseGroupSubst
            rw [if_pos (denseContainsFast_of_mem xs y (by
              rw [← hxk]; exact List.getElem_mem (by simpa using hklt)))]
          rw [hσ]
          simp only [Option.map_some, Option.getD_some]
          cases cd.hm.get[y]? <;> rfl
      · next hge =>
          rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega), denseBitCM, hzero]

/-! ### States that differ only in the domain memo

The build touches the memo, never the system; the `ensure*` helpers build one index each. -/

structure DenseRncCore (st st' : DenseRncState p) : Prop where
  cs : st'.cs = st.cs
  cvs : st'.cvs = st.cvs
  bis : st'.bis = st.bis
  anchor : st'.anchor = st.anchor
  useCs : st'.useCs = st.useCs
  useBis : st'.useBis = st.useBis
  foldCs : st'.foldCs = st.foldCs
  foldBis : st'.foldBis = st.foldBis
  varSeen : st'.varSeen = st.varSeen
  minted : st'.minted = st.minted
  nVar : st'.nVar = st.nVar

theorem DenseRncCore.refl (st : DenseRncState p) : DenseRncCore st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem DenseRncCore.trans {st st' st'' : DenseRncState p} (h1 : DenseRncCore st st')
    (h2 : DenseRncCore st' st'') : DenseRncCore st st'' :=
  ⟨h2.cs.trans h1.cs, h2.cvs.trans h1.cvs, h2.bis.trans h1.bis, h2.anchor.trans h1.anchor,
   h2.useCs.trans h1.useCs, h2.useBis.trans h1.useBis, h2.foldCs.trans h1.foldCs,
   h2.foldBis.trans h1.foldBis, h2.varSeen.trans h1.varSeen, h2.minted.trans h1.minted,
   h2.nVar.trans h1.nVar⟩

theorem DenseRncCore.view {st st' : DenseRncState p} (h : DenseRncCore st st') :
    denseRncView st' = denseRncView st := by
  unfold denseRncView; rw [h.cs, h.bis]

theorem DenseRncCore.ok {st st' : DenseRncState p} (h : DenseRncCore st st') (hok : DenseRncOk st) :
    DenseRncOk st' := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [h.cvs, h.cs]; exact hok.sizes
  · intro i c hi; rw [h.cvs]; rw [h.cs] at hi; exact hok.cvs i c hi
  · intro i c hi v hv; rw [h.anchor]; rw [h.cs] at hi; exact hok.anchor i c hi v hv
  · intro m hm i c hi v hv
    rw [h.useCs] at hm; rw [h.cs] at hi
    exact hok.use.1 m hm i c hi v hv
  · intro sf hsf i c hi hfd
    rw [h.foldCs] at hsf; rw [h.cs] at hi
    exact hok.use.2 sf hsf i c hi hfd
  · intro m hm i bi hi v hv
    rw [h.useBis] at hm; rw [h.bis] at hi
    exact hok.bus.1 m hm i bi hi v hv
  · intro sf hsf i bi hi hfd
    rw [h.foldBis] at hsf; rw [h.bis] at hi
    exact hok.bus.2 sf hsf i bi hi hfd

/-- The weaker relation the `ensure*` helpers satisfy: they build indexes, but the system, the
    freshness data and the index-array size are untouched. -/
structure DenseRncSysSame (st st' : DenseRncState p) : Prop where
  cs : st'.cs = st.cs
  bis : st'.bis = st.bis
  anchor : st'.anchor = st.anchor
  varSeen : st'.varSeen = st.varSeen
  minted : st'.minted = st.minted
  nVar : st'.nVar = st.nVar

theorem DenseRncCore.sysSame {st st' : DenseRncState p} (h : DenseRncCore st st') :
    DenseRncSysSame st st' := ⟨h.cs, h.bis, h.anchor, h.varSeen, h.minted, h.nVar⟩

theorem DenseRncSysSame.view {st st' : DenseRncState p} (h : DenseRncSysSame st st') :
    denseRncView st' = denseRncView st := by unfold denseRncView; rw [h.cs, h.bis]

theorem DenseRncSysSame.varsOk {st st' : DenseRncState p} (h : DenseRncSysSame st st')
    (hv : DenseRncVarsOk st) : DenseRncVarsOk st' := by
  intro v hvm
  show ((match st'.varSeen with | some m => denseRncGetB m v | none => true)
    || st'.minted.contains v) = true
  rw [h.varSeen, h.minted]
  exact hv v (by rwa [h.view] at hvm)

theorem DenseRncSysSame.nVarOk {st st' : DenseRncState p} (h : DenseRncSysSame st st')
    (hn : DenseRncNVarOk st) : DenseRncNVarOk st' := by
  intro v hvm
  rw [h.minted, h.nVar]
  exact hn v (by rwa [h.view] at hvm)

theorem denseRncCore_setDom (st : DenseRncState p) (v : VarId)
    (r : Option (Nat × List (ZMod p))) : DenseRncCore st (st.setDom v r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The bundle of facts the step threads about a state that only had indexes built. -/
structure DenseRncFacts (st0 st : DenseRncState p) : Prop where
  view : denseRncView st = denseRncView st0
  ok : DenseRncOk st
  vo : DenseRncVarsOk st
  nv : DenseRncNVarOk st

theorem denseRncCore_domOf (ops : DenseZModOps p) (st : DenseRncState p) (v : VarId) :
    DenseRncCore st (denseRncDomOf ops st v).2 := by
  unfold denseRncDomOf
  split
  · exact DenseRncCore.refl st
  · exact denseRncCore_setDom st v _

theorem denseRncCore_doms (ops : DenseZModOps p) :
    ∀ (ys : List VarId) (st : DenseRncState p) (acc : Array (Array (ZMod p))),
      DenseRncCore st (denseRncDoms ops st ys acc).2 := by
  intro ys
  induction ys with
  | nil => intro st acc; exact DenseRncCore.refl st
  | cons y rest ih =>
      intro st acc
      rw [denseRncDoms]
      split
      · next ds st' hd =>
          have h1 : DenseRncCore st st' := by
            have hh := denseRncCore_domOf ops st y
            rw [hd] at hh
            exact hh
          exact h1.trans (ih st' _)
      · next st' hd =>
          have hh := denseRncCore_domOf ops st y
          rw [hd] at hh
          exact hh

theorem denseRncSysSame_ensureUse (st : DenseRncState p) :
    DenseRncSysSame st (denseRncEnsureUse st) := by
  unfold denseRncEnsureUse; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem denseRncSysSame_ensureUseBis (st : DenseRncState p) :
    DenseRncSysSame st (denseRncEnsureUseBis st) := by
  unfold denseRncEnsureUseBis; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem denseRncSysSame_ensureFoldCs (st : DenseRncState p) :
    DenseRncSysSame st (denseRncEnsureFoldCs st) := by
  unfold denseRncEnsureFoldCs; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem denseRncSysSame_ensureFoldBis (st : DenseRncState p) :
    DenseRncSysSame st (denseRncEnsureFoldBis st) := by
  unfold denseRncEnsureFoldBis; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem denseRncSysSame_ensureSeen (st : DenseRncState p) :
    (denseRncEnsureSeen st).cs = st.cs ∧ (denseRncEnsureSeen st).bis = st.bis ∧
    (denseRncEnsureSeen st).anchor = st.anchor ∧ (denseRncEnsureSeen st).minted = st.minted ∧
    (denseRncEnsureSeen st).nVar = st.nVar := by
  unfold denseRncEnsureSeen; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem denseRncEnsureUseBis_useCs (st : DenseRncState p) :
    (denseRncEnsureUseBis st).useCs = st.useCs := by
  unfold denseRncEnsureUseBis; split <;> rfl

theorem denseRncEnsureFoldCs_useCs (st : DenseRncState p) :
    (denseRncEnsureFoldCs st).useCs = st.useCs := by
  unfold denseRncEnsureFoldCs; split <;> rfl

theorem denseRncEnsureFoldCs_useBis (st : DenseRncState p) :
    (denseRncEnsureFoldCs st).useBis = st.useBis := by
  unfold denseRncEnsureFoldCs; split <;> rfl

theorem denseRncEnsureFoldBis_useCs (st : DenseRncState p) :
    (denseRncEnsureFoldBis st).useCs = st.useCs := by
  unfold denseRncEnsureFoldBis; split <;> rfl

theorem denseRncEnsureFoldBis_useBis (st : DenseRncState p) :
    (denseRncEnsureFoldBis st).useBis = st.useBis := by
  unfold denseRncEnsureFoldBis; split <;> rfl

theorem denseRncEnsureFoldBis_foldCs (st : DenseRncState p) :
    (denseRncEnsureFoldBis st).foldCs = st.foldCs := by
  unfold denseRncEnsureFoldBis; split <;> rfl

theorem denseRncEnsureSeen_useCs (st : DenseRncState p) :
    (denseRncEnsureSeen st).useCs = st.useCs := by
  unfold denseRncEnsureSeen; split <;> rfl

theorem denseRncEnsureSeen_useBis (st : DenseRncState p) :
    (denseRncEnsureSeen st).useBis = st.useBis := by
  unfold denseRncEnsureSeen; split <;> rfl

theorem denseRncEnsureSeen_view (st : DenseRncState p) :
    denseRncView (denseRncEnsureSeen st) = denseRncView st := by
  unfold denseRncView
  obtain ⟨h1, h2, _, _, _⟩ := denseRncSysSame_ensureSeen st
  rw [h1, h2]

theorem denseRncEnsureSeen_nVarOk {st : DenseRncState p} (hn : DenseRncNVarOk st) :
    DenseRncNVarOk (denseRncEnsureSeen st) := by
  intro v hvm
  obtain ⟨_, _, _, h3, h4⟩ := denseRncSysSame_ensureSeen st
  rw [h3, h4]
  exact hn v (by rwa [denseRncEnsureSeen_view] at hvm)

theorem denseRncOk_ensureSeen {st : DenseRncState p} (h : DenseRncOk st) :
    DenseRncOk (denseRncEnsureSeen st) := by
  unfold denseRncEnsureSeen
  split
  · exact h
  · exact ⟨h.sizes, h.cvs, h.anchor, h.use, h.bus⟩

/-! ### What the candidate builder guarantees -/

theorem denseRncBuild_state (ctx : DenseRncCtx p) (reg : VarRegistry) (st : DenseRncState p)
    (xs : List VarId) (fb : String) :
    (denseRncBuild ctx reg st xs fb).2.2 = (denseRncDoms ctx.ops st xs #[]).2 := by
  unfold denseRncBuild
  split
  · next h => rw [h]
  · next h => rw [h]; split <;> rfl

theorem denseRncBuild_core (ctx : DenseRncCtx p) (reg : VarRegistry) (st : DenseRncState p)
    (xs : List VarId) (fb : String) : DenseRncCore st (denseRncBuild ctx reg st xs fb).2.2 := by
  rw [denseRncBuild_state]
  exact denseRncCore_doms ctx.ops xs st #[]

theorem denseRncBuildCand_spec (ctx : DenseRncCtx p) (reg : VarRegistry) (st : DenseRncState p)
    (planned : List (Nat × DenseExpr p)) (doms : Array (Array (ZMod p))) (xs : List VarId)
    (fb : String) :
    reg.Extends (denseRncBuildCand ctx reg st planned doms xs fb).1
    ∧ (∀ i, (denseRncBuildCand ctx reg st planned doms xs fb).1.isInput i = reg.isInput i)
    ∧ ∀ cd, (denseRncBuildCand ctx reg st planned doms xs fb).2 = some cd →
        cd.es = planned.map Prod.snd
        ∧ cd.patts.get = denseAssignments (denseBitBox cd.bits)
        ∧ cd.pattsA.get = cd.patts.get.toArray
        ∧ cd.imgs.get = cd.pattsA.get.map (fun aβ =>
            (xs.toArray).map (fun x => ((cd.hm.get[x]?).getD (.var x)).evalFast
              (denseEnvOfFast aβ)))
        ∧ (∀ b ∈ cd.bits, (denseRncBuildCand ctx reg st planned doms xs fb).1.Valid b) := by
  fun_cases denseRncBuildCand ctx reg st planned doms xs fb <;>
    first
      | exact ⟨VarRegistry.Extends.refl reg, fun _ => rfl, fun cd hcd => absurd hcd (by simp)⟩
      | refine ⟨(denseRegisterBits_props reg fb _).1,
          (denseRegisterBits_props reg fb _).2.1, fun cd hcd => ?_⟩
  have hcd' := Option.some.inj hcd
  subst hcd'
  exact ⟨rfl, rfl, rfl, rfl, (denseRegisterBits_props reg fb _).2.2⟩

theorem denseRncBuild_spec (ctx : DenseRncCtx p) (reg : VarRegistry) (st : DenseRncState p)
    (xs : List VarId) (fb : String) :
    reg.Extends (denseRncBuild ctx reg st xs fb).1
    ∧ (∀ i, (denseRncBuild ctx reg st xs fb).1.isInput i = reg.isInput i)
    ∧ ∀ cd, (denseRncBuild ctx reg st xs fb).2.1 = some cd →
        cd.es = (denseCoveredIdxPos st.anchor st.cs xs).map Prod.snd
        ∧ cd.patts.get = denseAssignments (denseBitBox cd.bits)
        ∧ cd.pattsA.get = cd.patts.get.toArray
        ∧ cd.imgs.get = cd.pattsA.get.map (fun aβ =>
            (xs.toArray).map (fun x => ((cd.hm.get[x]?).getD (.var x)).evalFast
              (denseEnvOfFast aβ)))
        ∧ (∀ b ∈ cd.bits, (denseRncBuild ctx reg st xs fb).1.Valid b) := by
  unfold denseRncBuild
  split
  · exact ⟨VarRegistry.Extends.refl reg, fun _ => rfl, fun cd hcd => absurd hcd (by simp)⟩
  · next doms st' hd =>
      split
      · exact ⟨VarRegistry.Extends.refl reg, fun _ => rfl, fun cd hcd => absurd hcd (by simp)⟩
      · obtain ⟨hext, hii, hcd⟩ := denseRncBuildCand_spec ctx reg st'
          (denseCoveredIdxPos st'.anchor st'.cs xs) doms xs fb
        have hcore := denseRncCore_doms ctx.ops xs st #[]
        rw [hd] at hcore
        refine ⟨hext, hii, fun cd hc => ?_⟩
        obtain ⟨h1, h2, h3, h4, h5⟩ := hcd cd hc
        rw [hcore.anchor, hcore.cs] at h1
        exact ⟨h1, h2, h3, h4, h5⟩

/-! ### The write's freshness fields

`varSeen` and the index-array size are untouched; `minted` gains exactly the new bits. -/

theorem denseRncCsFold_varSeen (ctx : DenseRncCtx p) :
    ∀ (es : List (DenseRncCsEdit p)) (st : DenseRncState p),
      (es.foldl (denseRncCsStep ctx) st).varSeen = st.varSeen
      ∧ (es.foldl (denseRncCsStep ctx) st).minted = st.minted
      ∧ (es.foldl (denseRncCsStep ctx) st).nVar = st.nVar := by
  intro es
  induction es with
  | nil => intro st; exact ⟨rfl, rfl, rfl⟩
  | cons e rest ih =>
      intro st
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3⟩ := ih (denseRncCsStep ctx st e)
      refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩ <;> cases e <;> rfl

theorem denseRncBiFold_varSeen :
    ∀ (es : List (Nat × BusInteraction (DenseExpr p))) (st : DenseRncState p),
      (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).varSeen = st.varSeen
      ∧ (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).minted = st.minted
      ∧ (es.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) st).nVar = st.nVar := by
  intro es
  induction es with
  | nil => intro st; exact ⟨rfl, rfl, rfl⟩
  | cons e rest ih =>
      intro st
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3⟩ := ih (st.rewriteBiAt e.1 e.2)
      exact ⟨h1, h2, h3⟩

theorem denseRncBoolFold_fields :
    ∀ (bits : List VarId) (st : DenseRncState p),
      (bits.foldl (fun st b => st.pushBool b) st).varSeen = st.varSeen
      ∧ (bits.foldl (fun st b => st.pushBool b) st).nVar = st.nVar
      ∧ (∀ v, st.minted.contains v = true →
          (bits.foldl (fun st b => st.pushBool b) st).minted.contains v = true)
      ∧ (∀ v ∈ bits, (bits.foldl (fun st b => st.pushBool b) st).minted.contains v = true) := by
  intro bits
  induction bits with
  | nil => intro st; exact ⟨rfl, rfl, fun _ h => h, fun v hv => by simp at hv⟩
  | cons b rest ih =>
      intro st
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := ih (st.pushBool b)
      refine ⟨h1, h2, ?_, ?_⟩
      · intro v hv
        refine h3 v ?_
        show (st.minted.insert b).contains v = true
        rw [Std.HashSet.contains_insert]; simp [hv]
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv'
        · refine h3 v ?_
          show (st.minted.insert v).contains v = true
          rw [Std.HashSet.contains_insert]; simp
        · exact h4 v hv'

theorem denseRncWrite_fields (ctx : DenseRncCtx p) (st : DenseRncState p) (bits : List VarId)
    (csE : List (DenseRncCsEdit p)) (biE : List (Nat × BusInteraction (DenseExpr p))) :
    (denseRncWrite ctx st bits csE biE).varSeen = st.varSeen
    ∧ (denseRncWrite ctx st bits csE biE).nVar = st.nVar
    ∧ (∀ v, st.minted.contains v = true →
        (denseRncWrite ctx st bits csE biE).minted.contains v = true)
    ∧ (∀ v ∈ bits, (denseRncWrite ctx st bits csE biE).minted.contains v = true) := by
  obtain ⟨hc1, hc2, hc3⟩ := denseRncCsFold_varSeen ctx csE st
  obtain ⟨hb1, hb2, hb3⟩ := denseRncBiFold_varSeen biE (csE.foldl (denseRncCsStep ctx) st)
  obtain ⟨hp1, hp2, hp3, hp4⟩ := denseRncBoolFold_fields bits
    (biE.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2) (csE.foldl (denseRncCsStep ctx) st))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((denseRncWrite ctx st bits csE biE)).varSeen
      = (bits.foldl (fun st b => st.pushBool b)
          (biE.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
            (csE.foldl (denseRncCsStep ctx) st))).varSeen from rfl, hp1, hb1, hc1]
  · rw [show ((denseRncWrite ctx st bits csE biE)).nVar
      = (bits.foldl (fun st b => st.pushBool b)
          (biE.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
            (csE.foldl (denseRncCsStep ctx) st))).nVar from rfl, hp2, hb3, hc3]
  · intro v hv
    show (bits.foldl (fun st b => st.pushBool b)
      (biE.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        (csE.foldl (denseRncCsStep ctx) st))).minted.contains v = true
    refine hp3 v ?_
    rw [hb2, hc2]
    exact hv
  · intro v hv
    show (bits.foldl (fun st b => st.pushBool b)
      (biE.foldl (fun st ib => st.rewriteBiAt ib.1 ib.2)
        (csE.foldl (denseRncCsStep ctx) st))).minted.contains v = true
    exact hp4 v hv

theorem denseRncWrite_seen {ctx : DenseRncCtx p} {st : DenseRncState p} {bits : List VarId}
    {csE : List (DenseRncCsEdit p)} {biE : List (Nat × BusInteraction (DenseExpr p))} (v : VarId)
    (h : denseRncSeen st v = true ∨ v ∈ bits) :
    denseRncSeen (denseRncWrite ctx st bits csE biE) v = true := by
  obtain ⟨h1, _, h3, h4⟩ := denseRncWrite_fields ctx st bits csE biE
  unfold denseRncSeen
  rw [h1]
  rcases h with h | h
  · unfold denseRncSeen at h
    rcases Bool.or_eq_true_iff.1 h with h' | h'
    · exact Bool.or_eq_true_iff.2 (Or.inl h')
    · exact Bool.or_eq_true_iff.2 (Or.inr (h3 v h'))
  · exact Bool.or_eq_true_iff.2 (Or.inr (h4 v h))

/-! ### The step

Everything the accept branch needs is in place: the certificate gives the audited
`denseCheckReencode` on the view, the write gives `denseReencodeOut` of that view, and the
derivations are `denseBitCM`'s. The reject branches only ever build indexes. -/

/-- The step's post-condition: the pass-level obligations plus the threaded invariants. -/
def DenseRncPost (bs : BusSemantics p) (reg : VarRegistry) (st : DenseRncState p)
    (r : VarRegistry × DenseRncState p × DenseDerivations p) : Prop :=
  reg.Extends r.1 ∧ (∀ i, r.1.isInput i = reg.isInput i)
  ∧ (denseRncView r.2.1).CoveredBy r.1
  ∧ DenseDerivations.CoveredBy r.1 r.2.2
  ∧ DensePassCorrect r.1.isInput (denseRncView st) (denseRncView r.2.1) r.2.2 bs
  ∧ DenseRncOk r.2.1 ∧ DenseRncVarsOk r.2.1 ∧ DenseRncNVarOk r.2.1

theorem denseRncPost_reject {bs : BusSemantics p} {reg reg' : VarRegistry}
    {st st' : DenseRncState p} (hext : reg.Extends reg')
    (hii : ∀ i, reg'.isInput i = reg.isInput i) (hview : denseRncView st' = denseRncView st)
    (hcov : (denseRncView st).CoveredBy reg) (hok : DenseRncOk st') (hvo : DenseRncVarsOk st')
    (hnv : DenseRncNVarOk st') : DenseRncPost bs reg st (reg', st', []) := by
  refine ⟨hext, hii, ?_, (by intro x hx; cases hx), ?_, hok, hvo, hnv⟩
  · rw [hview]; exact csCoveredBy_mono hext hcov
  · rw [hview]; exact DensePassCorrect.refl reg'.isInput (denseRncView st) bs

/-- The name guard only builds `varSeen`. -/
theorem denseRncNameTaken_props (reg : VarRegistry) (st : DenseRncState p) (fb : String)
    (hok : DenseRncOk st) (hvo : DenseRncVarsOk st) (hnv : DenseRncNVarOk st) :
    denseRncView (denseRncNameTaken reg st fb).2 = denseRncView st
    ∧ DenseRncOk (denseRncNameTaken reg st fb).2
    ∧ DenseRncVarsOk (denseRncNameTaken reg st fb).2
    ∧ DenseRncNVarOk (denseRncNameTaken reg st fb).2 := by
  unfold denseRncNameTaken
  split
  · exact ⟨denseRncEnsureSeen_view st, denseRncOk_ensureSeen hok,
      denseRncVarsOk_ensureSeen hvo hnv, denseRncEnsureSeen_nVarOk hnv⟩
  · exact ⟨rfl, hok, hvo, hnv⟩

theorem denseRncFacts_nameTaken {st0 st : DenseRncState p} (reg : VarRegistry) (fb : String)
    (h : DenseRncFacts st0 st) : DenseRncFacts st0 (denseRncNameTaken reg st fb).2 := by
  obtain ⟨hv1, hok1, hvo1, hnv1⟩ := denseRncNameTaken_props reg st fb h.ok h.vo h.nv
  exact ⟨hv1.trans h.view, hok1, hvo1, hnv1⟩

theorem denseRncFacts_build {st0 st : DenseRncState p} (ctx : DenseRncCtx p) (reg : VarRegistry)
    (xs : List VarId) (fb : String) (h : DenseRncFacts st0 st) :
    DenseRncFacts st0 (denseRncBuild ctx reg st xs fb).2.2 :=
  let hc := denseRncBuild_core ctx reg st xs fb
  ⟨hc.view.trans h.view, hc.ok h.ok, hc.sysSame.varsOk h.vo, hc.sysSame.nVarOk h.nv⟩

theorem denseRncFacts_ensureUse {st0 st : DenseRncState p} (h : DenseRncFacts st0 st) :
    DenseRncFacts st0 (denseRncEnsureUse st) :=
  let hs := denseRncSysSame_ensureUse st
  ⟨hs.view.trans h.view, (denseRncOk_ensureUse h.ok).1, hs.varsOk h.vo, hs.nVarOk h.nv⟩

theorem denseRncFacts_ensureUseBis {st0 st : DenseRncState p} (h : DenseRncFacts st0 st) :
    DenseRncFacts st0 (denseRncEnsureUseBis st) :=
  let hs := denseRncSysSame_ensureUseBis st
  ⟨hs.view.trans h.view, (denseRncOk_ensureUseBis h.ok).1, hs.varsOk h.vo, hs.nVarOk h.nv⟩

theorem denseRncFacts_ensureFoldCs {st0 st : DenseRncState p} (h : DenseRncFacts st0 st) :
    DenseRncFacts st0 (denseRncEnsureFoldCs st) :=
  let hs := denseRncSysSame_ensureFoldCs st
  ⟨hs.view.trans h.view, (denseRncOk_ensureFoldCs h.ok).1, hs.varsOk h.vo, hs.nVarOk h.nv⟩

theorem denseRncFacts_ensureFoldBis {st0 st : DenseRncState p} (h : DenseRncFacts st0 st) :
    DenseRncFacts st0 (denseRncEnsureFoldBis st) :=
  let hs := denseRncSysSame_ensureFoldBis st
  ⟨hs.view.trans h.view, (denseRncOk_ensureFoldBis h.ok).1, hs.varsOk h.vo, hs.nVarOk h.nv⟩

theorem denseRncFacts_ensureSeen {st0 st : DenseRncState p} (h : DenseRncFacts st0 st) :
    DenseRncFacts st0 (denseRncEnsureSeen st) :=
  ⟨(denseRncEnsureSeen_view st).trans h.view, denseRncOk_ensureSeen h.ok,
   denseRncVarsOk_ensureSeen h.vo h.nv, denseRncEnsureSeen_nVarOk h.nv⟩

set_option maxHeartbeats 4000000 in
theorem denseRncStep_correct [Fact p.Prime] (ctx : DenseRncCtx p) (reg : VarRegistry)
    (st : DenseRncState p) (xs : List VarId) (freshBase : String) (bs : BusSemantics p)
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) (hopz : ctx.ops.zero = (0 : ZMod p))
    (hcov : (denseRncView st).CoveredBy reg) (hok : DenseRncOk st) (hvo : DenseRncVarsOk st)
    (hnv : DenseRncNVarOk st) :
    DenseRncPost bs reg st (denseRncStep ctx reg st xs freshBase) := by
  have hF0 : DenseRncFacts st st := ⟨rfl, hok, hvo, hnv⟩
  set st1 := (denseRncNameTaken reg st freshBase).2 with hst1def
  have hF1 : DenseRncFacts st st1 := denseRncFacts_nameTaken reg freshBase hF0
  set rB := denseRncBuild ctx reg st1 xs freshBase with hrB
  obtain ⟨hbext, hbii, hbcd⟩ := denseRncBuild_spec ctx reg st1 xs freshBase
  have hFb : DenseRncFacts st rB.2.2 := denseRncFacts_build ctx reg xs freshBase hF1
  have hF3 : DenseRncFacts st (denseRncEnsureUseBis (denseRncEnsureUse rB.2.2)) :=
    denseRncFacts_ensureUseBis (denseRncFacts_ensureUse hFb)
  have hF4 : DenseRncFacts st
      (denseRncEnsureSeen (denseRncEnsureUseBis (denseRncEnsureUse rB.2.2))) :=
    denseRncFacts_ensureSeen hF3
  have hF5 : DenseRncFacts st (denseRncEnsureFoldBis (denseRncEnsureFoldCs
      (denseRncEnsureSeen (denseRncEnsureUseBis (denseRncEnsureUse rB.2.2))))) :=
    denseRncFacts_ensureFoldBis (denseRncFacts_ensureFoldCs hF4)
  fun_cases denseRncStep ctx reg st xs freshBase <;>
    first
      | exact denseRncPost_reject (VarRegistry.Extends.refl reg) (fun _ => rfl) rfl hcov hok hvo hnv
      | exact denseRncPost_reject (VarRegistry.Extends.refl reg) (fun _ => rfl) hF1.view hcov
          hF1.ok hF1.vo hF1.nv
      | exact denseRncPost_reject hbext hbii hFb.view hcov hFb.ok hFb.vo hFb.nv
      | exact denseRncPost_reject hbext hbii hF3.view hcov hF3.ok hF3.vo hF3.nv
      | exact denseRncPost_reject hbext hbii hF4.view hcov hF4.ok hF4.vo hF4.nv
      | exact denseRncPost_reject hbext hbii hF5.view hcov hF5.ok hF5.vo hF5.nv
      | skip
  -- the accept
  case case11 =>
    rename_i cd hcd _ _ _ _ _ _ _ hcertN _ _ _ _ _
    set st3 := denseRncEnsureUseBis (denseRncEnsureUse rB.2.2) with hst3
    set st4 := denseRncEnsureSeen st3 with hst4
    set st0 := denseRncEnsureFoldBis (denseRncEnsureFoldCs st4) with hst0
    obtain ⟨hes, hpatts, hpattsA, himgs, hbval⟩ := hbcd cd hcd
    have hcert : denseRncCert st4 xs cd = true := by simpa using hcertN
    have hUse : st0.useCs.isSome = true := by
      rw [hst0, denseRncEnsureFoldBis_useCs, denseRncEnsureFoldCs_useCs, hst4,
        denseRncEnsureSeen_useCs, hst3, denseRncEnsureUseBis_useCs]
      exact (denseRncOk_ensureUse hFb.ok).2
    have hUseB : st0.useBis.isSome = true := by
      rw [hst0, denseRncEnsureFoldBis_useBis, denseRncEnsureFoldCs_useBis, hst4,
        denseRncEnsureSeen_useBis]
      exact (denseRncOk_ensureUseBis (denseRncOk_ensureUse hFb.ok).1).2
    have hFold : st0.foldCs.isSome = true := by
      rw [hst0, denseRncEnsureFoldBis_foldCs]
      exact (denseRncOk_ensureFoldCs (denseRncOk_ensureSeen hF3.ok)).2
    have hFoldB : st0.foldBis.isSome = true :=
      (denseRncOk_ensureFoldBis (denseRncOk_ensureFoldCs (denseRncOk_ensureSeen hF3.ok)).1).2
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hUse
    obtain ⟨mB, hmB⟩ := Option.isSome_iff_exists.1 hUseB
    obtain ⟨sf, hsf⟩ := Option.isSome_iff_exists.1 hFold
    obtain ⟨sfB, hsfB⟩ := Option.isSome_iff_exists.1 hFoldB
    have hanchor : st0.anchor = st1.anchor := by
      rw [hst0, (denseRncSysSame_ensureFoldBis _).anchor, (denseRncSysSame_ensureFoldCs _).anchor,
        hst4, (denseRncSysSame_ensureSeen st3).2.2.1, hst3,
        (denseRncSysSame_ensureUseBis _).anchor, (denseRncSysSame_ensureUse _).anchor,
        (denseRncBuild_core ctx reg st1 xs freshBase).anchor]
    have hcs : st0.cs = st1.cs := by
      rw [hst0, (denseRncSysSame_ensureFoldBis _).cs, (denseRncSysSame_ensureFoldCs _).cs,
        hst4, (denseRncSysSame_ensureSeen st3).1, hst3,
        (denseRncSysSame_ensureUseBis _).cs, (denseRncSysSame_ensureUse _).cs,
        (denseRncBuild_core ctx reg st1 xs freshBase).cs]
    have hcert0 : denseRncCert st0 xs cd = true := by
      rw [denseRncCert, Bool.and_eq_true]
      rw [denseRncCert, Bool.and_eq_true] at hcert
      refine ⟨?_, hcert.2⟩
      refine List.all_eq_true.2 (fun b hb => ?_)
      have h4 := List.all_eq_true.mp hcert.1 b hb
      show (!denseRncSeen st0 b) = true
      have hseen : denseRncSeen st0 b = denseRncSeen st4 b := by
        unfold denseRncSeen
        rw [hst0, (denseRncSysSame_ensureFoldBis _).varSeen,
          (denseRncSysSame_ensureFoldCs _).varSeen, (denseRncSysSame_ensureFoldBis _).minted,
          (denseRncSysSame_ensureFoldCs _).minted]
      rw [hseen]
      exact h4
    have hchk : denseCheckReencode (denseRncView st0) xs cd.bits cd.hm.get = true := by
      refine denseRncCert_sound hF5.ok.anchor hF5.vo ?_ hcert0
      rw [hes, hanchor, hcs]
    have hview : denseRncView (denseRncWrite ctx st0 cd.bits
        (denseRncCsEdits ctx st0 xs cd).1 (denseRncBiEdits ctx st0 xs cd).1)
        = (denseReencodeOut (denseRncView st0) xs cd.bits cd.hm.get).filterConstraints
            (fun c => !denseIsZero c) :=
      denseRncWrite_view hzero hpatts hF5.ok.cvs hF5.ok.use hF5.ok.bus hm hsf hmB hsfB
    have hpolyVars := denseCheckReencode_polyVars (denseRncView st0) xs cd.bits cd.hm.get hchk
    have hxsInput : ∀ x ∈ xs, rB.1.isInput x = true := by
      intro x hx
      rw [hbii x]
      have hg : xs.all (fun x => reg.isInput x) = true := by
        simpa using ‹¬(!xs.all fun x => reg.isInput x) = true›
      exact List.all_eq_true.mp hg x hx
    have hxsOcc : ∀ x ∈ xs, x ∈ (denseRncView st0).occ :=
      denseCheckReencode_xsOcc (denseRncView st0) xs cd.bits cd.hm.get hchk
    have hxsBits : ∀ x ∈ xs, x ∉ cd.bits := by
      intro x hx
      have hg : xs.all (fun x => decide (x ∉ cd.bits)) = true := by
        simpa using ‹¬(!xs.all fun x => decide (x ∉ cd.bits)) = true›
      exact of_decide_eq_true (List.all_eq_true.mp hg x hx)
    have hbnInput : ∀ b ∈ cd.bits, rB.1.isInput b = false := by
      intro b hb
      have hg : cd.bits.all (fun b => decide ((rB.1.resolve b).powdrId? = none)) = true := by
        simpa using ‹¬(!cd.bits.all fun b => decide ((rB.1.resolve b).powdrId? = none)) = true›
      have hpd : (rB.1.resolve b).powdrId? = none :=
        of_decide_eq_true (List.all_eq_true.mp hg b hb)
      show (rB.1.resolve b).powdrId?.isSome = false
      rw [hpd]; rfl
    have hcov0 : (denseRncView st0).CoveredBy reg := by rw [hF5.view]; exact hcov
    have hcovOut := csCoveredBy_mono hbext hcov0
    have hxsValid : ∀ x ∈ xs, rB.1.Valid x := fun x hx =>
      hbext.valid (DenseConstraintSystem.occ_valid hcov0 x (hxsOcc x hx))
    have hderiv : (cd.bits.map (fun b => (b, denseRncBitCMGo ctx cd xs b 0)))
        = cd.bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox cd.bits)) xs
            cd.hm.get b)) := by
      refine List.map_congr_left (fun b _ => ?_)
      rw [denseRncBitCM_eq hopz himgs cd.pattsA.get.size 0 (by omega)]
      rw [List.drop_zero, hpattsA, List.toList_toArray, hpatts]
    refine ⟨hbext, hbii, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hview]
      exact denseFilterConstraints_coveredBy
        (denseReencodeOut_covered rB.1 (denseRncView st0) xs cd.bits cd.hm.get hcovOut hbval
          hpolyVars)
    · rw [hderiv]
      exact denseBitCM_covered rB.1 xs cd.bits cd.hm.get hxsValid hbval
    · rw [hview, hderiv, ← hF5.view]
      have h1 := denseCheckReencode_sound (denseRncView st0) bs rB.1.isInput xs cd.bits cd.hm.get
        hxsInput hxsOcc hxsBits hbnInput hchk
      have h2 := DensePassCorrect.denseFilterConstraintsEntailed
        (denseReencodeOut (denseRncView st0) xs cd.bits cd.hm.get) bs rB.1.isInput
        (fun c => !denseIsZero c) (fun c _ hk => denseIsZero_eval (by simpa using hk))
      simpa using h1.andThen h2
    · exact denseRncOk_write hzero hF5.ok (denseRncCsEdits_editOk ctx st0 xs cd)
    · intro v hv
      rcases denseRncWrite_occ_sub hzero hpatts hF5.ok.cvs hF5.ok.use hF5.ok.bus hm hsf hmB hsfB
        hpolyVars v hv with h | h
      · exact denseRncWrite_seen v (Or.inl (hF5.vo v h))
      · exact denseRncWrite_seen v (Or.inr h)
    · intro v hv
      rcases denseRncWrite_occ_sub hzero hpatts hF5.ok.cvs hF5.ok.use hF5.ok.bus hm hsf hmB hsfB
        hpolyVars v hv with h | h
      · obtain ⟨_, h2, h3, _⟩ := denseRncWrite_fields ctx st0 cd.bits
          (denseRncCsEdits ctx st0 xs cd).1 (denseRncBiEdits ctx st0 xs cd).1
        rcases hF5.nv v h with h1 | h1
        · exact Or.inl (by rw [h2]; exact h1)
        · exact Or.inr (h3 v h1)
      · obtain ⟨_, _, _, h4⟩ := denseRncWrite_fields ctx st0 cd.bits
          (denseRncCsEdits ctx st0 xs cd).1 (denseRncBiEdits ctx st0 xs cd).1
        exact Or.inr (h4 v h)

/-! ### The loop -/

theorem denseRncLoop_correct [Fact p.Prime] (ctx : DenseRncCtx p) (bs : BusSemantics p)
    (hzero : ctx.zeroE = (DenseExpr.const 0 : DenseExpr p)) (hopz : ctx.ops.zero = (0 : ZMod p)) :
    ∀ (targets : List (List VarId)) (idx : Nat) (reg : VarRegistry) (st : DenseRncState p)
      (pre : String),
      (denseRncView st).CoveredBy reg → DenseRncOk st → DenseRncVarsOk st → DenseRncNVarOk st →
      DenseRncPost bs reg st (denseRncLoop ctx targets idx reg st pre) := by
  intro targets
  induction targets with
  | nil =>
      intro idx reg st pre hcov hok hvo hnv
      exact ⟨VarRegistry.Extends.refl reg, fun _ => rfl, hcov,
        (by intro x hx; cases hx),
        DensePassCorrect.refl reg.isInput (denseRncView st) bs, hok, hvo, hnv⟩
  | cons xs rest ih =>
      intro idx reg st pre hcov hok hvo hnv
      simp only [denseRncLoop]
      rcases hstep : denseRncStep ctx reg st xs (pre ++ toString idx) with ⟨reg1, st1, derivs1⟩
      have hsp := denseRncStep_correct ctx reg st xs (pre ++ toString idx) bs hzero hopz hcov hok
        hvo hnv
      simp only [DenseRncPost, hstep] at hsp
      obtain ⟨hs_ext, hs_ii, hs_cov, hs_dcov, hs_correct, hs_ok, hs_vo, hs_nv⟩ := hsp
      rcases hrec : denseRncLoop ctx rest (idx + 1) reg1 st1
          (if derivs1.isEmpty then pre else s!"rnc{st1.live}_{st1.bisN}_") with ⟨reg2, st2, derivs2⟩
      have hih := ih (idx + 1) reg1 st1
        (if derivs1.isEmpty then pre else s!"rnc{st1.live}_{st1.bisN}_") hs_cov hs_ok hs_vo hs_nv
      simp only [DenseRncPost, hrec] at hih
      obtain ⟨hr_ext, hr_ii, hr_cov, hr_dcov, hr_correct, hr_ok, hr_vo, hr_nv⟩ := hih
      refine ⟨hs_ext.trans hr_ext, fun i => (hr_ii i).trans (hs_ii i), hr_cov, ?_, ?_, hr_ok,
        hr_vo, hr_nv⟩
      · exact DenseDerivations.coveredBy_append
          (DenseDerivations.CoveredBy.mono hr_ext hs_dcov) hr_dcov
      · have hfe : reg2.isInput = reg1.isInput := funext hr_ii
        have hstepcert : DensePassCorrect reg2.isInput (denseRncView st) (denseRncView st1)
            derivs1 bs := by rw [hfe]; exact hs_correct
        exact hstepcert.andThen hr_correct

/-! ### The pass

The seed's view is `d` with trivially-true constraints dropped — itself a verified step
(`DensePassCorrect.denseFilterConstraintsEntailed`) — and its invariants come from the scan, the
anchor builder and coverage; the lazily built indexes start as `none`, so their invariants hold
vacuously. -/

theorem denseRncRun_props [Fact p.Prime] (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (d : DenseConstraintSystem p) (targets : List (List VarId))
    (hcov : d.CoveredBy reg)
    (hcvs : ∀ (i : Nat) (c : DenseExpr p), d.algebraicConstraints.toArray[i]? = some c →
      (denseRncScan d.algebraicConstraints.toArray).1[i]? = some (denseRncCapVars c))
    (hsize : (denseRncScan d.algebraicConstraints.toArray).1.size
      = d.algebraicConstraints.toArray.size) :
    reg.Extends (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).1
    ∧ (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).2.1.CoveredBy
      (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).1
    ∧ DenseDerivations.CoveredBy (denseRncRun b reg d
        (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).1
      (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).2.2
    ∧ DensePassCorrect (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).1.isInput d
      (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).2.1
      (denseRncRun b reg d (denseRncScan d.algebraicConstraints.toArray).1
        (denseRncScan d.algebraicConstraints.toArray).2 targets).2.2 bs := by
  unfold denseRncRun
  split
  · exact ⟨VarRegistry.Extends.refl reg, hcov, (by intro x hx; cases hx),
      DensePassCorrect.refl reg.isInput d bs⟩
  · have hfilter : DensePassCorrect reg.isInput d (d.filterConstraints (fun c => !denseIsZero c))
        ([] : DenseDerivations p) bs :=
      DensePassCorrect.denseFilterConstraintsEntailed d bs _ (fun c => !denseIsZero c)
        (fun c _ hk => denseIsZero_eval (by simpa using hk))
    set cvs := (denseRncScan d.algebraicConstraints.toArray).1 with hcvsdef
    set live := (denseRncScan d.algebraicConstraints.toArray).2 with hlivedef
    set st := denseRncSeed reg.byId.size d cvs live with hst
    have hseedCs : st.cs = d.algebraicConstraints.toArray := by rw [hst]; rfl
    have hseedBis : st.bis = d.busInteractions.toArray := by rw [hst]; rfl
    have hseedView : denseRncView st = d.filterConstraints (fun c => !denseIsZero c) := by
      unfold denseRncView DenseConstraintSystem.filterConstraints
      rw [hseedCs, hseedBis, Array.toList_filter, List.toList_toArray, List.toList_toArray]
    have hseedCov : (denseRncView st).CoveredBy reg := by
      rw [hseedView]; exact denseFilterConstraints_coveredBy hcov
    have hseedOk : DenseRncOk st := by
      refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [hseedCs]; show cvs.size = _; exact hsize
      · intro i c hi
        rw [hseedCs] at hi
        show cvs[i]? = some (denseRncCapVars c)
        exact hcvs i c hi
      · intro i c hi v hv
        rw [hseedCs] at hi
        show i ∈ (denseRncAnchorBuild d.algebraicConstraints).buckets.getD v []
        refine denseRncAnchorBuild_complete d.algebraicConstraints i c ?_ v hv
        rw [← Array.getElem?_toList (xs := d.algebraicConstraints.toArray),
          List.toList_toArray] at hi
        exact hi
      · intro m hm; rw [hst] at hm; exact absurd hm (by simp [denseRncSeed])
      · intro sf hsf; rw [hst] at hsf; exact absurd hsf (by simp [denseRncSeed])
      · intro m hm; rw [hst] at hm; exact absurd hm (by simp [denseRncSeed])
      · intro sf hsf; rw [hst] at hsf; exact absurd hsf (by simp [denseRncSeed])
    have hseedVo : DenseRncVarsOk st := by
      intro v _
      show ((match st.varSeen with | some m => denseRncGetB m v | none => true)
        || st.minted.contains v) = true
      rw [hst]
      simp [denseRncSeed]
    have hseedNv : DenseRncNVarOk st := by
      intro v hv
      refine Or.inl ?_
      have hd : v ∈ d.occ := by
        rw [hseedView] at hv
        exact denseFilterConstraints_occ_sub d (fun c => !denseIsZero c) v hv
      show v.index < st.nVar
      rw [hst]
      exact DenseConstraintSystem.occ_valid hcov v hd
    obtain ⟨hext, hii, hcovOut, hdcov, hcorr, _, _, _⟩ :=
      denseRncLoop_correct (denseRncCtxOf b) bs (by
        show DenseExpr.const (denseZModOps (p := p)).zero = DenseExpr.const 0
        rw [show (denseZModOps (p := p)).zero = (0 : ZMod p) from zmodZeroP_eq])
        (show (denseRncCtxOf (p := p) b).ops.zero = (0 : ZMod p) from zmodZeroP_eq)
        targets 0 reg st (s!"rnc{live}_{d.busInteractions.length}_") hseedCov hseedOk hseedVo
        hseedNv
    refine ⟨hext, hcovOut, hdcov, ?_⟩
    have hfe : (denseRncLoop (denseRncCtxOf b) targets 0 reg st
        (s!"rnc{live}_{d.busInteractions.length}_")).1.isInput = reg.isInput := funext hii
    have hpre : DensePassCorrect (denseRncLoop (denseRncCtxOf b) targets 0 reg st
        (s!"rnc{live}_{d.busInteractions.length}_")).1.isInput d (denseRncView st)
        ([] : DenseDerivations p) bs := by
      rw [hfe, hseedView]; exact hfilter
    simpa using hpre.andThen hcorr

theorem denseRncF_props (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    reg.Extends (denseRncF pw b reg bs facts d).1
    ∧ (denseRncF pw b reg bs facts d).2.1.CoveredBy (denseRncF pw b reg bs facts d).1
    ∧ DenseDerivations.CoveredBy (denseRncF pw b reg bs facts d).1
        (denseRncF pw b reg bs facts d).2.2
    ∧ DensePassCorrect (denseRncF pw b reg bs facts d).1.isInput d
        (denseRncF pw b reg bs facts d).2.1 (denseRncF pw b reg bs facts d).2.2 bs := by
  unfold denseRncF
  split
  · next hpr =>
      haveI : Fact p.Prime := ⟨pw.correct hpr⟩
      obtain ⟨hcvs, hsize⟩ := denseRncScan_cvsOk d.algebraicConstraints.toArray
      exact denseRncRun_props b reg bs d _ hcov hcvs hsize
  · refine ⟨VarRegistry.Extends.refl reg, hcov, ?_, DensePassCorrect.refl reg.isInput d bs⟩
    intro x hx; cases hx

/-- The registered witness re-encoding pass (see `denseRncF` in `Reencode.lean`). -/
def denseReencodePass (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofExtending (denseRncF pw b)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).1)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).2.1)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).2.2.1)
    (fun reg bs facts d hcov => (denseRncF_props pw b reg bs facts d hcov).2.2.2)

end ApcOptimizer.Dense
