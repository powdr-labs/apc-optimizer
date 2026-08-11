import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DigitFold

set_option autoImplicit false

/-! # Collapsing a multi-limb reciprocal-witness group to one hint — proof

`VarId` correctness for `denseHintCollapseF` (`HintCollapse.lean`) over dense environments
`VarId → ZMod p`, via `Bridge.lean`. Substituting the once-occurring witnesses `D` to a common value
collapses target `E` to `denom·inv + rest`, with `inv = QuotientOrZero(−rest, denom)` a fresh
`powdrId? = none` witness (so `isInput` is preserved pointwise). Field-sum lemmas come from
`HintCollapse.lean`; the bounds map through `denseBuild_sound` (`Proofs/DigitFold.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dense expression evaluation congruence and occurrence facts -/

/-- Dense expression evaluation depends only on the variables that occur (file-local). -/
private theorem hcEvalCongr (e : DenseExpr p) (d1 d2 : VarId → ZMod p)
    (h : ∀ i ∈ e.vars, d1 i = d2 i) : e.eval d1 = e.eval d2 := by
  induction e with
  | const n => rfl
  | var i => exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
      simp only [DenseExpr.eval]
      rw [iha (fun i hi => h i (by simp [DenseExpr.vars, hi])),
          ihb (fun i hi => h i (by simp [DenseExpr.vars, hi]))]
  | mul a b iha ihb =>
      simp only [DenseExpr.eval]
      rw [iha (fun i hi => h i (by simp [DenseExpr.vars, hi])),
          ihb (fun i hi => h i (by simp [DenseExpr.vars, hi]))]

theorem denseMentions_false_not_mem (i : VarId) (e : DenseExpr p) (h : e.mentions i = false) :
    i ∉ e.vars := by
  induction e with
  | const n => intro hi; simp [DenseExpr.vars] at hi
  | var j =>
      intro hi
      simp only [DenseExpr.vars, List.mem_singleton] at hi
      simp only [DenseExpr.mentions] at h
      rw [hi] at h
      simp at h
  | add a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (ha | hb)
      · exact iha h.1 ha
      · exact ihb h.2 hb
  | mul a b iha ihb =>
      simp only [DenseExpr.mentions, Bool.or_eq_false_iff] at h
      simp only [DenseExpr.vars, List.mem_append]
      rintro (ha | hb)
      · exact iha h.1 ha
      · exact ihb h.2 hb

/-! ## Splitting off the linear part in one variable (`extractLinear`/`peel`/`sumExpr`) -/

theorem denseExtractLinear_eval (wv : VarId) (E : DenseExpr p) (denv : VarId → ZMod p) :
    E.eval denv
      = (denseExtractLinear wv E).1.eval denv * denv wv + (denseExtractLinear wv E).2.eval denv := by
  induction E with
  | const c => simp [denseExtractLinear, DenseExpr.eval]
  | var x => by_cases h : x = wv <;> simp [denseExtractLinear, h, DenseExpr.eval]
  | add e1 e2 ih1 ih2 =>
      simp only [denseExtractLinear, DenseExpr.eval]
      rw [ih1, ih2]; ring
  | mul e1 e2 ih1 ih2 =>
      simp only [denseExtractLinear]
      split
      · simp only [DenseExpr.eval]; rw [ih1]; ring
      · simp only [DenseExpr.eval]; rw [ih2]; ring

theorem densePeel_eval (ds : List VarId) (E : DenseExpr p) (denv : VarId → ZMod p) :
    E.eval denv
      = ((densePeel ds E).1.zip ds).foldr (fun cd acc => cd.1.eval denv * denv cd.2 + acc) 0
        + (densePeel ds E).2.eval denv := by
  induction ds generalizing E with
  | nil => simp [densePeel]
  | cons d ds ih =>
      simp only [densePeel]
      rw [denseExtractLinear_eval d E denv, ih (denseExtractLinear d E).2]
      simp only [List.zip_cons_cons, List.foldr_cons]
      ring

theorem denseSumExpr_eval (l : List (DenseExpr p)) (denv : VarId → ZMod p) :
    (denseSumExpr l).eval denv = (l.map (fun c => c.eval denv)).sum := by
  induction l with
  | nil => simp [denseSumExpr, DenseExpr.eval]
  | cons c cs ih =>
      simp only [denseSumExpr, List.foldr_cons] at *
      simp only [DenseExpr.eval, List.map_cons, List.sum_cons, ih]

theorem denseSumExpr_vars {l : List (DenseExpr p)} {x : VarId}
    (hx : x ∈ (denseSumExpr l).vars) : ∃ c ∈ l, x ∈ c.vars := by
  induction l with
  | nil => simp [denseSumExpr, DenseExpr.vars] at hx
  | cons c cs ih =>
      simp only [denseSumExpr, List.foldr_cons, DenseExpr.vars, List.mem_append] at hx
      rcases hx with h | h
      · exact ⟨c, List.mem_cons_self .., h⟩
      · obtain ⟨c', hc', hx'⟩ := ih h
        exact ⟨c', List.mem_cons_of_mem _ hc', hx'⟩

theorem densePeel_length (D : List VarId) (E : DenseExpr p) :
    (densePeel D E).1.length = D.length := by
  induction D generalizing E with
  | nil => simp [densePeel]
  | cons d ds ih => simp only [densePeel, List.length_cons]; rw [ih]

theorem denseExtractLinear_vars (wv : VarId) (E : DenseExpr p) :
    (∀ x ∈ (denseExtractLinear wv E).1.vars, x ∈ E.vars) ∧
      (∀ x ∈ (denseExtractLinear wv E).2.vars, x ∈ E.vars) := by
  induction E with
  | const c => simp [denseExtractLinear, DenseExpr.vars]
  | var x => by_cases h : x = wv <;> simp [denseExtractLinear, h, DenseExpr.vars]
  | add e1 e2 ih1 ih2 =>
      simp only [denseExtractLinear, DenseExpr.vars, List.mem_append]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> rcases hx with h | h
      · exact Or.inl (ih1.1 x h)
      · exact Or.inr (ih2.1 x h)
      · exact Or.inl (ih1.2 x h)
      · exact Or.inr (ih2.2 x h)
  | mul e1 e2 ih1 ih2 =>
      simp only [denseExtractLinear]
      split <;> simp only [DenseExpr.vars, List.mem_append] <;>
        refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> rcases hx with h | h
      · exact Or.inl (ih1.1 x h)
      · exact Or.inr h
      · exact Or.inl (ih1.2 x h)
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr (ih2.1 x h)
      · exact Or.inl h
      · exact Or.inr (ih2.2 x h)

theorem densePeel_snd_vars (D : List VarId) (E : DenseExpr p) :
    ∀ x ∈ (densePeel D E).2.vars, x ∈ E.vars := by
  induction D generalizing E with
  | nil => simp [densePeel]
  | cons d ds ih =>
      intro x hx
      simp only [densePeel] at hx
      exact (denseExtractLinear_vars d E).2 x (ih (denseExtractLinear d E).2 x hx)

theorem densePeel_fst_vars (D : List VarId) (E : DenseExpr p) :
    ∀ c ∈ (densePeel D E).1, ∀ x ∈ c.vars, x ∈ E.vars := by
  induction D generalizing E with
  | nil => simp [densePeel]
  | cons d ds ih =>
      intro c hc x hx
      simp only [densePeel, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact (denseExtractLinear_vars d E).1 x hx
      · exact (denseExtractLinear_vars d E).2 x (ih (denseExtractLinear d E).2 c hc x hx)

/-! ## The plain reassignment frame -/

/-- Reassign every variable of `D` to `w`, leaving the rest at `denv`. -/
def denseReassign (D : List VarId) (w : ZMod p) (denv : VarId → ZMod p) : VarId → ZMod p :=
  fun v => if v ∈ D then w else denv v

theorem denseEval_reassign_free (c : DenseExpr p) (D : List VarId) (w : ZMod p)
    (denv : VarId → ZMod p) (h : ∀ d ∈ D, d ∉ c.vars) :
    c.eval (denseReassign D w denv) = c.eval denv :=
  hcEvalCongr c _ _ (fun x hx => by
    show (if x ∈ D then w else denv x) = denv x
    rw [if_neg (fun hxD => h x hxD hx)])

theorem denseFoldr_reassign (pairs : List (DenseExpr p × VarId)) (D : List VarId)
    (denv : VarId → ZMod p) (w : ZMod p)
    (hmem : ∀ cd ∈ pairs, cd.2 ∈ D)
    (hfree : ∀ cd ∈ pairs, ∀ d ∈ D, d ∉ cd.1.vars) :
    pairs.foldr (fun cd acc => cd.1.eval (denseReassign D w denv) * (denseReassign D w denv) cd.2 + acc) 0
      = (pairs.map (fun cd => cd.1.eval denv)).sum * w := by
  induction pairs with
  | nil => simp
  | cons cd rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      rw [ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
            (fun x hx => hfree x (List.mem_cons_of_mem _ hx))]
      have h1 : (denseReassign D w denv) cd.2 = w := by
        show (if cd.2 ∈ D then w else denv cd.2) = w
        rw [if_pos (hmem cd (List.mem_cons_self ..))]
      have h2 : cd.1.eval (denseReassign D w denv) = cd.1.eval denv :=
        denseEval_reassign_free cd.1 D w denv (fun d hd => hfree cd (List.mem_cons_self ..) d hd)
      rw [h1, h2]; ring

theorem densePeel_reassign_eval (D : List VarId) (E : DenseExpr p)
    (hcfree : ∀ c ∈ (densePeel D E).1, ∀ d ∈ D, d ∉ c.vars)
    (hrfree : ∀ d ∈ D, d ∉ (densePeel D E).2.vars)
    (denv : VarId → ZMod p) (w : ZMod p) :
    E.eval (denseReassign D w denv)
      = (denseSumExpr (densePeel D E).1).eval denv * w + (densePeel D E).2.eval denv := by
  have hz : ((densePeel D E).1.zip D).map (fun cd => cd.1.eval denv)
      = (densePeel D E).1.map (fun c => c.eval denv) := by
    have hlen : (densePeel D E).1.length ≤ D.length := by rw [densePeel_length]
    conv_rhs => rw [← List.map_fst_zip hlen, List.map_map]
    rfl
  rw [densePeel_eval D E (denseReassign D w denv), denseEval_reassign_free _ D w denv hrfree,
      denseFoldr_reassign ((densePeel D E).1.zip D) D denv w
        (fun cd hcd => (List.of_mem_zip hcd).2)
        (fun cd hcd d hd => hcfree cd.1 (List.of_mem_zip hcd).1 d hd),
      denseSumExpr_eval, hz]

theorem denseFoldr_zero (pairs : List (DenseExpr p × VarId)) (denv : VarId → ZMod p)
    (h0 : ∀ cd ∈ pairs, cd.1.eval denv = 0) :
    pairs.foldr (fun cd acc => cd.1.eval denv * denv cd.2 + acc) 0 = 0 := by
  induction pairs with
  | nil => simp
  | cons cd rest ih =>
      simp only [List.foldr_cons]
      rw [h0 cd (List.mem_cons_self ..), ih (fun x hx => h0 x (List.mem_cons_of_mem _ hx))]
      ring

/-! ## The weighted (sum-of-squares) reassignment frame -/

/-- Set each witness `cd.2` to `cd.1.eval denv * w`, leaving the rest at `denv`. -/
def denseAssocReassign (P : List (DenseExpr p × VarId)) (denv : VarId → ZMod p) (w : ZMod p) :
    VarId → ZMod p :=
  fun v => match P.find? (fun cd => cd.2 == v) with
    | some cd => cd.1.eval denv * w
    | none => denv v

theorem denseAssocReassign_agree (P : List (DenseExpr p × VarId)) (denv : VarId → ZMod p)
    (w : ZMod p) (v : VarId) (hv : v ∉ P.map (·.2)) : denseAssocReassign P denv w v = denv v := by
  have hnone : P.find? (fun cd => cd.2 == v) = none := by
    rw [List.find?_eq_none]
    intro cd hcd hbeq
    exact hv (List.mem_map.2 ⟨cd, hcd, of_decide_eq_true hbeq⟩)
  simp only [denseAssocReassign, hnone]

theorem denseFind?_snd_of_nodup (P : List (DenseExpr p × VarId))
    (hnd : (P.map (·.2)).Nodup) (cd : DenseExpr p × VarId) (hmem : cd ∈ P) :
    P.find? (fun x => x.2 == cd.2) = some cd := by
  induction P with
  | nil => simp at hmem
  | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hmem with rfl | htl
      · rw [List.find?_cons_of_pos (by simp)]
      · have hne : hd.2 ≠ cd.2 := fun h => hnd.1 (h ▸ List.mem_map.2 ⟨cd, htl, rfl⟩)
        rw [List.find?_cons_of_neg (by simp [hne])]
        exact ih hnd.2 htl

theorem denseAssocReassign_key (P : List (DenseExpr p × VarId)) (hnd : (P.map (·.2)).Nodup)
    (denv : VarId → ZMod p) (w : ZMod p) (cd : DenseExpr p × VarId) (hmem : cd ∈ P) :
    denseAssocReassign P denv w cd.2 = cd.1.eval denv * w := by
  simp only [denseAssocReassign, denseFind?_snd_of_nodup P hnd cd hmem]

theorem denseFoldr_sqReassign (P : List (DenseExpr p × VarId)) (σ denv : VarId → ZMod p)
    (w : ZMod p) (hval : ∀ cd ∈ P, σ cd.2 = cd.1.eval denv * w)
    (hfree : ∀ cd ∈ P, cd.1.eval σ = cd.1.eval denv) :
    P.foldr (fun cd acc => cd.1.eval σ * σ cd.2 + acc) 0
      = (P.map (fun cd => cd.1.eval denv * cd.1.eval denv)).sum * w := by
  induction P with
  | nil => simp
  | cons cd rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      rw [hval cd (List.mem_cons_self ..), hfree cd (List.mem_cons_self ..),
          ih (fun x hx => hval x (List.mem_cons_of_mem _ hx))
             (fun x hx => hfree x (List.mem_cons_of_mem _ hx))]
      ring

theorem densePeel_sqReassign_eval (D : List VarId) (E : DenseExpr p) (hnd : D.Nodup)
    (hcfree : ∀ c ∈ (densePeel D E).1, ∀ d ∈ D, d ∉ c.vars)
    (hrfree : ∀ d ∈ D, d ∉ (densePeel D E).2.vars)
    (denv : VarId → ZMod p) (w : ZMod p) :
    E.eval (denseAssocReassign ((densePeel D E).1.zip D) denv w)
      = (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).eval denv * w
        + (densePeel D E).2.eval denv := by
  set P := (densePeel D E).1.zip D with hP
  set σ := denseAssocReassign P denv w with hσ
  have hlen : (densePeel D E).1.length = D.length := densePeel_length D E
  have hmap2 : P.map (·.2) = D := by rw [hP]; exact List.map_snd_zip (by rw [hlen])
  have hmap1 : P.map (·.1) = (densePeel D E).1 := by rw [hP]; exact List.map_fst_zip (by rw [hlen])
  have hndP : (P.map (·.2)).Nodup := by rw [hmap2]; exact hnd
  have hrestσ : (densePeel D E).2.eval σ = (densePeel D E).2.eval denv :=
    hcEvalCongr _ _ _ (fun x hx => by
      rw [hσ]; exact denseAssocReassign_agree P denv w x
        (by rw [hmap2]; exact fun hxD => hrfree x hxD hx))
  have hcoσ : ∀ cd ∈ P, cd.1.eval σ = cd.1.eval denv := by
    intro cd hcd
    have hc1 : cd.1 ∈ (densePeel D E).1 := by rw [← hmap1]; exact List.mem_map.2 ⟨cd, hcd, rfl⟩
    refine hcEvalCongr _ _ _ (fun x hx => ?_)
    rw [hσ]
    exact denseAssocReassign_agree P denv w x (by rw [hmap2]; exact fun hxD => hcfree cd.1 hc1 x hxD hx)
  have hval : ∀ cd ∈ P, σ cd.2 = cd.1.eval denv * w :=
    fun cd hcd => by rw [hσ]; exact denseAssocReassign_key P hndP denv w cd hcd
  rw [densePeel_eval D E σ, hrestσ, denseFoldr_sqReassign P σ denv w hval hcoσ]
  have hLHS : P.map (fun cd => cd.1.eval denv * cd.1.eval denv)
      = (densePeel D E).1.map (fun c => c.eval denv * c.eval denv) := by
    rw [← hmap1, List.map_map]; rfl
  have hRHS : (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).eval denv
      = ((densePeel D E).1.map (fun c => c.eval denv * c.eval denv)).sum := by
    rw [denseSumExpr_eval, List.map_map]; rfl
  rw [hLHS, hRHS]

/-! ## Coefficient recognizers (soundness) -/

theorem denseCoeffVar_sound {c : DenseExpr p} {a : VarId} (h : denseCoeffVar c = some a) :
    (∀ denv, c.eval denv = denv a) ∧ (∀ x ∈ c.vars, x = a) ∧ a ∈ c.vars := by
  unfold denseCoeffVar at h
  split at h
  · rename_i a'; simp only [Option.some.injEq] at h; subst h
    exact ⟨fun _ => rfl, fun x hx => by simpa [DenseExpr.vars] using hx, by simp [DenseExpr.vars]⟩
  · rename_i a' c'; split_ifs at h with hc1; simp only [Option.some.injEq] at h; subst h; subst hc1
    exact ⟨fun denv => by simp [DenseExpr.eval], fun x hx => by simpa [DenseExpr.vars] using hx,
      by simp [DenseExpr.vars]⟩
  · rename_i c' a'; split_ifs at h with hc1; simp only [Option.some.injEq] at h; subst h; subst hc1
    exact ⟨fun denv => by simp [DenseExpr.eval], fun x hx => by simpa [DenseExpr.vars] using hx,
      by simp [DenseExpr.vars]⟩
  · exact absurd h (by simp)

theorem denseCoeffsByteOK_sound (reg : VarRegistry) (B : Std.HashMap VarId Nat) (D : List VarId) :
    ∀ (coeffs : List (DenseExpr p)), denseCoeffsByteOK reg B D coeffs = true →
      ∀ c ∈ coeffs, ∃ a : VarId, (∀ denv, c.eval denv = denv a) ∧ (∀ d ∈ D, d ∉ c.vars) ∧
        (∀ x ∈ c.vars, reg.isInput x = true) ∧ a ∈ c.vars ∧ ∃ b, B[a]? = some b ∧ b ≤ 256 := by
  intro coeffs
  induction coeffs with
  | nil => intro _ c hc; simp at hc
  | cons c0 cs ih =>
      intro h c hc
      simp only [denseCoeffsByteOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hcv, hDf⟩, hpow⟩, hrec⟩ := h
      rcases List.mem_cons.1 hc with rfl | hcs
      · cases hcva : denseCoeffVar c.fold with
        | none => rw [hcva] at hcv; simp at hcv
        | some a =>
            simp only [hcva] at hcv
            obtain ⟨heval, _, hmem⟩ := denseCoeffVar_sound hcva
            refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
            · intro denv
              rw [← DenseExpr.fold_eval c denv]; exact heval denv
            · intro d hd; exact of_decide_eq_true (List.all_eq_true.1 hDf d hd)
            · intro x hx; exact List.all_eq_true.1 hpow x hx
            · exact DenseExpr.fold_vars c a hmem
            · revert hcv
              cases hb : B[a]? with
              | none => intro hcv; simp at hcv
              | some b => intro hcv; exact ⟨b, rfl, of_decide_eq_true hcv⟩
      · exact ih hrec c hcs

theorem denseDiffVarsOf_sound {c : DenseExpr p} {a b : VarId}
    (h : denseDiffVarsOf c = some (a, b)) :
    (∀ denv, c.eval denv = denv a - denv b) ∧ (∀ x ∈ c.vars, x = a ∨ x = b) ∧
      a ∈ c.vars ∧ b ∈ c.vars := by
  unfold denseDiffVarsOf at h
  split at h
  · rename_i a' c' b'
    split_ifs at h with hc1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; subst hc1
    refine ⟨fun denv => by simp [DenseExpr.eval, sub_eq_add_neg], fun x hx => ?_, ?_, ?_⟩
    · simp only [DenseExpr.vars, List.nil_append, List.mem_append, List.mem_singleton] at hx
      exact hx
    · simp [DenseExpr.vars]
    · simp [DenseExpr.vars]
  · exact absurd h (by simp)

theorem denseSqCoeffsOK_sound (reg : VarRegistry) (B : Std.HashMap VarId Nat) (D : List VarId) :
    ∀ (coeffs : List (DenseExpr p)), denseSqCoeffsOK reg B D coeffs = true →
      ∀ c ∈ coeffs, ∃ a b : VarId, (∀ denv, c.eval denv = denv a - denv b) ∧
        (∀ d ∈ D, d ∉ c.vars) ∧ (∀ x ∈ c.vars, reg.isInput x = true) ∧
        a ∈ c.vars ∧ b ∈ c.vars ∧
        (∃ ba, B[a]? = some ba ∧ ba ≤ 256) ∧ (∃ bb, B[b]? = some bb ∧ bb ≤ 256) := by
  intro coeffs
  induction coeffs with
  | nil => intro _ c hc; simp at hc
  | cons c0 cs ih =>
      intro h c hc
      simp only [denseSqCoeffsOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hdv, hDf⟩, hpow⟩, hrec⟩ := h
      rcases List.mem_cons.1 hc with rfl | hcs
      · cases hdva : denseDiffVarsOf c.fold with
        | none => rw [hdva] at hdv; simp at hdv
        | some ab =>
            obtain ⟨a, b⟩ := ab
            simp only [hdva, Bool.and_eq_true] at hdv
            obtain ⟨hba, hbb⟩ := hdv
            obtain ⟨heval, _, hmema, hmemb⟩ := denseDiffVarsOf_sound hdva
            refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro denv; rw [← DenseExpr.fold_eval c denv]; exact heval denv
            · intro d hd; exact of_decide_eq_true (List.all_eq_true.1 hDf d hd)
            · intro x hx; exact List.all_eq_true.1 hpow x hx
            · exact DenseExpr.fold_vars c a hmema
            · exact DenseExpr.fold_vars c b hmemb
            · revert hba; cases hb : B[a]? with
              | none => intro hba; simp at hba
              | some ba => intro hba; exact ⟨ba, rfl, of_decide_eq_true hba⟩
            · revert hbb; cases hb : B[b]? with
              | none => intro hbb; simp at hbb
              | some bb => intro hbb; exact ⟨bb, rfl, of_decide_eq_true hbb⟩
      · exact ih hrec c hcs

/-! ## `occ` membership, registry/freshness helpers -/

theorem hcMemOcc {d : DenseConstraintSystem p} {i : VarId} :
    i ∈ d.occ ↔ (∃ c ∈ d.algebraicConstraints, i ∈ c.vars) ∨
      (∃ bi ∈ d.busInteractions, i ∈ denseBIVars bi) := by
  simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap]

/-- The `VarId` `register` returns for an already-registered variable is exactly its existing ID. -/
theorem register_snd_eq_of_idOf {reg : VarRegistry} {v : OutputVariable} {i : VarId}
    (h : reg.idOf? v = some i) : (reg.register v).2 = i := by
  have h1 := VarRegistry.register_idOf reg v
  have h2 := (VarRegistry.register_extends reg v).idOf_eq h
  rw [h1] at h2
  exact Option.some.inj h2

/-- For an unregistered variable, `register` allocates the trailing (fresh) `VarId`. -/
theorem register_snd_eq_of_none {reg : VarRegistry} {v : OutputVariable}
    (h : reg.idOf? v = none) : (reg.register v).2 = ⟨reg.byId.size⟩ := by
  grind [VarRegistry.register, VarRegistry.idOf?]

/-- Registering a `powdrId? = none` variable preserves `isInput` pointwise. -/
theorem hcRegisterIsInputEq (reg : VarRegistry) (v : OutputVariable) (hv : v.powdrId? = none)
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

/-- The freshly-minted witness does not occur in the current system: on an existing registration the
    `denseIsFresh` gate ruled out `d.occ` membership; on a fresh registration the new trailing `VarId`
    is out of range, hence not a covered occurrence. -/
theorem denseIsFresh_notMem {reg : VarRegistry} {d : DenseConstraintSystem p} {v : OutputVariable}
    (hcov : d.CoveredBy reg) (h : denseIsFresh reg d v = true) :
    (reg.register v).2 ∉ d.occ := by
  unfold denseIsFresh at h
  cases hlook : reg.idOf? v with
  | some i =>
      simp only [hlook] at h
      rw [register_snd_eq_of_idOf hlook]
      intro hmem
      rw [List.contains_iff_mem.mpr hmem] at h
      simp at h
  | none =>
      rw [register_snd_eq_of_none hlook]
      intro hmem
      have hv := DenseConstraintSystem.occ_valid hcov _ hmem
      exact absurd hv (by simp [VarRegistry.Valid])

/-! ## The collapse transport -/

/-- Correctness of the hint collapse: replacing target `E` by `denom·inv + rest`
    (with `inv = QuotientOrZero(−rest, denom)` a fresh derived witness) is `DensePassCorrect`. The
    hypotheses: `hEeq` — the reciprocal-witness collapse identity; `hbyte` — a vanishing denominator
    forces the remainder to vanish; the rest are framing: freshness, the witnesses occurring only in
    `E`, and the new expressions reading only input columns. -/
theorem dense_collapse_correct [Fact p.Prime] (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (E denom rest : DenseExpr p) (D : List VarId) (invId : VarId)
    (reasg : (VarId → ZMod p) → ZMod p → (VarId → ZMod p))
    (hE : E ∈ d.algebraicConstraints)
    (hagree : ∀ (denv : VarId → ZMod p) (w : ZMod p) (v : VarId), v ∉ D → reasg denv w v = denv v)
    (hEeq : ∀ (denv : VarId → ZMod p) (w : ZMod p),
      E.eval (reasg denv w) = denom.eval denv * w + rest.eval denv)
    (hbyte : ∀ denv, d.satisfies bs denv → denom.eval denv = 0 → rest.eval denv = 0)
    (hinv_fresh : invId ∉ d.occ) (hinv_id : isInput invId = false)
    (hDonce : ∀ dw ∈ D, ∀ c ∈ d.algebraicConstraints, dw ∈ c.vars → c = E)
    (hDbus : ∀ dw ∈ D, ∀ bi ∈ d.busInteractions,
      dw ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, dw ∉ e.vars)
    (hrest_sub : ∀ x ∈ rest.vars, x ∈ d.occ) (hden_sub : ∀ x ∈ denom.vars, x ∈ d.occ)
    (hden_pow : ∀ x ∈ denom.vars, isInput x = true)
    (hrest_pow : ∀ x ∈ rest.vars, isInput x = true) :
    DensePassCorrect isInput d
      { d with algebraicConstraints :=
          d.algebraicConstraints.map (fun c => if c = E then
            (DenseExpr.add (DenseExpr.mul denom (DenseExpr.var invId)) rest) else c) }
      [(invId, DenseComputationMethod.quotientOrZero (DenseExpr.mul (DenseExpr.const (-1)) rest) denom)]
      bs := by
  set E' : DenseExpr p := DenseExpr.add (DenseExpr.mul denom (DenseExpr.var invId)) rest with hE'
  set method : DenseComputationMethod p :=
    DenseComputationMethod.quotientOrZero (DenseExpr.mul (DenseExpr.const (-1)) rest) denom with hmeth
  set out : DenseConstraintSystem p :=
    { d with algebraicConstraints := d.algebraicConstraints.map (fun c => if c = E then E' else c) }
    with hout
  have hob : out.busInteractions = d.busInteractions := by rw [hout]
  have hoa : out.algebraicConstraints
      = d.algebraicConstraints.map (fun c => if c = E then E' else c) := by rw [hout]
  have hE'eval : ∀ denv : VarId → ZMod p,
      E'.eval denv = denom.eval denv * denv invId + rest.eval denv := fun denv => rfl
  have hmemOut : ∀ c' ∈ out.algebraicConstraints, c' = E' ∨ c' ∈ d.algebraicConstraints := by
    intro c' hc'
    rw [hoa] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    by_cases h : c = E
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simpa [h] using hc)
  have hE'mem : E' ∈ out.algebraicConstraints := by
    rw [hoa]; exact List.mem_map.2 ⟨E, hE, by simp⟩
  have hframe_ne : ∀ (c : DenseExpr p), (∀ dw ∈ D, dw ∉ c.vars) →
      ∀ (w : ZMod p) (denv : VarId → ZMod p), c.eval (reasg denv w) = c.eval denv := by
    intro c hc w denv
    exact hcEvalCongr c _ _ (fun x hx => hagree denv w x (fun hxD => hc x hxD hx))
  have hbe : ∀ (denv : VarId → ZMod p) (bi : BusInteraction (DenseExpr p)),
      bi ∈ d.busInteractions → denseBIEval bi (reasg denv (denv invId)) = denseBIEval bi denv := by
    intro denv bi hbi
    refine denseBIEval_congr bi _ _ (fun x hx => ?_)
    have hxfree : x ∉ D := by
      intro hxD
      obtain ⟨hm, hp⟩ := hDbus x hxD bi hbi
      simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hx
      rcases hx with hx | ⟨e, he, hxe⟩
      · exact hm hx
      · exact hp e he hxe
    exact hagree denv (denv invId) x hxfree
  have hcssat : ∀ denv, out.satisfies bs denv → d.satisfies bs (reasg denv (denv invId)) := by
    intro denv hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · by_cases h : c = E
      · subst h
        rw [hEeq denv (denv invId)]
        have hz : E'.eval denv = 0 := hsat.1 E' hE'mem
        rw [hE'eval] at hz; exact hz
      · have hcvarsfree : ∀ dw ∈ D, dw ∉ c.vars := fun dw hd hdc => h (hDonce dw hd c hc hdc)
        rw [hframe_ne c hcvarsfree (denv invId) denv]
        have hfc : (if c = E then E' else c) = c := by simp [h]
        have hc0 := hsat.1 (if c = E then E' else c) (by rw [hoa]; exact List.mem_map.2 ⟨c, hc, rfl⟩)
        rwa [hfc] at hc0
    · rw [hbe denv bi (hob ▸ hbi)]
      exact hsat.2 bi (hob ▸ hbi)
  have hsound : out.implies d bs := by
    intro denv hsat
    refine ⟨reasg denv (denv invId), hcssat denv hsat, ?_⟩
    have hse : out.sideEffects bs denv = d.sideEffects bs (reasg denv (denv invId)) := by
      unfold DenseConstraintSystem.sideEffects
      refine funext (fun message => congrArg (multiplicitySum message) ?_)
      rw [hob]
      refine List.map_congr_left (fun bi hbi => ?_)
      rw [hbe denv bi (List.mem_of_mem_filter hbi)]
    rw [hse]
  have hout_occ : ∀ i ∈ out.occ, i = invId ∨ i ∈ d.occ := by
    intro i hi
    rw [hcMemOcc] at hi
    rcases hi with ⟨c', hc', hic⟩ | ⟨bi, hbi, hbiv⟩
    · rcases hmemOut c' (hoa ▸ hc') with rfl | hcs
      · rw [hE'] at hic
        simp only [DenseExpr.vars, List.mem_append, List.mem_singleton] at hic
        rcases hic with (hd | hi') | hr
        · exact Or.inr (hden_sub i hd)
        · exact Or.inl hi'
        · exact Or.inr (hrest_sub i hr)
      · exact Or.inr (hcMemOcc.2 (Or.inl ⟨c', hcs, hic⟩))
    · exact Or.inr (hcMemOcc.2 (Or.inr ⟨bi, hob ▸ hbi, hbiv⟩))
  refine ⟨hsound, ?_, ?_, ?_⟩
  · -- Invariant preservation.
    intro hcsInv denv hsatOut bi hbiOut
    show (denseBIEval bi denv).multiplicity ≠ 0 → bs.maintainsInvariants (denseBIEval bi denv)
    rw [← hbe denv bi (hob ▸ hbiOut)]
    exact hcsInv (reasg denv (denv invId)) (hcssat denv hsatOut) bi (hob ▸ hbiOut)
  · -- No new powdr-ID (input) column.
    intro i hiout hisT
    rcases hout_occ i hiout with rfl | hd
    · rw [hinv_id] at hisT; exact absurd hisT (by simp)
    · exact hd
  · -- Completeness with derivations.
    intro denv hadm hsat
    set envC := Function.update denv invId (method.eval denv) with hCdef
    have hagreeOcc : ∀ i ∈ d.occ, envC i = denv i := by
      intro i hi
      refine Function.update_of_ne ?_ _ _
      intro heq; exact hinv_fresh (heq ▸ hi)
    have hbeC : ∀ bi ∈ d.busInteractions, denseBIEval bi envC = denseBIEval bi denv := by
      intro bi hbi
      refine denseBIEval_congr bi _ _ (fun x hx => ?_)
      exact hagreeOcc x (DenseConstraintSystem.mem_occ_of_bi hbi hx)
    have hmethodCongr : method.eval envC = method.eval denv := by
      rw [hmeth]
      simp only [DenseComputationMethod.eval, DenseExpr.eval]
      rw [hcEvalCongr denom envC denv (fun x hx => hagreeOcc x (hden_sub x hx)),
          hcEvalCongr rest envC denv (fun x hx => hagreeOcc x (hrest_sub x hx))]
    refine ⟨envC, ⟨fun c' hc' => ?_, fun bi hbi => ?_⟩, ?_, ?_, ?_, ?_⟩
    · -- output constraints hold at `envC`
      rcases hmemOut c' (hoa ▸ hc') with rfl | hcs
      · rw [hE'eval]
        have hdenC : denom.eval envC = denom.eval denv :=
          hcEvalCongr _ _ _ (fun x hx => hagreeOcc x (hden_sub x hx))
        have hrestC : rest.eval envC = rest.eval denv :=
          hcEvalCongr _ _ _ (fun x hx => hagreeOcc x (hrest_sub x hx))
        rw [hdenC, hrestC, hCdef, Function.update_self]
        by_cases hd0 : denom.eval denv = 0
        · have hme : method.eval denv = 0 := by
            rw [hmeth]; simp only [DenseComputationMethod.eval, hd0, if_pos]
          rw [hme, mul_zero, zero_add]
          exact hbyte denv hsat hd0
        · have hme : method.eval denv = (denom.eval denv)⁻¹ * ((-1) * rest.eval denv) := by
            rw [hmeth]; simp only [DenseComputationMethod.eval, if_neg hd0, DenseExpr.eval]
          rw [hme, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
          ring
      · have hce : c'.eval envC = c'.eval denv :=
          hcEvalCongr _ _ _ (fun x hx =>
            hagreeOcc x (hcMemOcc.2 (Or.inl ⟨c', hcs, hx⟩)))
        rw [hce]; exact hsat.1 c' hcs
    · rw [hbeC bi (hob ▸ hbi)]; exact hsat.2 bi (hob ▸ hbi)
    · -- admissibility preserved
      have hmapeq : (d.busInteractions.map (fun bi => denseBIEval bi envC))
          = (d.busInteractions.map (fun bi => denseBIEval bi denv)) :=
        List.map_congr_left (fun bi hbi => hbeC bi hbi)
      show bs.admissible ((out.busInteractions.map (fun bi => denseBIEval bi envC)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId))
      rw [hob, hmapeq]; exact hadm
    · -- side effects equivalent
      have hse : d.sideEffects bs denv = out.sideEffects bs envC := by
        unfold DenseConstraintSystem.sideEffects
        refine funext (fun message => congrArg (multiplicitySum message) ?_)
        rw [hob]
        refine List.map_congr_left (fun bi hbi => ?_)
        rw [hbeC bi (List.mem_of_mem_filter hbi)]
      rw [hse]
    · -- input columns preserved
      intro i hisT
      have hne : i ≠ invId := by intro heq; rw [heq, hinv_id] at hisT; exact absurd hisT (by simp)
      exact Function.update_of_ne hne _ _
    · -- reconstruction of derived columns
      intro inputVarIds hpowIn i hiout hisF
      have hmf_pos : DenseDerivations.methodFor [(invId, method)] invId = some method := by
        simp [DenseDerivations.methodFor]
      have hmf_neg : ∀ j, j ≠ invId →
          DenseDerivations.methodFor [(invId, method)] j = none := by
        intro j hj; simp [DenseDerivations.methodFor, Ne.symm hj]
      by_cases hveq : i = invId
      · subst hveq
        simp only [hmf_pos]
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          rw [hmeth] at hj
          simp only [DenseComputationMethod.vars, DenseExpr.vars, List.nil_append,
            List.mem_append] at hj
          rcases hj with hr | hd
          · exact hrest_pow j hr
          · exact hden_pow j hd
        · intro j hj
          rw [hmeth] at hj
          simp only [DenseComputationMethod.vars, DenseExpr.vars, List.nil_append,
            List.mem_append] at hj
          rcases hj with hr | hd
          · exact hpowIn j (hrest_sub j hr) (hrest_pow j hr)
          · exact hpowIn j (hden_sub j hd) (hden_pow j hd)
        · rw [hmethodCongr, hCdef, Function.update_self]
      · simp only [hmf_neg i hveq]
        have hidocc : i ∈ d.occ := (hout_occ i hiout).resolve_left hveq
        exact ⟨hidocc, hagreeOcc i hidocc⟩

/-! ## Coverage helpers -/

/-- Occurrence-validity gives coverage. -/
theorem hcCoveredByOfOcc {r : VarRegistry} {d : DenseConstraintSystem p}
    (h : ∀ i ∈ d.occ, r.Valid i) : d.CoveredBy r := by
  grind [DenseConstraintSystem.CoveredBy, DenseExpr.CoveredBy, denseBICovered, denseBIVars,
    DenseConstraintSystem.mem_occ_of_constraint, DenseConstraintSystem.mem_occ_of_bi]

/-- An occurrence of the collapse output is either a variable of the replacement `E'` or an
    occurrence of the input system. -/
theorem hcOutOcc {d : DenseConstraintSystem p} {E E' : DenseExpr p} {i : VarId}
    (hi : i ∈ ({d with algebraicConstraints :=
        d.algebraicConstraints.map (fun c => if c = E then E' else c)} : DenseConstraintSystem p).occ) :
    i ∈ E'.vars ∨ i ∈ d.occ := by
  rw [hcMemOcc] at hi
  rcases hi with ⟨c', hc', hic⟩ | ⟨bi, hbi, hbiv⟩
  · have hcase : c' = E' ∨ c' ∈ d.algebraicConstraints := by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      by_cases h : c = E
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simpa [h] using hc)
    rcases hcase with rfl | hcs
    · exact Or.inl hic
    · exact Or.inr (hcMemOcc.2 (Or.inl ⟨c', hcs, hic⟩))
  · exact Or.inr (hcMemOcc.2 (Or.inr ⟨bi, hbi, hbiv⟩))

/-! ## The full collapse bundle (extends + coverage + correctness) at the minted registry -/

/-- The complete `ofExtending` obligation bundle for one accepted collapse: mint `invVar`
    (`powdrId? = none`, so `isInput` is preserved pointwise), extend the registry, and combine coverage
    of the output/derivations with `dense_collapse_correct`. Both `tryOne`/`tryOneSq` discharge only
    the pure structural hypotheses and call this. -/
theorem dense_collapse_bundle [Fact p.Prime] (reg : VarRegistry) (invVar : OutputVariable)
    (hpv : invVar.powdrId? = none) (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (E denom rest : DenseExpr p) (D : List VarId)
    (reasg : (VarId → ZMod p) → ZMod p → (VarId → ZMod p)) (hcov : d.CoveredBy reg)
    (hE : E ∈ d.algebraicConstraints)
    (hagree : ∀ (denv : VarId → ZMod p) (w : ZMod p) (v : VarId), v ∉ D → reasg denv w v = denv v)
    (hEeq : ∀ (denv : VarId → ZMod p) (w : ZMod p),
      E.eval (reasg denv w) = denom.eval denv * w + rest.eval denv)
    (hbyte : ∀ denv, d.satisfies bs denv → denom.eval denv = 0 → rest.eval denv = 0)
    (hfresh : denseIsFresh reg d invVar = true)
    (hDonce : ∀ dw ∈ D, ∀ c ∈ d.algebraicConstraints, dw ∈ c.vars → c = E)
    (hDbus : ∀ dw ∈ D, ∀ bi ∈ d.busInteractions,
      dw ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, dw ∉ e.vars)
    (hrest_sub : ∀ x ∈ rest.vars, x ∈ d.occ) (hden_sub : ∀ x ∈ denom.vars, x ∈ d.occ)
    (hden_pow : ∀ x ∈ denom.vars, reg.isInput x = true)
    (hrest_pow : ∀ x ∈ rest.vars, reg.isInput x = true) :
    reg.Extends (reg.register invVar).1 ∧
    ({d with algebraicConstraints :=
        d.algebraicConstraints.map (fun c => if c = E then
          (DenseExpr.add (DenseExpr.mul denom (DenseExpr.var (reg.register invVar).2)) rest)
          else c)} : DenseConstraintSystem p).CoveredBy (reg.register invVar).1 ∧
    DenseDerivations.CoveredBy (reg.register invVar).1
      [((reg.register invVar).2,
        DenseComputationMethod.quotientOrZero (DenseExpr.mul (DenseExpr.const (-1)) rest) denom)] ∧
    DensePassCorrect (reg.register invVar).1.isInput d
      ({d with algebraicConstraints :=
        d.algebraicConstraints.map (fun c => if c = E then
          (DenseExpr.add (DenseExpr.mul denom (DenseExpr.var (reg.register invVar).2)) rest)
          else c)})
      [((reg.register invVar).2,
        DenseComputationMethod.quotientOrZero (DenseExpr.mul (DenseExpr.const (-1)) rest) denom)] bs := by
  have hext : reg.Extends (reg.register invVar).1 := VarRegistry.register_extends reg invVar
  have hii : ∀ i, (reg.register invVar).1.isInput i = reg.isInput i := hcRegisterIsInputEq reg invVar hpv
  have hinv_fresh : (reg.register invVar).2 ∉ d.occ := denseIsFresh_notMem hcov hfresh
  have hinv_id : (reg.register invVar).1.isInput (reg.register invVar).2 = false := by
    show ((reg.register invVar).1.resolve (reg.register invVar).2).powdrId?.isSome = false
    rw [VarRegistry.register_resolve reg invVar, hpv]; rfl
  have hden_pow1 : ∀ x ∈ denom.vars, (reg.register invVar).1.isInput x = true :=
    fun x hx => by rw [hii x]; exact hden_pow x hx
  have hrest_pow1 : ∀ x ∈ rest.vars, (reg.register invVar).1.isInput x = true :=
    fun x hx => by rw [hii x]; exact hrest_pow x hx
  have hcorrect := dense_collapse_correct (reg.register invVar).1.isInput d bs E denom rest D
    (reg.register invVar).2 reasg hE hagree hEeq hbyte hinv_fresh hinv_id hDonce hDbus
    hrest_sub hden_sub hden_pow1 hrest_pow1
  have hEvalid : ∀ i ∈ (DenseExpr.add (DenseExpr.mul denom (DenseExpr.var (reg.register invVar).2))
        rest).vars, (reg.register invVar).1.Valid i := by
    intro i hi
    simp only [DenseExpr.vars, List.mem_append, List.mem_singleton] at hi
    rcases hi with (hd | hinv) | hr
    · exact hext.valid (DenseConstraintSystem.occ_valid hcov i (hden_sub i hd))
    · subst hinv; exact VarRegistry.register_valid reg invVar
    · exact hext.valid (DenseConstraintSystem.occ_valid hcov i (hrest_sub i hr))
  have hrestCov : rest.CoveredBy (reg.register invVar).1 :=
    fun i hi => hext.valid (DenseConstraintSystem.occ_valid hcov i (hrest_sub i hi))
  have hdenCov : denom.CoveredBy (reg.register invVar).1 :=
    fun i hi => hext.valid (DenseConstraintSystem.occ_valid hcov i (hden_sub i hi))
  refine ⟨hext, ?_, ?_, hcorrect⟩
  · refine hcCoveredByOfOcc (fun i hi => ?_)
    rcases hcOutOcc hi with he | hd
    · exact hEvalid i he
    · exact hext.valid (DenseConstraintSystem.occ_valid hcov i hd)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    refine ⟨VarRegistry.register_valid reg invVar, ?_⟩
    show (DenseComputationMethod.quotientOrZero (DenseExpr.mul (DenseExpr.const (-1)) rest) denom).CoveredBy
      (reg.register invVar).1
    exact ⟨DenseExpr.coveredBy_mul.mpr ⟨DenseExpr.coveredBy_const _ (-1), hrestCov⟩, hdenCov⟩

/-! ## The occurrence-code scan (`denseHcScan`)

The discovery layer reads every claim it makes off the code array, so three facts about it carry the
pass: a `2 + i` code means the variable occurs in no bus interaction (`denseHcScan_bus`) and in no
constraint entry but `i` (`denseHcScan_unique`), and a `0` code means it does not occur at all
(`denseHcScan_zero`). Out-of-range indices read the `0` default, so a nonzero code is in range and
the `setIfInBounds` writes that built it landed.

`Array.getD` unfolds to a `dite` on the bound, which `split` would case on instead of on the mark's
own tests — hence `by_cases` on the `Bool` conditions plus the `hc*_var` equations throughout. -/

private theorem hcGetD_set_self {A : Array Nat} {i x dflt : Nat} (h : i < A.size) :
    (A.setIfInBounds i x).getD i dflt = x := by
  simp [Array.getD, Array.setIfInBounds, h]

private theorem hcGetD_set_ne {A : Array Nat} {i j x dflt : Nat} (h : j ≠ i) :
    (A.setIfInBounds i x).getD j dflt = A.getD j dflt := by
  simp only [Array.getD, Array.setIfInBounds]
  split <;> simp [Array.getElem_set, Ne.symm h]

private theorem hcGetD_of_ge {A : Array Nat} {i dflt : Nat} (h : A.size ≤ i) :
    A.getD i dflt = dflt := by
  simp [Array.getD, Nat.not_lt.mpr h]

/-- In range the default is irrelevant: `denseHcCsMark` reads with `1`, its users with `0`. -/
private theorem hcGetD_dflt {A : Array Nat} {i d1 d2 : Nat} (h : i < A.size) :
    A.getD i d1 = A.getD i d2 := by
  simp [Array.getD, h]

private theorem hcLt_of_ne_zero {A : Array Nat} {i : Nat} (h : A.getD i 0 ≠ 0) : i < A.size := by
  by_contra hge
  exact h (hcGetD_of_ge (Nat.le_of_not_lt hge))

private theorem hcBusMark_var (w : VarId) (A : Array Nat) :
    denseHcBusMark (p := p) (.var w) A =
      (if (A.getD w.index 1 == 1) = true then A else A.setIfInBounds w.index 1) := rfl

private theorem hcCsMark_var (i : Nat) (w : VarId) (A : Array Nat) :
    denseHcCsMark (p := p) i (.var w) A =
      (if (A.getD w.index 1 == 0) = true then A.setIfInBounds w.index (2 + i)
       else if (A.getD w.index 1 == 2 + i || A.getD w.index 1 == 1) = true then A
       else A.setIfInBounds w.index 1) := rfl

/-! ### The bus phase: every bus variable ends at code `1` -/

private theorem hcBusMark_size (e : DenseExpr p) (A : Array Nat) :
    (denseHcBusMark e A).size = A.size := by
  induction e generalizing A with
  | const c => rfl
  | var w =>
      rw [hcBusMark_var]
      by_cases h1 : (A.getD w.index 1 == 1) = true
      · rw [if_pos h1]
      · rw [if_neg h1]; simp
  | add a b iha ihb => simp only [denseHcBusMark, ihb, iha]
  | mul a b iha ihb => simp only [denseHcBusMark, ihb, iha]

private theorem hcBusMarkL_size (es : List (DenseExpr p)) (A : Array Nat) :
    (denseHcBusMarkL es A).size = A.size := by
  induction es generalizing A with
  | nil => rfl
  | cons e es ih => simp only [denseHcBusMarkL, ih, hcBusMark_size]

private theorem hcBusScan_size (bis : List (BusInteraction (DenseExpr p))) (A : Array Nat) :
    (denseHcBusScan bis A).size = A.size := by
  induction bis generalizing A with
  | nil => rfl
  | cons bi rest ih => simp only [denseHcBusScan, ih, hcBusMarkL_size, hcBusMark_size]

/-- Code `1` is absorbing in the bus phase. -/
private theorem hcBusMark_one (e : DenseExpr p) (A : Array Nat) (v : VarId)
    (h : A.getD v.index 0 = 1) : (denseHcBusMark e A).getD v.index 0 = 1 := by
  induction e generalizing A with
  | const c => exact h
  | var w =>
      have hlt : v.index < A.size := hcLt_of_ne_zero (by rw [h]; omega)
      rw [hcBusMark_var]
      by_cases hvw : v.index = w.index
      · have h1 : (A.getD w.index 1 == 1) = true := by
          rw [← hvw, hcGetD_dflt hlt (d2 := 0), h]; simp
        rw [if_pos h1]; exact h
      · by_cases h1 : (A.getD w.index 1 == 1) = true
        · rw [if_pos h1]; exact h
        · rw [if_neg h1, hcGetD_set_ne hvw]; exact h
  | add a b iha ihb => exact ihb _ (iha _ h)
  | mul a b iha ihb => exact ihb _ (iha _ h)

private theorem hcBusMarkL_one (es : List (DenseExpr p)) (A : Array Nat) (v : VarId)
    (h : A.getD v.index 0 = 1) : (denseHcBusMarkL es A).getD v.index 0 = 1 := by
  induction es generalizing A with
  | nil => exact h
  | cons e es ih => exact ih _ (hcBusMark_one e A v h)

private theorem hcBusScan_one (bis : List (BusInteraction (DenseExpr p))) (A : Array Nat)
    (v : VarId) (h : A.getD v.index 0 = 1) : (denseHcBusScan bis A).getD v.index 0 = 1 := by
  induction bis generalizing A with
  | nil => exact h
  | cons bi rest ih => exact ih _ (hcBusMarkL_one _ _ v (hcBusMark_one _ _ v h))

/-- An occurrence in a marked expression ends at code `1`. -/
private theorem hcBusMark_hit (e : DenseExpr p) (A : Array Nat) (v : VarId) (hv : v ∈ e.vars)
    (hlt : v.index < A.size) : (denseHcBusMark e A).getD v.index 0 = 1 := by
  induction e generalizing A with
  | const c => simp [DenseExpr.vars] at hv
  | var w =>
      simp only [DenseExpr.vars, List.mem_singleton] at hv
      subst hv
      rw [hcBusMark_var]
      by_cases h1 : (A.getD v.index 1 == 1) = true
      · rw [if_pos h1, hcGetD_dflt hlt (d2 := 1)]; simpa using h1
      · rw [if_neg h1]; exact hcGetD_set_self hlt
  | add a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at hv
      simp only [denseHcBusMark]
      rcases hv with ha | hb
      · exact hcBusMark_one b _ v (iha A ha hlt)
      · exact ihb _ hb (by rw [hcBusMark_size]; exact hlt)
  | mul a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at hv
      simp only [denseHcBusMark]
      rcases hv with ha | hb
      · exact hcBusMark_one b _ v (iha A ha hlt)
      · exact ihb _ hb (by rw [hcBusMark_size]; exact hlt)

private theorem hcBusMarkL_hit (es : List (DenseExpr p)) (A : Array Nat) (v : VarId)
    (e : DenseExpr p) (he : e ∈ es) (hv : v ∈ e.vars) (hlt : v.index < A.size) :
    (denseHcBusMarkL es A).getD v.index 0 = 1 := by
  induction es generalizing A with
  | nil => simp at he
  | cons e0 es ih =>
      simp only [denseHcBusMarkL]
      rcases List.mem_cons.1 he with rfl | hes
      · exact hcBusMarkL_one _ _ v (hcBusMark_hit _ A v hv hlt)
      · exact ih _ hes (by rw [hcBusMark_size]; exact hlt)

private theorem hcBusScan_hit (bis : List (BusInteraction (DenseExpr p))) (A : Array Nat)
    (v : VarId) (bi : BusInteraction (DenseExpr p)) (hbi : bi ∈ bis) (hv : v ∈ denseBIVars bi)
    (hlt : v.index < A.size) : (denseHcBusScan bis A).getD v.index 0 = 1 := by
  induction bis generalizing A with
  | nil => simp at hbi
  | cons bi0 rest ih =>
      simp only [denseHcBusScan]
      rcases List.mem_cons.1 hbi with rfl | hrest
      · refine hcBusScan_one _ _ v ?_
        simp only [denseBIVars, List.mem_append, List.mem_flatMap] at hv
        rcases hv with hm | ⟨e, he, hve⟩
        · exact hcBusMarkL_one _ _ v (hcBusMark_hit _ A v hm hlt)
        · exact hcBusMarkL_hit _ _ v e he hve (by rw [hcBusMark_size]; exact hlt)
      · exact ih _ hrest (by rw [hcBusMarkL_size, hcBusMark_size]; exact hlt)

/-! ### The constraint phase: a `2 + i` code names the one entry the variable occurs in -/

private theorem hcCsMark_size (i : Nat) (e : DenseExpr p) (A : Array Nat) :
    (denseHcCsMark i e A).size = A.size := by
  induction e generalizing A with
  | const c => rfl
  | var w =>
      rw [hcCsMark_var]
      by_cases h0 : (A.getD w.index 1 == 0) = true
      · rw [if_pos h0]; simp
      · rw [if_neg h0]
        by_cases hk : (A.getD w.index 1 == 2 + i || A.getD w.index 1 == 1) = true
        · rw [if_pos hk]
        · rw [if_neg hk]; simp
  | add a b iha ihb => simp only [denseHcCsMark, ihb, iha]
  | mul a b iha ihb => simp only [denseHcCsMark, ihb, iha]

private theorem hcCsScan_size (k : Nat) (l : List (DenseExpr p)) (A : Array Nat) :
    (denseHcCsScan k l A).size = A.size := by
  induction l generalizing k A with
  | nil => rfl
  | cons c cs ih => simp only [denseHcCsScan, ih, hcCsMark_size]

/-- Code `1` is absorbing in the constraint phase too. -/
private theorem hcCsMark_one (i : Nat) (e : DenseExpr p) (A : Array Nat) (v : VarId)
    (h : A.getD v.index 0 = 1) : (denseHcCsMark i e A).getD v.index 0 = 1 := by
  induction e generalizing A with
  | const c => exact h
  | var w =>
      have hlt : v.index < A.size := hcLt_of_ne_zero (by rw [h]; omega)
      rw [hcCsMark_var]
      by_cases hvw : v.index = w.index
      · have hc : A.getD w.index 1 = 1 := by rw [← hvw, hcGetD_dflt hlt (d2 := 0)]; exact h
        rw [if_neg (by rw [hc]; simp), if_pos (by rw [hc]; simp)]
        exact h
      · by_cases h0 : (A.getD w.index 1 == 0) = true
        · rw [if_pos h0, hcGetD_set_ne hvw]; exact h
        · rw [if_neg h0]
          by_cases hk : (A.getD w.index 1 == 2 + i || A.getD w.index 1 == 1) = true
          · rw [if_pos hk]; exact h
          · rw [if_neg hk, hcGetD_set_ne hvw]; exact h
  | add a b iha ihb => exact ihb _ (iha _ h)
  | mul a b iha ihb => exact ihb _ (iha _ h)

private theorem hcCsScan_one (k : Nat) (l : List (DenseExpr p)) (A : Array Nat) (v : VarId)
    (h : A.getD v.index 0 = 1) : (denseHcCsScan k l A).getD v.index 0 = 1 := by
  induction l generalizing k A with
  | nil => exact h
  | cons c cs ih => exact ih _ _ (hcCsMark_one k c A v h)

/-- The set `{2 + m, 1}` is closed under every mark: a mark at a different entry demotes `2 + m` to
    `1`, which is in the set, and `1` is absorbing. This is what pins a variable's final code to the
    entry that first claimed it. -/
private theorem hcCsMark_keep (i m : Nat) (e : DenseExpr p) (A : Array Nat) (v : VarId)
    (h : A.getD v.index 0 = 2 + m ∨ A.getD v.index 0 = 1) :
    (denseHcCsMark i e A).getD v.index 0 = 2 + m ∨ (denseHcCsMark i e A).getD v.index 0 = 1 := by
  induction e generalizing A with
  | const c => exact h
  | var w =>
      have hne0 : A.getD v.index 0 ≠ 0 := by rcases h with h | h <;> rw [h] <;> omega
      have hlt : v.index < A.size := hcLt_of_ne_zero hne0
      rw [hcCsMark_var]
      by_cases hvw : v.index = w.index
      · have hc : A.getD w.index 1 = A.getD v.index 0 := by
          rw [← hvw, hcGetD_dflt hlt (d2 := 0)]
        rw [if_neg (by rw [hc]; simpa using hne0)]
        by_cases hk : (A.getD w.index 1 == 2 + i || A.getD w.index 1 == 1) = true
        · rw [if_pos hk]; exact h
        · rw [if_neg hk, ← hvw]; exact Or.inr (hcGetD_set_self hlt)
      · by_cases h0 : (A.getD w.index 1 == 0) = true
        · rw [if_pos h0, hcGetD_set_ne hvw]; exact h
        · rw [if_neg h0]
          by_cases hk : (A.getD w.index 1 == 2 + i || A.getD w.index 1 == 1) = true
          · rw [if_pos hk]; exact h
          · rw [if_neg hk, hcGetD_set_ne hvw]; exact h
  | add a b iha ihb => exact ihb _ (iha _ h)
  | mul a b iha ihb => exact ihb _ (iha _ h)

private theorem hcCsScan_keep (m : Nat) (l : List (DenseExpr p)) (k : Nat) (A : Array Nat)
    (v : VarId) (h : A.getD v.index 0 = 2 + m ∨ A.getD v.index 0 = 1) :
    (denseHcCsScan k l A).getD v.index 0 = 2 + m ∨ (denseHcCsScan k l A).getD v.index 0 = 1 := by
  induction l generalizing k A with
  | nil => exact h
  | cons c cs ih => exact ih _ _ (hcCsMark_keep k m c A v h)

/-- An occurrence in entry `i` leaves the variable at `2 + i` or `1`. -/
private theorem hcCsMark_hit (i : Nat) (e : DenseExpr p) (A : Array Nat) (v : VarId)
    (hv : v ∈ e.vars) (hlt : v.index < A.size) :
    (denseHcCsMark i e A).getD v.index 0 = 2 + i ∨ (denseHcCsMark i e A).getD v.index 0 = 1 := by
  induction e generalizing A with
  | const c => simp [DenseExpr.vars] at hv
  | var w =>
      simp only [DenseExpr.vars, List.mem_singleton] at hv
      subst hv
      rw [hcCsMark_var]
      by_cases h0 : (A.getD v.index 1 == 0) = true
      · rw [if_pos h0]; exact Or.inl (hcGetD_set_self hlt)
      · rw [if_neg h0]
        by_cases hk : (A.getD v.index 1 == 2 + i || A.getD v.index 1 == 1) = true
        · rw [if_pos hk, hcGetD_dflt hlt (d2 := 1)]
          have hk' : A.getD v.index 1 = 2 + i ∨ A.getD v.index 1 = 1 := by simpa using hk
          exact hk'.imp id id
        · rw [if_neg hk]; exact Or.inr (hcGetD_set_self hlt)
  | add a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at hv
      simp only [denseHcCsMark]
      rcases hv with ha | hb
      · exact hcCsMark_keep i i b _ v (iha A ha hlt)
      · exact ihb _ hb (by rw [hcCsMark_size]; exact hlt)
  | mul a b iha ihb =>
      simp only [DenseExpr.vars, List.mem_append] at hv
      simp only [denseHcCsMark]
      rcases hv with ha | hb
      · exact hcCsMark_keep i i b _ v (iha A ha hlt)
      · exact ihb _ hb (by rw [hcCsMark_size]; exact hlt)

/-- **Uniqueness.** A final code of `2 + i` forces every entry containing the variable to be `i`. -/
private theorem hcCsScan_unique (v : VarId) :
    ∀ (l : List (DenseExpr p)) (k : Nat) (A : Array Nat) (i j : Nat) (c : DenseExpr p),
      (denseHcCsScan k l A).getD v.index 0 = 2 + i → l[j]? = some c → v ∈ c.vars → i = k + j := by
  intro l
  induction l with
  | nil => intro _ _ _ j _ _ hj _; simp at hj
  | cons c0 cs ih =>
      intro k A i j c hfin hj hv
      have hlt : v.index < A.size := by
        have h1 := hcLt_of_ne_zero (A := denseHcCsScan k (c0 :: cs) A) (i := v.index)
          (by rw [hfin]; omega)
        rwa [hcCsScan_size] at h1
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          have hkeep := hcCsScan_keep k cs (k + 1) (denseHcCsMark k c0 A) v
            (hcCsMark_hit k c0 A v hv hlt)
          simp only [denseHcCsScan] at hfin
          rcases hkeep with h | h <;> rw [hfin] at h <;> omega
      | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          simp only [denseHcCsScan] at hfin
          have h1 := ih (k + 1) (denseHcCsMark k c0 A) i j c hfin hj hv
          omega

/-- An occurrence anywhere in the scanned entries leaves a nonzero code. -/
private theorem hcCsScan_nonzero (v : VarId) :
    ∀ (l : List (DenseExpr p)) (k : Nat) (A : Array Nat) (c : DenseExpr p),
      c ∈ l → v ∈ c.vars → v.index < A.size → (denseHcCsScan k l A).getD v.index 0 ≠ 0 := by
  intro l
  induction l with
  | nil => intro _ _ _ hc; simp at hc
  | cons c0 cs ih =>
      intro k A c hc hv hlt
      simp only [denseHcCsScan]
      rcases List.mem_cons.1 hc with rfl | hcs
      · have hkeep := hcCsScan_keep k cs (k + 1) (denseHcCsMark k c A) v
          (hcCsMark_hit k c A v hv hlt)
        rcases hkeep with h | h <;> rw [h] <;> omega
      · exact ih (k + 1) (denseHcCsMark k c0 A) c hcs hv (by rw [hcCsMark_size]; exact hlt)

/-! ### The three facts the pass consumes -/

theorem denseHcScan_size (nvars : Nat) (d : DenseConstraintSystem p) :
    (denseHcScan nvars d).size = nvars := by
  simp only [denseHcScan, hcCsScan_size, hcBusScan_size, Array.size_replicate]

/-- A `2 + i` code names the only constraint entry the variable occurs in. -/
theorem denseHcScan_unique {nvars : Nat} {d : DenseConstraintSystem p} {v : VarId} {i j : Nat}
    {c : DenseExpr p} (h : (denseHcScan nvars d).getD v.index 0 = 2 + i)
    (hj : d.algebraicConstraints[j]? = some c) (hv : v ∈ c.vars) : i = j := by
  simpa using hcCsScan_unique v d.algebraicConstraints 0 _ i j c h hj hv

/-- A `2 + i` code rules out every bus occurrence: a bus variable is left at `1`, and the constraint
    phase cannot undo that. -/
theorem denseHcScan_bus {nvars : Nat} {d : DenseConstraintSystem p} {v : VarId} {i : Nat}
    (h : (denseHcScan nvars d).getD v.index 0 = 2 + i) {bi : BusInteraction (DenseExpr p)}
    (hbi : bi ∈ d.busInteractions) : v ∉ denseBIVars bi := by
  intro hv
  have hlt : v.index < nvars := by
    have h1 := hcLt_of_ne_zero (A := denseHcScan nvars d) (i := v.index) (by rw [h]; omega)
    rwa [denseHcScan_size] at h1
  have hbus : (denseHcBusScan d.busInteractions (Array.replicate nvars 0)).getD v.index 0 = 1 :=
    hcBusScan_hit _ _ v bi hbi hv (by rw [Array.size_replicate]; exact hlt)
  have h1 : (denseHcScan nvars d).getD v.index 0 = 1 := by
    simp only [denseHcScan]; exact hcCsScan_one _ _ _ v hbus
  rw [h] at h1; omega

/-- A `0` code rules out every occurrence — exactly the `d.occ` test `denseIsFresh` runs. -/
theorem denseHcScan_zero {nvars : Nat} {d : DenseConstraintSystem p} {v : VarId}
    (h : (denseHcScan nvars d).getD v.index 0 = 0) (hlt : v.index < nvars) : v ∉ d.occ := by
  intro hocc
  rcases hcMemOcc.1 hocc with ⟨c, hc, hvc⟩ | ⟨bi, hbi, hvbi⟩
  · exact hcCsScan_nonzero v d.algebraicConstraints 0
      (denseHcBusScan d.busInteractions (Array.replicate nvars 0)) c hc hvc
      (by rw [hcBusScan_size, Array.size_replicate]; exact hlt)
      (by simpa only [denseHcScan] using h)
  · have hbus : (denseHcBusScan d.busInteractions (Array.replicate nvars 0)).getD v.index 0 = 1 :=
      hcBusScan_hit _ _ v bi hbi hvbi (by rw [Array.size_replicate]; exact hlt)
    have h1 : (denseHcScan nvars d).getD v.index 0 = 1 := by
      simp only [denseHcScan]; exact hcCsScan_one _ _ _ v hbus
    rw [h] at h1; omega

/-! ## The candidate targets, their witnesses, and the indexed replacement -/

/-- `denseHcPick` reports constraint entries at the indices it pairs them with. -/
private theorem hcPick_spec :
    ∀ (l : List (DenseExpr p)) (is : List Nat) (j i : Nat) (E : DenseExpr p),
      (i, E) ∈ denseHcPick j is l → ∃ k, i = j + k ∧ l[k]? = some E := by
  intro l
  induction l with
  | nil => intro is j i E hmem; simp [denseHcPick] at hmem
  | cons c cs ih =>
      intro is j i E hmem
      cases is with
      | nil => simp [denseHcPick] at hmem
      | cons i0 is' =>
          simp only [denseHcPick] at hmem
          by_cases hij : (i0 == j) = true
          · rw [if_pos hij] at hmem
            rcases List.mem_cons.1 hmem with heq | htl
            · simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact ⟨0, by simpa using eq_of_beq hij, rfl⟩
            · obtain ⟨k, rfl, hk⟩ := ih is' (j + 1) i E htl
              exact ⟨k + 1, by omega, by simpa using hk⟩
          · rw [if_neg hij] at hmem
            obtain ⟨k, rfl, hk⟩ := ih (i0 :: is') (j + 1) i E hmem
            exact ⟨k + 1, by omega, by simpa using hk⟩

private theorem hcWitsGo_var (st : Array Nat) (code : Nat) (w : VarId) (acc : List VarId) :
    denseHcWitsGo (p := p) st code (.var w) acc =
      (if (st.getD w.index 0 == code && !acc.contains w) = true then w :: acc else acc) := rfl

private theorem hcWitsGo_mem (st : Array Nat) (code : Nat) :
    ∀ (E : DenseExpr p) (acc : List VarId) (v : VarId), v ∈ denseHcWitsGo st code E acc →
      v ∈ acc ∨ (st.getD v.index 0 = code ∧ v ∈ E.vars) := by
  intro E
  induction E with
  | const c => intro acc v hv; exact Or.inl hv
  | var w =>
      intro acc v hv
      rw [hcWitsGo_var] at hv
      by_cases hc : (st.getD w.index 0 == code && !acc.contains w) = true
      · rw [if_pos hc] at hv
        rcases List.mem_cons.1 hv with rfl | hacc
        · refine Or.inr ⟨?_, by simp [DenseExpr.vars]⟩
          rw [Bool.and_eq_true] at hc
          simpa using hc.1
        · exact Or.inl hacc
      · rw [if_neg hc] at hv; exact Or.inl hv
  | add a b iha ihb =>
      intro acc v hv
      simp only [denseHcWitsGo] at hv
      rcases ihb _ v hv with h | ⟨hcode, hb⟩
      · rcases iha acc v h with h' | ⟨hcode, ha⟩
        · exact Or.inl h'
        · exact Or.inr ⟨hcode, by simp [DenseExpr.vars, ha]⟩
      · exact Or.inr ⟨hcode, by simp [DenseExpr.vars, hb]⟩
  | mul a b iha ihb =>
      intro acc v hv
      simp only [denseHcWitsGo] at hv
      rcases ihb _ v hv with h | ⟨hcode, hb⟩
      · rcases iha acc v h with h' | ⟨hcode, ha⟩
        · exact Or.inl h'
        · exact Or.inr ⟨hcode, by simp [DenseExpr.vars, ha]⟩
      · exact Or.inr ⟨hcode, by simp [DenseExpr.vars, hb]⟩

private theorem hcWitsGo_nodup (st : Array Nat) (code : Nat) :
    ∀ (E : DenseExpr p) (acc : List VarId), acc.Nodup → (denseHcWitsGo st code E acc).Nodup := by
  intro E
  induction E with
  | const c => intro acc h; exact h
  | var w =>
      intro acc h
      rw [hcWitsGo_var]
      by_cases hc : (st.getD w.index 0 == code && !acc.contains w) = true
      · rw [if_pos hc]
        have hw : w ∉ acc := by
          rw [Bool.and_eq_true] at hc
          simpa [List.contains_iff_mem] using hc.2
        exact List.nodup_cons.2 ⟨hw, h⟩
      · rw [if_neg hc]; exact h
  | add a b iha ihb => intro acc h; exact ihb _ (iha acc h)
  | mul a b iha ihb => intro acc h; exact ihb _ (iha acc h)

private theorem hcWits_code {st : Array Nat} {idx : Nat} {E : DenseExpr p} {v : VarId}
    (h : v ∈ denseHcWits st idx E) : st.getD v.index 0 = 2 + idx := by
  rcases hcWitsGo_mem st (2 + idx) E [] v (by simpa [denseHcWits] using h) with h' | ⟨hc, _⟩
  · simp at h'
  · exact hc

private theorem hcWits_mem {st : Array Nat} {idx : Nat} {E : DenseExpr p} {v : VarId}
    (h : v ∈ denseHcWits st idx E) : v ∈ E.vars := by
  rcases hcWitsGo_mem st (2 + idx) E [] v (by simpa [denseHcWits] using h) with h' | ⟨_, hm⟩
  · simp at h'
  · exact hm

private theorem hcWits_nodup (st : Array Nat) (idx : Nat) (E : DenseExpr p) :
    (denseHcWits st idx E).Nodup := by
  simpa [denseHcWits] using hcWitsGo_nodup st (2 + idx) E [] List.nodup_nil

/-- With `E` at index `idx` and nowhere else, replacing at the index is replacing every copy — so
    the collapse transport (`dense_collapse_bundle`) applies to the indexed output unchanged. -/
private theorem hcSet_eq_map {α : Type} [DecidableEq α] :
    ∀ (l : List α) (idx : Nat) (E E' : α), l[idx]? = some E →
      (∀ j, j ≠ idx → l[j]? ≠ some E) →
      l.set idx E' = l.map (fun c => if c = E then E' else c) := by
  intro l
  induction l with
  | nil => intro idx E E' hidx _; simp at hidx
  | cons a t ih =>
      intro idx E E' hidx huniq
      cases idx with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hidx
          subst hidx
          have htail : t.map (fun c => if c = a then E' else c) = t := by
            conv_rhs => rw [← List.map_id t]
            refine List.map_congr_left (fun x hx => ?_)
            obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
            have hne : x ≠ a := by
              intro hxa
              exact huniq (k + 1) (by omega) (by simpa [hxa] using hk)
            simp [hne]
          simp [List.set, htail]
      | succ k =>
          simp only [List.getElem?_cons_succ] at hidx
          have hane : a ≠ E := by
            intro hae
            exact huniq 0 (by omega) (by simp [hae])
          have huniq' : ∀ j, j ≠ k → t[j]? ≠ some E :=
            fun j hj => huniq (j + 1) (by omega)
          simp only [List.set, List.map_cons, if_neg hane]
          rw [ih k E E' hidx huniq']

/-! ## The bounds map over the wanted interactions -/

/-- **Bounds soundness.** `denseHcBounds` is `denseAddAll` over a sublist of the interactions, so
    every bound it stores is justified exactly as `denseBuild`'s are — the `want` marks are an
    untrusted filter that can only lose bounds. -/
theorem denseHcBounds_sound (bs : BusSemantics p) (facts : BusFacts p bs) (nvars : Nat)
    (want : List VarId) (bis : List (BusInteraction (DenseExpr p))) (i : VarId) (b : Nat)
    (hlk : (denseHcBounds bs facts nvars want bis)[i]? = some b) (denv : VarId → ZMod p)
    (hbus : ∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.accepts (denseBIEval bi denv)) : (denv i).val < b := by
  unfold denseHcBounds at hlk
  split at hlk
  · rw [Std.HashMap.getElem?_empty] at hlk; exact absurd hlk (by simp)
  · exact denseAddAll_soundAt bs facts denv _
      (fun bi hbi => hbus bi (List.mem_of_mem_filter hbi)) ∅ (DenseBMSoundAt.empty denv) i b hlk

/-! ## Freshness from the occurrence codes -/

/-- The array-served freshness test is the `d.occ` test: a `0` code means no occurrence. -/
private theorem hcFresh_isFresh {reg : VarRegistry} {d : DenseConstraintSystem p} {v : OutputVariable}
    (h : denseHcFresh reg (denseHcScan reg.byId.size d) v = true) : denseIsFresh reg d v = true := by
  unfold denseHcFresh at h
  unfold denseIsFresh
  cases hlook : reg.idOf? v with
  | none => simp
  | some i =>
      rw [hlook] at h
      simp only [beq_iff_eq] at h
      have hlt : i.index < reg.byId.size := VarRegistry.valid_of_idOf hlook
      have hnot : i ∉ d.occ := denseHcScan_zero h hlt
      show (!d.occ.contains i) = true
      simp [hnot]

/-! ## The collapse attempt (correctness) -/

/-- The `ofExtending` bundle for an accepted collapse at a known index: with the target unique in
    the list, the indexed replacement is the by-value one, and `dense_collapse_bundle` transports
    it. -/
theorem denseHcAccept_correct [Fact p.Prime] (reg : VarRegistry) (invVar : OutputVariable)
    (hpv : invVar.powdrId? = none) (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (E denom rest : DenseExpr p) (D : List VarId) (idx : Nat)
    (reasg : (VarId → ZMod p) → ZMod p → (VarId → ZMod p)) (hcov : d.CoveredBy reg)
    (hidx : d.algebraicConstraints[idx]? = some E)
    (huniq : ∀ j, j ≠ idx → d.algebraicConstraints[j]? ≠ some E)
    (hagree : ∀ (denv : VarId → ZMod p) (w : ZMod p) (v : VarId), v ∉ D → reasg denv w v = denv v)
    (hEeq : ∀ (denv : VarId → ZMod p) (w : ZMod p),
      E.eval (reasg denv w) = denom.eval denv * w + rest.eval denv)
    (hbyte : ∀ denv, d.satisfies bs denv → denom.eval denv = 0 → rest.eval denv = 0)
    (hfresh : denseIsFresh reg d invVar = true)
    (hDonce : ∀ dw ∈ D, ∀ c ∈ d.algebraicConstraints, dw ∈ c.vars → c = E)
    (hDbus : ∀ dw ∈ D, ∀ bi ∈ d.busInteractions,
      dw ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, dw ∉ e.vars)
    (hrest_sub : ∀ x ∈ rest.vars, x ∈ d.occ) (hden_sub : ∀ x ∈ denom.vars, x ∈ d.occ)
    (hden_pow : ∀ x ∈ denom.vars, reg.isInput x = true)
    (hrest_pow : ∀ x ∈ rest.vars, reg.isInput x = true) :
    reg.Extends (denseHcAccept reg d idx invVar denom rest).1 ∧
      (denseHcAccept reg d idx invVar denom rest).2.1.CoveredBy
        (denseHcAccept reg d idx invVar denom rest).1 ∧
      DenseDerivations.CoveredBy (denseHcAccept reg d idx invVar denom rest).1
        (denseHcAccept reg d idx invVar denom rest).2.2 ∧
      DensePassCorrect (denseHcAccept reg d idx invVar denom rest).1.isInput d
        (denseHcAccept reg d idx invVar denom rest).2.1
        (denseHcAccept reg d idx invVar denom rest).2.2 bs := by
  have hset : d.algebraicConstraints.set idx
      (DenseExpr.add (DenseExpr.mul denom (DenseExpr.var (reg.register invVar).2)) rest)
      = d.algebraicConstraints.map (fun c => if c = E then
          DenseExpr.add (DenseExpr.mul denom (DenseExpr.var (reg.register invVar).2)) rest
          else c) :=
    hcSet_eq_map _ idx E _ hidx huniq
  have hb := dense_collapse_bundle reg invVar hpv d bs E denom rest D reasg hcov
    (List.mem_of_getElem? hidx) hagree hEeq hbyte hfresh hDonce hDbus hrest_sub hden_sub
    hden_pow hrest_pow
  simpa only [denseHcAccept, hset] using hb

set_option maxHeartbeats 1000000 in
/-- One attempt's correctness: whichever shape it accepts, the result is a `DensePassCorrect`
    collapse. The two occurrence obligations come from the code array (`denseHcScan_unique`,
    `denseHcScan_bus`), the bound obligations from `denseHcBounds_sound`. -/
theorem denseHcTry_correct [Fact p.Prime] {bs : BusSemantics p} (facts : BusFacts p bs)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (idx : Nat) (E : DenseExpr p)
    (hcov : d.CoveredBy reg) (hidx : d.algebraicConstraints[idx]? = some E)
    (r : VarRegistry × DenseConstraintSystem p × DenseDerivations p)
    (hr : denseHcTry bs facts reg d (denseHcScan reg.byId.size d) idx E
      (denseHcWits (denseHcScan reg.byId.size d) idx E) = some r) :
    reg.Extends r.1 ∧ r.2.1.CoveredBy r.1 ∧ DenseDerivations.CoveredBy r.1 r.2.2 ∧
      DensePassCorrect r.1.isInput d r.2.1 r.2.2 bs := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set st := denseHcScan reg.byId.size d with hst
  set D := denseHcWits st idx E with hDdef
  set Bm := denseHcBounds bs facts st.size (denseHcWantVars (densePeel D E).1) d.busInteractions
    with hBm
  -- the three occurrence facts, read off the codes
  have hDcode : ∀ v ∈ D, st.getD v.index 0 = 2 + idx := fun v hv => hcWits_code hv
  have hDE : ∀ v ∈ D, v ∈ E.vars := fun v hv => hcWits_mem hv
  have hnd : D.Nodup := hcWits_nodup st idx E
  have hDonce : ∀ dw ∈ D, ∀ c ∈ d.algebraicConstraints, dw ∈ c.vars → c = E := by
    intro dw hdw c hc hdwc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hij : idx = j := denseHcScan_unique (hst ▸ hDcode dw hdw) hj hdwc
    rw [← hij, hidx] at hj
    exact (Option.some.inj hj).symm
  have hDbus : ∀ dw ∈ D, ∀ bi ∈ d.busInteractions,
      dw ∉ bi.multiplicity.vars ∧ ∀ e ∈ bi.payload, dw ∉ e.vars := by
    intro dw hdw bi hbi
    have hnot : dw ∉ denseBIVars bi := denseHcScan_bus (hst ▸ hDcode dw hdw) hbi
    refine ⟨fun hm => hnot ?_, fun e he hme => hnot ?_⟩
    · simp only [denseBIVars, List.mem_append]; exact Or.inl hm
    · simp only [denseBIVars, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨e, he, hme⟩
  -- the bound lookups the certificates make are sound
  have hBmSound : ∀ (a : VarId) (b : Nat), Bm[a]? = some b → ∀ denv, d.satisfies bs denv →
      (denv a).val < b := by
    intro a b hlk denv hsat
    exact denseHcBounds_sound bs facts st.size _ d.busInteractions a b hlk denv hsat.2
  simp only [denseHcTry, ← hBm] at hr
  split_ifs at hr with h2len hrfreeG hrpowG hplain hfreshP hsq hfreshS
  all_goals obtain rfl := Option.some.inj hr
  -- shared framing, common to both shapes
  all_goals (
    have hrfree : ∀ dw ∈ D, dw ∉ (densePeel D E).2.vars :=
      fun dw hd => of_decide_eq_true (List.all_eq_true.1 hrfreeG dw hd)
    have hrest_sub2 : ∀ x ∈ (densePeel D E).2.vars, x ∈ d.occ :=
      fun x hx => DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_getElem? hidx)
        (densePeel_snd_vars D E x hx)
    have huniq : ∀ j, j ≠ idx → d.algebraicConstraints[j]? ≠ some E := by
      intro j hj hjE
      obtain ⟨dw, hdw⟩ : ∃ dw, dw ∈ D := by
        cases hDl : D with
        | nil => rw [hDl] at h2len; simp at h2len
        | cons a t => exact ⟨a, List.mem_cons_self ..⟩
      exact hj (denseHcScan_unique (hst ▸ hDcode dw hdw) hjE (hDE dw hdw)).symm)
  · -- the plain-sum shape
    rw [Bool.and_eq_true] at hplain
    obtain ⟨hbyteOK, hfitG⟩ := hplain
    have hcfree : ∀ c ∈ (densePeel D E).1, ∀ dw ∈ D, dw ∉ c.vars := by
      intro c hc dw hd
      obtain ⟨a, _, hDf, _, _, _⟩ := denseCoeffsByteOK_sound reg Bm D (densePeel D E).1 hbyteOK c hc
      exact hDf dw hd
    have hden_sub2 : ∀ x ∈ (denseSumExpr (densePeel D E).1).vars, x ∈ d.occ := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := denseSumExpr_vars hx
      exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_getElem? hidx)
        (densePeel_fst_vars D E c hc x hxc)
    have hden_pow : ∀ x ∈ (denseSumExpr (densePeel D E).1).vars, reg.isInput x = true := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := denseSumExpr_vars hx
      obtain ⟨a, _, _, hpow, _, _⟩ := denseCoeffsByteOK_sound reg Bm D (densePeel D E).1 hbyteOK c hc
      exact hpow x hxc
    have hbyte : ∀ denv, d.satisfies bs denv → (denseSumExpr (densePeel D E).1).eval denv = 0 →
        (densePeel D E).2.eval denv = 0 := by
      intro denv hsat hden0
      have hE0 : E.eval denv = 0 := hsat.1 E (List.mem_of_getElem? hidx)
      have hbytes : ∀ c ∈ (densePeel D E).1, (c.eval denv).val < 256 := by
        intro c hc
        obtain ⟨a, heval, _, _, _, b, hlk, hb256⟩ :=
          denseCoeffsByteOK_sound reg Bm D (densePeel D E).1 hbyteOK c hc
        have hlt := hBmSound a b hlk denv hsat
        rw [heval denv]; omega
      have hsum0 : ((densePeel D E).1.map (fun c => c.eval denv)).sum = 0 := by
        rw [← denseSumExpr_eval]; exact hden0
      have hfit' : (((densePeel D E).1.map (fun c => c.eval denv)).map (fun x => x.val)).sum < p := by
        have hle := List.sum_le_card_nsmul
          (((densePeel D E).1.map (fun c => c.eval denv)).map (fun x => x.val)) 255 (by
            intro x hx
            simp only [List.mem_map] at hx
            obtain ⟨b, ⟨c, hc, rfl⟩, rfl⟩ := hx
            have := hbytes c hc; omega)
        simp only [List.length_map, smul_eq_mul] at hle
        have hlen : (densePeel D E).1.length = D.length := densePeel_length D E
        have hfit := of_decide_eq_true hfitG
        omega
      have hallz : ∀ c ∈ (densePeel D E).1, c.eval denv = 0 := fun c hc =>
        sum_zero_all_zero hp0 _ hfit' hsum0 (c.eval denv) (List.mem_map.2 ⟨c, hc, rfl⟩)
      have hfz := denseFoldr_zero ((densePeel D E).1.zip D) denv
        (fun cd hcd => hallz cd.1 (List.of_mem_zip hcd).1)
      rw [densePeel_eval D E denv, hfz, zero_add] at hE0
      exact hE0
    exact denseHcAccept_correct reg ⟨"hcinv#" ++ (reg.resolve (D.headD default)).name, none⟩ rfl
      d bs E (denseSumExpr (densePeel D E).1) (densePeel D E).2 D idx
      (fun denv w => denseReassign D w denv) hcov hidx huniq
      (fun denv w v hv => by show (if v ∈ D then w else denv v) = denv v; rw [if_neg hv])
      (fun denv w => densePeel_reassign_eval D E hcfree hrfree denv w)
      hbyte (hcFresh_isFresh hfreshP) hDonce hDbus hrest_sub2 hden_sub2 hden_pow
      (fun x hx => List.all_eq_true.1 hrpowG x hx)
  · -- the sum-of-squares shape
    rw [Bool.and_eq_true] at hsq
    obtain ⟨hsqOK, hfitG⟩ := hsq
    have hlen : (densePeel D E).1.length = D.length := densePeel_length D E
    have hcfree : ∀ c ∈ (densePeel D E).1, ∀ dw ∈ D, dw ∉ c.vars := by
      intro c hc dw hd
      obtain ⟨a, b, _, hDf, _, _, _, _, _⟩ :=
        denseSqCoeffsOK_sound reg Bm D (densePeel D E).1 hsqOK c hc
      exact hDf dw hd
    have hmap2 : ((densePeel D E).1.zip D).map (fun x => x.2) = D :=
      List.map_snd_zip (by rw [hlen])
    have hdenvars : ∀ x ∈ (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).vars,
        ∃ c ∈ (densePeel D E).1, x ∈ c.vars := by
      intro x hx
      obtain ⟨e, he, hxe⟩ := denseSumExpr_vars hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      simp only [DenseExpr.vars, List.mem_append, or_self] at hxe
      exact ⟨c, hc, hxe⟩
    have hden_sub2 : ∀ x ∈ (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).vars,
        x ∈ d.occ := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hdenvars x hx
      exact DenseConstraintSystem.mem_occ_of_constraint (List.mem_of_getElem? hidx)
        (densePeel_fst_vars D E c hc x hxc)
    have hden_pow : ∀ x ∈ (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).vars,
        reg.isInput x = true := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hdenvars x hx
      obtain ⟨a, b, _, _, hpow, _, _, _, _⟩ :=
        denseSqCoeffsOK_sound reg Bm D (densePeel D E).1 hsqOK c hc
      exact hpow x hxc
    have hbyte : ∀ denv, d.satisfies bs denv →
        (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).eval denv = 0 →
        (densePeel D E).2.eval denv = 0 := by
      intro denv hsat hden0
      have hE0 : E.eval denv = 0 := hsat.1 E (List.mem_of_getElem? hidx)
      have hbytes : ∀ c ∈ (densePeel D E).1, ((c.eval denv) * (c.eval denv)).val < 65536 := by
        intro c hc
        obtain ⟨a, b, heval, _, _, _, _, ⟨ba, hlka, hba⟩, ⟨bb, hlkb, hbb⟩⟩ :=
          denseSqCoeffsOK_sound reg Bm D (densePeel D E).1 hsqOK c hc
        have hlta := hBmSound a ba hlka denv hsat
        have hltb := hBmSound b bb hlkb denv hsat
        haveI : NeZero p := ⟨hp0.ne'⟩
        rw [heval denv]
        have hfit := of_decide_eq_true hfitG
        exact sq_diff_val_lt (by omega) (denv a) (denv b) (by omega) (by omega)
      have hdeneval : (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c))).eval denv
          = ((densePeel D E).1.map (fun c => c.eval denv * c.eval denv)).sum := by
        rw [denseSumExpr_eval, List.map_map]; rfl
      have hsum0 : ((densePeel D E).1.map (fun c => c.eval denv * c.eval denv)).sum = 0 := by
        rw [← hdeneval]; exact hden0
      have hfit' : (((densePeel D E).1.map (fun c => c.eval denv * c.eval denv)).map
          (fun x => x.val)).sum < p := by
        have hle := List.sum_le_card_nsmul
          (((densePeel D E).1.map (fun c => c.eval denv * c.eval denv)).map (fun x => x.val))
          65535 (by
            intro x hx
            simp only [List.mem_map] at hx
            obtain ⟨s, ⟨c, hc, rfl⟩, rfl⟩ := hx
            have := hbytes c hc; omega)
        simp only [List.length_map, smul_eq_mul] at hle
        have hfit := of_decide_eq_true hfitG
        omega
      have hallz : ∀ c ∈ (densePeel D E).1, c.eval denv * c.eval denv = 0 := fun c hc =>
        sum_zero_all_zero hp0 _ hfit' hsum0 (c.eval denv * c.eval denv) (List.mem_map.2 ⟨c, hc, rfl⟩)
      have hallz0 : ∀ c ∈ (densePeel D E).1, c.eval denv = 0 := fun c hc =>
        mul_self_eq_zero.1 (hallz c hc)
      have hfz := denseFoldr_zero ((densePeel D E).1.zip D) denv
        (fun cd hcd => hallz0 cd.1 (List.of_mem_zip hcd).1)
      rw [densePeel_eval D E denv, hfz, zero_add] at hE0
      exact hE0
    exact denseHcAccept_correct reg ⟨"hcsq#" ++ (reg.resolve (D.headD default)).name, none⟩ rfl
      d bs E (denseSumExpr ((densePeel D E).1.map (fun c => DenseExpr.mul c c)))
      (densePeel D E).2 D idx
      (fun denv w => denseAssocReassign ((densePeel D E).1.zip D) denv w) hcov hidx huniq
      (fun denv w v hv => denseAssocReassign_agree _ denv w v (by rw [hmap2]; exact hv))
      (fun denv w => densePeel_sqReassign_eval D E hnd hcfree hrfree denv w)
      hbyte (hcFresh_isFresh hfreshS) hDonce hDbus hrest_sub2 hden_sub2 hden_pow
      (fun x hx => List.all_eq_true.1 hrpowG x hx)

/-- First-hit scan correctness: whichever candidate target collapses, it is a `DensePassCorrect`
    collapse. -/
theorem denseHcScanTry_correct [Fact p.Prime] {bs : BusSemantics p} (facts : BusFacts p bs)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    ∀ (cands : List (Nat × DenseExpr p)),
      (∀ ie ∈ cands, d.algebraicConstraints[ie.1]? = some ie.2) →
      ∀ r, denseHcScanTry bs facts reg d (denseHcScan reg.byId.size d) cands = some r →
        reg.Extends r.1 ∧ r.2.1.CoveredBy r.1 ∧ DenseDerivations.CoveredBy r.1 r.2.2 ∧
          DensePassCorrect r.1.isInput d r.2.1 r.2.2 bs := by
  intro cands
  induction cands with
  | nil => intro _ r hr; simp [denseHcScanTry] at hr
  | cons ie rest ih =>
      intro hmem r hr
      obtain ⟨idx, E⟩ := ie
      simp only [denseHcScanTry] at hr
      split at hr
      · rename_i r1 heq
        obtain rfl := Option.some.inj hr
        exact denseHcTry_correct facts reg d idx E hcov (hmem (idx, E) (List.mem_cons_self ..))
          r1 heq
      · exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) r hr

theorem denseHintCollapseF_props (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    reg.Extends (denseHintCollapseF pw reg bs facts d).1
    ∧ (denseHintCollapseF pw reg bs facts d).2.1.CoveredBy (denseHintCollapseF pw reg bs facts d).1
    ∧ DenseDerivations.CoveredBy (denseHintCollapseF pw reg bs facts d).1
        (denseHintCollapseF pw reg bs facts d).2.2
    ∧ DensePassCorrect (denseHintCollapseF pw reg bs facts d).1.isInput d
        (denseHintCollapseF pw reg bs facts d).2.1 (denseHintCollapseF pw reg bs facts d).2.2 bs := by
  have hrefl : reg.Extends reg ∧ d.CoveredBy reg ∧
      DenseDerivations.CoveredBy (p := p) reg [] ∧
      DensePassCorrect reg.isInput d d ([] : DenseDerivations p) bs :=
    ⟨VarRegistry.Extends.refl reg, hcov, (by intro x hx; simp at hx),
      DensePassCorrect.refl reg.isInput d bs⟩
  simp only [denseHintCollapseF]
  by_cases hpr : pw.isPrime = true
  · rw [if_pos hpr]
    haveI : Fact p.Prime := ⟨pw.correct hpr⟩
    cases hgs : denseHcGroups (denseHcScan reg.byId.size d) with
    | nil => exact hrefl
    | cons i0 is =>
        have hpick : ∀ ie ∈ denseHcPick 0 (i0 :: is) d.algebraicConstraints,
            d.algebraicConstraints[ie.1]? = some ie.2 := by
          intro ie hie
          obtain ⟨k, hk, hget⟩ := hcPick_spec d.algebraicConstraints (i0 :: is) 0 ie.1 ie.2 hie
          rw [hk]; simpa using hget
        cases hres : denseHcScanTry bs facts reg d (denseHcScan reg.byId.size d)
            (denseHcPick 0 (i0 :: is) d.algebraicConstraints) with
        | none => simpa only [hres, Option.getD_none] using hrefl
        | some r =>
            simpa only [hres, Option.getD_some] using
              denseHcScanTry_correct facts reg d hcov _ hpick r hres
  · rw [if_neg hpr]; exact hrefl

/-- The registry-extending hint-collapse pass. -/
def denseHintCollapsePass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofExtending (denseHintCollapseF pw)
    (fun reg bs facts d hcov => (denseHintCollapseF_props pw reg bs facts d hcov).1)
    (fun reg bs facts d hcov => (denseHintCollapseF_props pw reg bs facts d hcov).2.1)
    (fun reg bs facts d hcov => (denseHintCollapseF_props pw reg bs facts d hcov).2.2.1)
    (fun reg bs facts d hcov => (denseHintCollapseF_props pw reg bs facts d hcov).2.2.2)

end ApcOptimizer.Dense
