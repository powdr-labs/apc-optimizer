import ApcOptimizer.Implementation.OptimizerPasses.FlagFold
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.EntailedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagUnify

set_option autoImplicit false

/-! # Soundness for the dense `flagFold` pass

`denseFlagFoldF` (`FlagFold.lean`) runs four transforms over one shared finite-domain table. Parts C
and D's certificates are proven here (the box tautology as a constraint map on the same environment,
the pointwise duplicate as a bus filter whose dropped interaction is accepted via its provably-kept
first-of-class twin); A's and B's are in `Proofs/FxSubst.lean` and `Proofs/BoxRewrite.lean`. The
pass is those four composed with `DensePassCorrect.trans`, plus what makes the table admissible:

* `ffSole_vars` — the scalar walk only reports single-variable constraints;
* `ffBucketsOf_mem` — every bucket holds single-variable constraints of the system;
* `ffTabGet_eq` — every table entry is its own bucket's `denseFindDomainAlg` verdict.

Part C's gate is an equality, not a new certificate (`ffBtCert_eq`: it rejects on `denseBtCert`'s
own cheapest conjunct first). Part B's gate needs no lemma at all — below the bound the pass
returns its input unchanged. Part D's sweep is a proposal generator re-verified by `densePdKeep`,
so it carries no obligation either. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The single-variable walk -/

/-- The walk's invariant: `0` means nothing seen, `1` is uninformative, `i + 2` means at least one
    variable was seen and every one of them is `⟨i⟩`. -/
def FfSoleInv (s : Nat) (l : List VarId) : Prop :=
  (s = 0 → l = []) ∧ (2 ≤ s → l ≠ [] ∧ ∀ y ∈ l, y.index + 2 = s)

theorem ffSoleGo_inv (e : DenseExpr p) :
    ∀ s acc, FfSoleInv s acc → FfSoleInv (ffSoleGo e s) (acc ++ e.vars) := by
  induction e with
  | const n => intro s acc h; simpa [ffSoleGo, DenseExpr.vars] using h
  | var i =>
      intro s acc h
      simp only [ffSoleGo, DenseExpr.vars]
      by_cases h0 : (s == 0) = true
      · have hs0 : s = 0 := by simpa using h0
        have hacc : acc = [] := h.1 hs0
        subst hacc
        rw [if_pos h0]
        refine ⟨by omega, fun _ => ⟨by simp, ?_⟩⟩
        intro y hy
        simp only [List.nil_append, List.mem_singleton] at hy
        subst hy; rfl
      · rw [if_neg h0]
        by_cases h1 : (s == i.index + 2) = true
        · have hsi : s = i.index + 2 := by simpa using h1
          rw [if_pos h1]
          refine ⟨by omega, fun _ => ⟨by simp, ?_⟩⟩
          intro y hy
          rcases List.mem_append.1 hy with hy' | hy'
          · by_cases hacc : acc = []
            · subst hacc; simp at hy'
            · exact (h.2 (by omega)).2 y hy'
          · simp only [List.mem_singleton] at hy'; subst hy'; exact hsi.symm
        · rw [if_neg h1]
          exact ⟨by omega, by omega⟩
  | add a b iha ihb =>
      intro s acc h
      simp only [ffSoleGo, DenseExpr.vars]
      by_cases h1 : (ffSoleGo a s == 1) = true
      · rw [if_pos h1]; exact ⟨by omega, by omega⟩
      · rw [if_neg h1, ← List.append_assoc]
        exact ihb _ _ (iha _ _ h)
  | mul a b iha ihb =>
      intro s acc h
      simp only [ffSoleGo, DenseExpr.vars]
      by_cases h1 : (ffSoleGo a s == 1) = true
      · rw [if_pos h1]; exact ⟨by omega, by omega⟩
      · rw [if_neg h1, ← List.append_assoc]
        exact ihb _ _ (iha _ _ h)

/-- A nonempty list all of whose elements are `v` deduplicates to `[v]`. -/
theorem eraseDups_of_all_eq {v : VarId} :
    ∀ (l : List VarId), l ≠ [] → (∀ y ∈ l, y = v) → l.eraseDups = [v] := by
  intro l hne hall
  match l with
  | [] => exact absurd rfl hne
  | a :: as =>
      have ha : a = v := hall a (by simp)
      subst ha
      rw [List.eraseDups_cons]
      have hnil : as.filter (fun b => !b == a) = [] := by
        refine List.filter_eq_nil_iff.2 (fun b hb => ?_)
        rw [hall b (by simp [hb])]
        simp
      rw [hnil]
      rfl

/-- `ffSole` only reports genuinely single-variable expressions. -/
theorem ffSole_vars {c : DenseExpr p} {v : VarId} (h : ffSole c = some v) :
    c.vars.eraseDups = [v] := by
  unfold ffSole at h
  by_cases hs : 2 ≤ ffSoleGo c 0
  · rw [if_pos hs] at h
    have hv : v = ⟨ffSoleGo c 0 - 2⟩ := by
      simp only [Option.some.injEq] at h; exact h.symm
    have hinv := ffSoleGo_inv c 0 [] ⟨fun _ => rfl, by omega⟩
    obtain ⟨hne, hall⟩ := hinv.2 hs
    rw [List.nil_append] at hne hall
    refine eraseDups_of_all_eq c.vars hne (fun y hy => ?_)
    have := hall y hy
    rw [hv]
    exact congrArg VarId.mk (by omega)
  · rw [if_neg hs] at h; exact absurd h (by simp)

/-- A constraint the walk accepts is one of the system's single-variable constraints. -/
theorem ffSole_mem_singleVarCs {cs : List (DenseExpr p)} {c : DenseExpr p} {v : VarId}
    (hc : c ∈ cs) (h : ffSole c = some v) : c ∈ denseSingleVarCs cs := by
  refine List.mem_filter.2 ⟨hc, ?_⟩
  rw [HashedDedup.hashedEraseDups_eq, ffSole_vars h]
  rfl

/-! ## The bucket array -/

theorem ffGetD_set!_cases {α : Type} (B : Array α) (j : Nat) (y d : α) (i : Nat) :
    (B.set! j y).getD i d = y ∨ (B.set! j y).getD i d = B.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  show ((B.setIfInBounds j y)[i]?).getD d = y ∨ ((B.setIfInBounds j y)[i]?).getD d = (B[i]?).getD d
  rw [Array.getElem?_setIfInBounds]
  by_cases hij : j = i
  · subst hij
    by_cases hj : j < B.size
    · rw [if_pos rfl, if_pos hj]; exact Or.inl rfl
    · rw [if_pos rfl, if_neg hj]
      refine Or.inr ?_
      rw [Array.getElem?_eq_none (by omega)]
  · rw [if_neg hij]; exact Or.inr rfl

/-- Every constraint in every bucket is a single-variable constraint of the source list. -/
theorem ffBucketsOf_mem (cs : List (DenseExpr p)) (v : VarId) (c : DenseExpr p)
    (h : c ∈ ffBucketOf (ffBucketsOf cs) v) : c ∈ denseSingleVarCs cs := by
  unfold ffBucketsOf ffBucketOf at h
  suffices hgen : ∀ (l : List (DenseExpr p)) (B : Array (List (DenseExpr p))),
      (∀ i, ∀ c' ∈ B.getD i [], c' ∈ denseSingleVarCs cs) →
      (∀ c' ∈ l, c' ∈ cs) →
      ∀ i, ∀ c' ∈ (l.foldr (fun c B =>
        match ffSole c with
        | some w => B.set! w.index (c :: B.getD w.index [])
        | none => B) B).getD i [], c' ∈ denseSingleVarCs cs from
    hgen cs _ (fun i c' hc' => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hc'
      split at hc' <;> simp at hc') (fun _ h => h) v.index c h
  intro l
  induction l with
  | nil => intro B hB _ i c' hc'; exact hB i c' hc'
  | cons a rest ih =>
      intro B hB hmem i c' hc'
      rw [List.foldr_cons] at hc'
      have hrest := ih B hB (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      cases hsole : ffSole a with
      | none => rw [hsole] at hc'; exact hrest i c' hc'
      | some w =>
          rw [hsole] at hc'
          rcases ffGetD_set!_cases (α := List (DenseExpr p)) _ w.index
            (a :: (rest.foldr _ B).getD w.index []) [] i with heq | heq
          · rw [heq] at hc'
            rcases List.mem_cons.1 hc' with heqa | hc''
            · exact heqa ▸ ffSole_mem_singleVarCs (hmem a (List.mem_cons_self ..)) hsole
            · exact hrest w.index c' hc''
          · rw [heq] at hc'; exact hrest i c' hc'

/-! ## The domain table -/

/-- Every table entry is its own bucket's `denseFindDomainAlg` verdict. -/
theorem ffTabGet_eq (B : Array (List (DenseExpr p))) (v : VarId) :
    ffTabGet (ffTabOf B) v = denseFindDomainAlg (ffBucketOf B v) v := by
  unfold ffTabGet ffTabOf ffBucketOf
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  by_cases hv : v.index < B.size
  · rw [Array.getElem?_eq_getElem (by rw [Array.size_mapFinIdx]; exact hv),
        Array.getElem?_eq_getElem hv, Array.getElem_mapFinIdx]
    rfl
  · rw [Array.getElem?_eq_none (by rw [Array.size_mapFinIdx]; omega),
        Array.getElem?_eq_none (by omega)]
    rfl

/-- The domains the fused pass reports are justified by their own buckets. -/
theorem ffTab_domOf (cs : List (DenseExpr p)) (v : VarId) (dm : List (ZMod p))
    (h : ffTabGet (ffTabOf (ffBucketsOf cs)) v = some dm) :
    denseFindDomainAlg (ffBucketOf (ffBucketsOf cs) v) v = some dm := by
  rwa [ffTabGet_eq] at h

/-! ## Part C's certificate: box tautology -/

/-- A constraint with fewer than two distinct variables fails `denseBtCert`'s first guard. -/
theorem denseBtCert_of_lt_two {domOf : VarId → Option (List (ZMod p))} {c : DenseExpr p}
    (hs : c.vars.eraseDups.length ≤ 1) : denseBtCert domOf c = false := by
  unfold denseBtCert
  have h1 : ¬ (2 ≤ (HashedDedup.hashedEraseDups (hash ·) c.vars).length) := by
    rw [HashedDedup.hashedEraseDups_eq]; omega
  simp [h1]

/-- A single-variable constraint is never replaced (it fails the `≥ 2` guard), so it survives
    verbatim into the output — the box justification stands on the output's own satisfaction. -/
theorem denseSingleVar_mem_boxTautoReplace (d : DenseConstraintSystem p)
    (domOf : VarId → Option (List (ZMod p))) (c : DenseExpr p)
    (hc : c ∈ d.algebraicConstraints) (hs : (c.vars.eraseDups.length == 1) = true) :
    c ∈ (d.boxTautoReplaceWith domOf).algebraicConstraints := by
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  rw [denseBtCert_of_lt_two (by have := of_decide_eq_true hs; omega)]
  simp

/-- Box-tautology replacement correctness: every replaced constraint is a tautology over its box.
The domains come from `domOf`, which is untrusted — `hdomOf` re-derives each reported domain as the
verdict of `denseFindDomainAlg` on `v`'s bucket, and `hidx` places that bucket inside the
never-replaced single-variable constraints, so the box justification stands on the output's own
satisfaction. Satisfaction is then preserved on the same environment and bus effects are
untouched. -/
theorem DenseConstraintSystem.boxTautoReplace_denseCorrect [Fact p.Prime]
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (bucketOf : VarId → List (DenseExpr p))
    (hidx : ∀ v, ∀ c ∈ bucketOf v, c ∈ denseSingleVarCs d.algebraicConstraints)
    (domOf : VarId → Option (List (ZMod p)))
    (hdomOf : ∀ v dm, domOf v = some dm → denseFindDomainAlg (bucketOf v) v = some dm) :
    DensePassCorrect isInput d (d.boxTautoReplaceWith domOf) [] bs := by
  have hzero : ∀ denv, (d.boxTautoReplaceWith domOf).satisfies bs denv →
      ∀ c ∈ d.algebraicConstraints, denseBtCert domOf c = true → c.eval denv = 0 := by
    intro denv hsat c _hc hcert
    unfold denseBtCert at hcert
    rw [HashedDedup.hashedEraseDups_eq] at hcert
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcert
    obtain ⟨_h2, ⟨⟨hcover, _hcap⟩, hall⟩⟩ := hcert
    have hcover' := of_decide_eq_true hcover
    have hdom : ∀ c' ∈ denseSingleVarCs d.algebraicConstraints, c'.eval denv = 0 := by
      intro c' hc'
      have hmem := List.mem_of_mem_filter hc'
      have hsingle : (c'.vars.eraseDups.length == 1) = true := by
        have h := (List.mem_filter.1 hc').2
        rwa [HashedDedup.hashedEraseDups_eq] at h
      exact hsat.1 c' (denseSingleVar_mem_boxTautoReplace d domOf c' hmem hsingle)
    have hbucket : ∀ v, ∀ c' ∈ bucketOf v, c'.eval denv = 0 :=
      fun v c' hc' => hdom c' (hidx v c' hc')
    have hmemdoms : ∀ vd ∈ c.vars.eraseDups.filterMap (fun v =>
        (domOf v).map (fun dm => (v, dm))), denv vd.1 ∈ vd.2 := by
      intro vd hvd
      obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
      cases hfd : domOf v with
      | none => rw [hfd] at hvd'; simp at hvd'
      | some dm =>
          rw [hfd] at hvd'
          simp only [Option.map_some, Option.some.injEq] at hvd'
          obtain rfl := hvd'.symm
          exact denseFindDomainAlg_sound denv (bucketOf v) v dm (hdomOf v dm hfd) (hbucket v)
    have hpt := mem_denseAssignments (c.vars.eraseDups.filterMap (fun v =>
      (domOf v).map (fun dm => (v, dm)))) denv hmemdoms
    have hptz := of_decide_eq_true (List.all_eq_true.mp hall _ hpt)
    have hagree : c.eval (denseEnvOfFast ((c.vars.eraseDups.filterMap (fun v =>
        (domOf v).map (fun dm => (v, dm)))).map (fun vd => (vd.1, denv vd.1)))) = c.eval denv := by
      refine DenseExpr.eval_congr c _ denv (fun v hv => ?_)
      refine denseEnvOfFast_map _ denv v ?_
      rw [show ((c.vars.eraseDups.filterMap (fun v =>
        (domOf v).map (fun dm => (v, dm)))).map Prod.fst) = c.vars.eraseDups from hcover']
      exact List.mem_eraseDups.2 hv
    rw [← hagree]; exact hptz
  have hiff : ∀ denv, (d.boxTautoReplaceWith domOf).satisfies bs denv ↔ d.satisfies bs denv := by
    intro denv
    constructor
    · intro hsat
      refine ⟨fun c hc => ?_, hsat.2⟩
      by_cases hcond : denseBtCert domOf c = true
      · exact hzero denv hsat c hc hcond
      · have h0 := hsat.1 _ (List.mem_map.2 ⟨c, hc, rfl⟩)
        rw [if_neg hcond] at h0
        exact h0
    · intro hsat
      refine ⟨fun c' hc' => ?_, hsat.2⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      by_cases hcond : denseBtCert domOf c = true
      · rw [if_pos hcond]; rfl
      · rw [if_neg hcond]; exact hsat.1 c hc
  refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
  ·
    intro denv hsat
    exact ⟨(hiff denv).1 hsat, rfl⟩
  ·
    intro hgi denv hsat bi hbi
    exact hgi denv ((hiff denv).1 hsat) bi hbi
  ·
    intro i hi
    simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
    rcases hi with ⟨c', hc', hic⟩ | ⟨bi, hbi, hib⟩
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hc'
      by_cases hcond : denseBtCert domOf c = true
      · rw [if_pos hcond] at hic; simp [DenseExpr.vars] at hic
      · rw [if_neg hcond] at hic
        exact DenseConstraintSystem.mem_occ_of_constraint hcm hic
    · exact DenseConstraintSystem.mem_occ_of_bi hbi hib
  ·
    intro denv hadm hsat
    exact ⟨(hiff denv).2 hsat, hadm, rfl⟩

/-- Coverage is preserved: replaced constraints are `const 0` (no variables) or original (covered);
    bus interactions unchanged. -/
theorem DenseConstraintSystem.boxTautoReplaceWith_covered {reg : VarRegistry}
    {d : DenseConstraintSystem p} (domOf : VarId → Option (List (ZMod p)))
    (hc : d.CoveredBy reg) : (d.boxTautoReplaceWith domOf).CoveredBy reg := by
  refine ⟨fun e he => ?_, fun bi hbi => hc.2 bi hbi⟩
  simp only [DenseConstraintSystem.boxTautoReplaceWith] at he
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 he
  by_cases hcond : denseBtCert domOf c = true
  · rw [if_pos hcond]; intro i hi; simp [DenseExpr.vars] at hi
  · rw [if_neg hcond]; exact hc.1 c hcm

/-! ## Part C's gate -/

theorem ffAllBoxed_false {T : FfTab p} :
    ∀ (c : DenseExpr p), ffAllBoxed T c = false → ∃ v ∈ c.vars, ffTabGet T v = none := by
  intro c
  induction c with
  | const n => intro h; simp [ffAllBoxed] at h
  | var i =>
      intro h
      refine ⟨i, by simp [DenseExpr.vars], ?_⟩
      simp only [ffAllBoxed, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      exact h
  | add a b iha ihb =>
      intro h
      simp only [ffAllBoxed, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨v, hv, hd⟩ := iha h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩
      · obtain ⟨v, hv, hd⟩ := ihb h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩
  | mul a b iha ihb =>
      intro h
      simp only [ffAllBoxed, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · obtain ⟨v, hv, hd⟩ := iha h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩
      · obtain ⟨v, hv, hd⟩ := ihb h
        exact ⟨v, by simp [DenseExpr.vars, hv], hd⟩

/-- The gate is one of `denseBtCert`'s own conjuncts: a variable without a domain breaks the
    `doms.map Prod.fst = vs` cover test. -/
theorem ffBtCert_eq (T : FfTab p) (c : DenseExpr p) :
    ffBtCert T c = denseBtCert (ffTabGet T) c := by
  unfold ffBtCert
  by_cases hg : ffAllBoxed T c = true
  · rw [hg, Bool.true_and]
  · rw [Bool.not_eq_true] at hg
    rw [hg, Bool.false_and]
    obtain ⟨v, hv, hd⟩ := ffAllBoxed_false c hg
    unfold denseBtCert
    rw [HashedDedup.hashedEraseDups_eq]
    have hcover : (decide ((c.vars.eraseDups.filterMap (fun w =>
        (ffTabGet T w).map (fun dm => (w, dm)))).map Prod.fst = c.vars.eraseDups)) = false := by
      simp only [decide_eq_false_iff_not]
      intro hc
      have hvm : v ∈ (c.vars.eraseDups.filterMap (fun w =>
          (ffTabGet T w).map (fun dm => (w, dm)))).map Prod.fst := by
        rw [hc]; exact List.mem_eraseDups.2 hv
      obtain ⟨pr, hpr, hfst⟩ := List.mem_map.1 hvm
      obtain ⟨w, _hw, hwe⟩ := List.mem_filterMap.1 hpr
      cases hdw : ffTabGet T w with
      | none => rw [hdw] at hwe; simp at hwe
      | some dm =>
          rw [hdw] at hwe
          simp only [Option.map_some, Option.some.injEq] at hwe
          rw [← hwe] at hfst
          simp only at hfst
          rw [hfst] at hdw
          rw [hd] at hdw
          exact absurd hdw (by simp)
    simp [hcover]

theorem ffBoxTauto_eq (d : DenseConstraintSystem p) (T : FfTab p) :
    d.ffBoxTauto T = d.boxTautoReplaceWith (ffTabGet T) := by
  unfold DenseConstraintSystem.ffBoxTauto DenseConstraintSystem.boxTautoReplaceWith
  refine congrArg (fun l => { d with algebraicConstraints := l }) ?_
  exact List.map_congr_left (fun c _ => by rw [ffBtCert_eq])

/-! ## Part D's certificate: pointwise-duplicate stateless checks -/

/-- Joint-box agreement soundness: agreement at every box point gives agreement on every assignment
    zeroing the single-variable constraints. -/
theorem denseBoxAgree_sound [Fact p.Prime]
    (domIdx : Std.HashMap VarId (List (DenseExpr p))) (R R' : DenseExpr p)
    (h : denseBoxAgree domIdx R R' = true) (denv : VarId → ZMod p)
    (hdom : ∀ v, ∀ c ∈ denseVarBucketLookup domIdx v, c.eval denv = 0) :
    R.eval denv = R'.eval denv := by
  unfold denseBoxAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hcover, _hcap⟩, hall⟩ := h
  have hmemdoms : ∀ vd ∈ (R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (denseFindDomainAlg
          (denseVarBucketLookup domIdx v) v).map (fun dm => (v, dm))), denv vd.1 ∈ vd.2 := by
    intro vd hvd
    obtain ⟨v, _hv, hvd'⟩ := List.mem_filterMap.1 hvd
    cases hfd : denseFindDomainAlg (denseVarBucketLookup domIdx v) v with
    | none => rw [hfd] at hvd'; simp at hvd'
    | some dm =>
        rw [hfd] at hvd'
        simp only [Option.map_some, Option.some.injEq] at hvd'
        obtain rfl := hvd'.symm
        exact denseFindDomainAlg_sound denv (denseVarBucketLookup domIdx v) v dm hfd (hdom v)
  have hpt := mem_denseAssignments ((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
    (denseFindDomainAlg (denseVarBucketLookup domIdx v) v).map (fun dm => (v, dm)))) denv hmemdoms
  have hagree : ∀ v, v ∈ (R.vars ++ R'.vars).eraseDups →
      denseEnvOfFast (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
        (denseFindDomainAlg (denseVarBucketLookup domIdx v) v).map (fun dm => (v, dm)))).map
          (fun vd => (vd.1, denv vd.1))) v = denv v := by
    intro v hv
    refine denseEnvOfFast_map _ denv v ?_
    rw [show (((R.vars ++ R'.vars).eraseDups.filterMap (fun v =>
      (denseFindDomainAlg (denseVarBucketLookup domIdx v) v).map (fun dm => (v, dm)))).map Prod.fst)
      = (R.vars ++ R'.vars).eraseDups from hcover]
    exact hv
  have hRR := of_decide_eq_true (List.all_eq_true.mp hall _ hpt)
  have hRa : R.eval (denseEnvOfFast (((R.vars ++ R'.vars).eraseDups.filterMap
      (fun v => (denseFindDomainAlg (denseVarBucketLookup domIdx v) v).map (fun dm => (v, dm)))).map
        (fun vd => (vd.1, denv vd.1)))) = R.eval denv :=
    DenseExpr.eval_congr R _ denv (fun v hv =>
      hagree v (List.mem_eraseDups.2 (List.mem_append_left _ hv)))
  have hRa' : R'.eval (denseEnvOfFast (((R.vars ++ R'.vars).eraseDups.filterMap
      (fun v => (denseFindDomainAlg (denseVarBucketLookup domIdx v) v).map (fun dm => (v, dm)))).map
        (fun vd => (vd.1, denv vd.1)))) = R'.eval denv :=
    DenseExpr.eval_congr R' _ denv (fun v hv =>
      hagree v (List.mem_eraseDups.2 (List.mem_append_right _ hv)))
  rw [← hRa, ← hRa', hRR]

/-- Slot-pair certificate soundness (`denseSlotEqCert`). -/
theorem denseSlotEqCert_sound [Fact p.Prime]
    (domIdx : Std.HashMap VarId (List (DenseExpr p))) (e e' : DenseExpr p)
    (h : denseSlotEqCert domIdx e e' = true) (denv : VarId → ZMod p)
    (hdom : ∀ v, ∀ c ∈ denseVarBucketLookup domIdx v, c.eval denv = 0) :
    e.eval denv = e'.eval denv := by
  unfold denseSlotEqCert at h
  rw [Bool.or_eq_true] at h
  rcases h with heq | hany
  · rw [eq_of_beq heq]
  · obtain ⟨x, _hx, hx⟩ := List.any_eq_true.1 hany
    rw [Bool.and_eq_true] at hx
    obtain ⟨_hm, hx⟩ := hx
    cases hsX : e.splitAt x with
    | none => rw [hsX] at hx; simp at hx
    | some kR =>
        obtain ⟨k, R⟩ := kR
        cases hsY : e'.splitAt x with
        | none => rw [hsX, hsY] at hx; simp at hx
        | some kR' =>
            obtain ⟨k2, R'⟩ := kR'
            simp only [hsX, hsY, Bool.and_eq_true] at hx
            obtain ⟨hk2, hba⟩ := hx
            rw [DenseExpr.splitAt_eval x e k R hsX denv,
                DenseExpr.splitAt_eval x e' k2 R' hsY denv, eq_of_beq hk2,
                denseBoxAgree_sound domIdx R R' hba denv hdom]

/-- Full-message certificate soundness: the two interactions evaluate to the same message. -/
theorem denseMsgEqCert_sound [Fact p.Prime] (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (bi bi' : BusInteraction (DenseExpr p)) (h : denseMsgEqCert domIdx bi bi' = true)
    (denv : VarId → ZMod p)
    (hdom : ∀ v, ∀ c ∈ denseVarBucketLookup domIdx v, c.eval denv = 0) :
    denseBIEval bi denv = denseBIEval bi' denv := by
  unfold denseMsgEqCert at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hbus, hmult⟩, hlen⟩, hslots⟩ := h
  have hmm : bi.multiplicity.eval denv = bi'.multiplicity.eval denv := by
    cases hm : bi.multiplicity.constValue? with
    | none => rw [hm] at hmult; simp at hmult
    | some m =>
        cases hm' : bi'.multiplicity.constValue? with
        | none => rw [hm, hm'] at hmult; simp at hmult
        | some m' =>
            rw [hm, hm'] at hmult
            rw [bi.multiplicity.constValue?_sound m hm denv,
                bi'.multiplicity.constValue?_sound m' hm' denv, eq_of_beq hmult]
  have hpay : bi.payload.map (fun e => e.eval denv)
      = bi'.payload.map (fun e => e.eval denv) := by
    have hlen' : bi.payload.length = bi'.payload.length := by simpa using hlen
    refine List.ext_getElem (by simpa) (fun i h1 h2 => ?_)
    have hi1 : i < bi.payload.length := by simpa using h1
    have hi2 : i < bi'.payload.length := by simpa using h2
    have hz : (bi.payload[i]'hi1, bi'.payload[i]'hi2) ∈ bi.payload.zip bi'.payload := by
      have hzi : (bi.payload.zip bi'.payload)[i]'(by rw [List.length_zip]; omega)
          = (bi.payload[i]'hi1, bi'.payload[i]'hi2) := by
        simp [List.getElem_zip]
      rw [← hzi]
      exact List.getElem_mem _
    have hcert := List.all_eq_true.mp hslots _ hz
    simp only [List.getElem_map]
    exact denseSlotEqCert_sound domIdx _ _ hcert denv hdom
  show denseBIEval bi denv = denseBIEval bi' denv
  unfold denseBIEval
  rw [eq_of_beq hbus, hmm, hpay]

/-- A first-of-class interaction is always kept — the depth-1 justification for `densePdKeep`. -/
theorem densePdFirst_keep (bs : BusSemantics p) (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (bis : List (BusInteraction (DenseExpr p))) (b : BusInteraction (DenseExpr p))
    (h : densePdFirst bs domIdx bis b = true) : densePdKeep bs domIdx bis b = true := by
  unfold densePdKeep
  rw [Bool.or_eq_true]
  right
  unfold densePdFirst at h
  cases hidx : bis.findIdx? (fun x => x == b) with
  | none => simp
  | some i =>
      rw [hidx] at h
      simp only
      rw [Bool.not_eq_true']
      by_contra hany
      have hany' : ((bis.take i).any (fun b' => !bs.isStateful b'.busId
          && denseMsgEqCert domIdx b' b && densePdFirst bs domIdx bis b')) = true := by
        by_cases hh : ((bis.take i).any (fun b' => !bs.isStateful b'.busId
            && denseMsgEqCert domIdx b' b && densePdFirst bs domIdx bis b')) = true
        · exact hh
        · exact absurd (by simpa using hh) hany
      obtain ⟨b'', hb''mem, hb''⟩ := List.any_eq_true.1 hany'
      rw [Bool.and_eq_true, Bool.and_eq_true] at hb''
      obtain ⟨⟨hnst, hcert⟩, _⟩ := hb''
      have hall := List.all_eq_true.mp h b'' hb''mem
      rw [Bool.or_eq_true] at hall
      rcases hall with hst | hnc
      · rw [Bool.not_eq_true'] at hnst
        rw [hnst] at hst
        exact absurd hst (by simp)
      · rw [Bool.not_eq_true'] at hnc
        rw [hcert] at hnc
        exact absurd hnc (by simp)

/-- Pointwise-duplicate drop correctness, over an arbitrary keep-predicate that only drops
    certified-droppable interactions (`hkeep`). A dropped interaction's first-of-class twin is kept,
    so it is accepted. `ffPdDropWith` instantiates `keep` with the verdict map. -/
theorem DensePassCorrect.densePointwiseDupDrop [Fact p.Prime]
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (keep : BusInteraction (DenseExpr p) → Bool)
    (hkeep : ∀ bi ∈ d.busInteractions, keep bi = false →
      densePdKeep bs (denseVarBucket DenseExpr.vars (denseSingleVarCs d.algebraicConstraints))
        d.busInteractions bi = false) :
    DensePassCorrect isInput d (d.filterBus keep) [] bs := by
  refine DensePassCorrect.denseFilterBusEntailed d bs isInput keep ?_ ?_
  · intro bi hbimem hkf
    have hkf' := hkeep bi hbimem hkf
    unfold densePdKeep at hkf'
    rw [Bool.or_eq_false_iff] at hkf'
    simpa using hkf'.1
  · intro bi hbimem hkf denv hsat hm
    have hkf' := hkeep bi hbimem hkf
    unfold densePdKeep at hkf'
    rw [Bool.or_eq_false_iff] at hkf'
    obtain ⟨_hst, hmatch⟩ := hkf'
    cases hidx : d.busInteractions.findIdx? (fun x => x == bi) with
    | none => rw [hidx] at hmatch; simp at hmatch
    | some i =>
        rw [hidx] at hmatch
        simp only [Bool.not_eq_false'] at hmatch
        obtain ⟨b, hbmem, hb⟩ := List.any_eq_true.1 hmatch
        rw [Bool.and_eq_true, Bool.and_eq_true] at hb
        obtain ⟨⟨hnst, hcert⟩, hfirst⟩ := hb
        have hbcs : b ∈ d.busInteractions := List.mem_of_mem_take hbmem
        have hbkeep : densePdKeep bs
            (denseVarBucket DenseExpr.vars (denseSingleVarCs d.algebraicConstraints))
            d.busInteractions b = true :=
          densePdFirst_keep bs
            (denseVarBucket DenseExpr.vars (denseSingleVarCs d.algebraicConstraints))
            d.busInteractions b hfirst
        have hbkept : keep b = true := by
          by_contra hkb
          have := hkeep b hbcs (by simpa using hkb)
          rw [this] at hbkeep
          exact absurd hbkeep (by simp)
        have hbout : b ∈ (d.filterBus keep).busInteractions :=
          List.mem_filter.2 ⟨hbcs, hbkept⟩
        have hdom : ∀ v, ∀ c ∈ denseVarBucketLookup
            (denseVarBucket DenseExpr.vars (denseSingleVarCs d.algebraicConstraints)) v,
            c.eval denv = 0 := by
          intro v c hc
          exact hsat.1 c (List.mem_of_mem_filter
            (denseVarBucket_mem DenseExpr.vars (denseSingleVarCs d.algebraicConstraints) v c hc))
        have heq : denseBIEval b denv = denseBIEval bi denv :=
          denseMsgEqCert_sound
            (denseVarBucket DenseExpr.vars (denseSingleVarCs d.algebraicConstraints))
            b bi hcert denv hdom
        have hob := hsat.2 b hbout
        rw [heq] at hob
        exact hob hm

/-- A `densePdVerdictKeep` drop carries its certificate (the bucket entry equals `bi`). -/
theorem densePdVerdictKeep_false {p : ℕ} {P : BusInteraction (DenseExpr p) → Prop}
    (verdicts : Std.HashMap UInt64 (List { b : BusInteraction (DenseExpr p) // P b }))
    (bi : BusInteraction (DenseExpr p)) (h : densePdVerdictKeep verdicts bi = false) : P bi := by
  unfold densePdVerdictKeep at h
  cases hv : verdicts[densePdValHash bi]? with
  | none => rw [hv] at h; simp at h
  | some l =>
    rw [hv] at h
    simp only [Bool.not_eq_false'] at h
    obtain ⟨b, _hb, hbe⟩ := List.any_eq_true.1 h
    exact of_decide_eq_true hbe ▸ b.property

/-! ## Part D's drop -/

theorem ffPdDropWith_covered {reg : VarRegistry} (bs : BusSemantics p)
    (d : DenseConstraintSystem p)
    (drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) (hcov : d.CoveredBy reg) :
    (ffPdDropWith bs d drops).CoveredBy reg := by
  unfold ffPdDropWith
  split_ifs with hE
  · exact hcov
  · exact DenseConstraintSystem.filterBus_covered hcov

theorem ffPdDropWith_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p)
    (drops : Std.HashMap UInt64 (List (BusInteraction (DenseExpr p)))) :
    DensePassCorrect isInput d (ffPdDropWith bs d drops) [] bs := by
  unfold ffPdDropWith
  split_ifs with hE
  · exact DensePassCorrect.refl isInput d bs
  · refine DensePassCorrect.densePointwiseDupDrop d bs isInput _ ?_
    intro bi _ hkf
    exact densePdVerdictKeep_false _ bi hkf

/-! ## The fused pass -/

theorem denseFlagFoldF_covered (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) : (denseFlagFoldF pw b bs facts d).CoveredBy reg := by
  unfold denseFlagFoldF
  split_ifs with hp
  · refine ffPdDropWith_covered bs _ _ ?_
    rw [ffBoxTauto_eq]
    refine DenseConstraintSystem.boxTautoReplaceWith_covered _ ?_
    split_ifs with hover
    · exact DenseConstraintSystem.boxRewrite_covered _ b
        (denseFxSubstF_covered pw reg bs facts d hcov)
    · exact denseFxSubstF_covered pw reg bs facts d hcov
  · exact hcov

theorem denseFlagFoldF_correct (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseFlagFoldF pw b bs facts d) [] bs
      (denseFxSubstFHints pw bs facts d).expr := by
  unfold denseFlagFoldF
  split_ifs with hp
  · haveI : Fact p.Prime := ⟨pw.correct hp⟩
    set d1 := denseFxSubstF pw bs facts d with hd1
    have hA : DensePassCorrect reg.isInput d d1 [] bs (denseFxSubstFHints pw bs facts d).expr :=
      denseFxSubstF_correct pw reg bs facts d hcov
    set d2 := (if ffAnyOverBound b d1
      then d1.boxRewriteWith (ffTabGet (ffTabOf (ffBucketsOf d1.algebraicConstraints))) b
      else d1) with hd2
    have hB : DensePassCorrect reg.isInput d1 d2 [] bs := by
      rw [hd2]
      split_ifs with hover
      · exact DenseConstraintSystem.boxRewrite_denseCorrect d1 bs reg.isInput
          (ffBucketOf (ffBucketsOf d1.algebraicConstraints))
          (fun v c hc => ffBucketsOf_mem d1.algebraicConstraints v c hc)
          _ (fun v dm hv => ffTab_domOf d1.algebraicConstraints v dm hv) b
      · exact DensePassCorrect.refl reg.isInput d1 bs
    have hC : DensePassCorrect reg.isInput d2
        (d2.ffBoxTauto (ffTabOf (ffBucketsOf d2.algebraicConstraints))) [] bs := by
      rw [ffBoxTauto_eq]
      exact DenseConstraintSystem.boxTautoReplace_denseCorrect d2 bs reg.isInput
        (ffBucketOf (ffBucketsOf d2.algebraicConstraints))
        (fun v c hc => ffBucketsOf_mem d2.algebraicConstraints v c hc)
        _ (fun v dm hv => ffTab_domOf d2.algebraicConstraints v dm hv)
    simpa using (hA.trans hB).trans
      (hC.trans (ffPdDropWith_correct bs reg.isInput _ _))
  · simpa [denseFxSubstFHints, hp] using DensePassCorrect.refl reg.isInput d bs

/-- The dense `flagFold` pass: substitute entailed nonlinear interpolations, rewrite over-bound
    survivors multilinearly, drop box tautologies and pointwise stateless-check duplicates.
    Unguarded here — box-rewrite intermediates legitimately exceed the bound — so the whole chain
    runs under ONE `guardDegree b` at its `cleanupPasses` entry. -/
def denseFlagFoldPass' (pw : PrimeWitness p) (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofWithHints (denseFxSubstFHints pw) (denseFlagFoldF pw b) (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseFlagFoldF_covered pw b reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseFlagFoldF_correct pw b reg bs facts d hcov)

end ApcOptimizer.Dense
