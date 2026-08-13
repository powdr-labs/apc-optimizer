import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.ExprOps
import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Dense affine normalization

`DenseExpr.normalize` replaces every maximal affine subexpression by its merged normal form
(`denseLinearize` → combine like terms → drop zeros → `DenseLinExpr.toExpr`). The pass
(`denseNormalizePass`) maps it over the system; same shape as `denseConstantFoldPass`
(`ExprOps.lean`). Its runtime is the single walk `denseNormalizeFast` below. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Merging a dense linear form's terms -/

/-- Add coefficient `c` to `VarId` `v` in a dense term list, merging into an existing entry. -/
def denseAddCoeff (v : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p)
  | [] => [(v, c)]
  | (v', c') :: rest => if v' = v then (v', c' + c) :: rest else (v', c') :: denseAddCoeff v c rest

/-- Merge a dense term list, combining coefficients of equal `VarId`s (`foldl`, first-occurrence
    order preserved). -/
def denseMergeTerms (ts : List (VarId × ZMod p)) : List (VarId × ZMod p) :=
  ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) []

/-! ## Linear like-term merge (runtime `@[csimp]` replacement for `denseMergeTerms`)

`denseMergeTermsFast` merges via a `Std.HashMap` keyed by `VarId` (O(terms) vs the list fold's
O(terms²)), with a list-fold fast path for small inputs. Proven `= denseMergeTerms` and installed
via `@[csimp]`, so every call site uses it at runtime with no further proof obligation. -/

/-- The coefficient the accumulator holds for `v` (the coefficient of its unique entry, if any). -/
def denseAssocCoeff : List (VarId × ZMod p) → VarId → Option (ZMod p)
  | [], _ => none
  | (v', c') :: rest, v => if v' = v then some c' else denseAssocCoeff rest v

theorem denseNotMem_of_assocCoeff_none (acc : List (VarId × ZMod p)) (v : VarId)
    (h : denseAssocCoeff acc v = none) : v ∉ acc.map Prod.fst := by
  induction acc with
  | nil => simp
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAssocCoeff] at h
      split at h
      · exact absurd h (by simp)
      · next hne =>
          simp only [List.map_cons, List.mem_cons, not_or]
          exact ⟨fun hh => hne hh.symm, ih h⟩

theorem denseMem_of_assocCoeff_some (acc : List (VarId × ZMod p)) (v : VarId) (c : ZMod p)
    (h : denseAssocCoeff acc v = some c) : v ∈ acc.map Prod.fst := by
  induction acc with
  | nil => simp [denseAssocCoeff] at h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAssocCoeff] at h
      simp only [List.map_cons, List.mem_cons]
      split at h
      · next he => exact Or.inl he.symm
      · next hne => exact Or.inr (ih h)

/-- The effect of one `denseAddCoeff` on `denseAssocCoeff`: bump `v`'s coefficient (0 if absent),
    leave every other variable untouched. -/
theorem denseAssocCoeff_addCoeff (v : VarId) (c : ZMod p) (acc : List (VarId × ZMod p))
    (w : VarId) :
    denseAssocCoeff (denseAddCoeff v c acc) w
      = if w = v then some ((denseAssocCoeff acc v).getD 0 + c) else denseAssocCoeff acc w := by
  induction acc with
  | nil =>
      simp only [denseAddCoeff, denseAssocCoeff, Option.getD_none, zero_add]
      by_cases hwv : w = v
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeff]
      by_cases hv' : v' = v
      · rw [if_pos hv']
        subst hv'
        simp only [denseAssocCoeff]
        by_cases hwv : w = v'
        · subst hwv; simp
        · have hwv' : ¬ v' = w := fun he => hwv he.symm
          simp only [if_neg hwv, if_neg hwv']
      · rw [if_neg hv']
        simp only [denseAssocCoeff, ih]
        rw [if_neg hv']
        by_cases hv'w : v' = w
        · have hwv : ¬ w = v := fun he => hv' (hv'w.trans he)
          rw [if_pos hv'w, if_neg hwv, if_pos hv'w]
        · rw [if_neg hv'w, if_neg hv'w]

theorem denseAddCoeff_map_fst_of_mem (v : VarId) (c : ZMod p) (acc : List (VarId × ZMod p))
    (h : v ∈ acc.map Prod.fst) : (denseAddCoeff v c acc).map Prod.fst = acc.map Prod.fst := by
  induction acc with
  | nil => simp at h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeff]
      split
      · next he => simp
      · next hne =>
          simp only [List.map_cons, List.mem_cons] at h
          have hmem : v ∈ rest.map Prod.fst := by
            rcases h with h | h
            · exact absurd h.symm hne
            · exact h
          simp [ih hmem]

theorem denseAddCoeff_append_of_not_mem (v : VarId) (c : ZMod p) (acc : List (VarId × ZMod p))
    (h : v ∉ acc.map Prod.fst) : denseAddCoeff v c acc = acc ++ [(v, c)] := by
  induction acc with
  | nil => simp [denseAddCoeff]
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [List.map_cons, List.mem_cons, not_or] at h
      obtain ⟨hne, hrest⟩ := h
      simp only [denseAddCoeff]
      rw [if_neg (fun he => hne he.symm)]
      simp [ih hrest]

/-- One step of the fast merge: bump `t.1`'s coefficient in the map, appending `t.1` to the order
    array on first occurrence. -/
def denseMtStep (st : Array VarId × Std.HashMap VarId (ZMod p)) (t : VarId × ZMod p) :
    Array VarId × Std.HashMap VarId (ZMod p) :=
  match st.2[t.1]? with
  | some c0 => (st.1, st.2.insert t.1 (c0 + t.2))
  | none => (st.1.push t.1, st.2.insert t.1 t.2)

/-- Correspondence invariant tying the fast `(order, map)` state to the `denseAddCoeff`-fold list. -/
def DenseMergeCorr (acc : List (VarId × ZMod p)) (order : Array VarId)
    (m : Std.HashMap VarId (ZMod p)) : Prop :=
  order.toList = acc.map Prod.fst ∧ (acc.map Prod.fst).Nodup ∧ ∀ v, m[v]? = denseAssocCoeff acc v

theorem denseMtStep_corr (acc : List (VarId × ZMod p)) (order : Array VarId)
    (m : Std.HashMap VarId (ZMod p)) (t : VarId × ZMod p) (h : DenseMergeCorr acc order m) :
    DenseMergeCorr (denseAddCoeff t.1 t.2 acc) (denseMtStep (order, m) t).1
      (denseMtStep (order, m) t).2 := by
  obtain ⟨hord, hnod, hm⟩ := h
  obtain ⟨tv, tc⟩ := t
  have hmtv := hm tv
  rcases hcase : (m[tv]? : Option (ZMod p)) with _ | c0
  · have habs : denseAssocCoeff acc tv = none := by rw [← hmtv, hcase]
    have hnmem : tv ∉ acc.map Prod.fst := denseNotMem_of_assocCoeff_none acc tv habs
    have hstep : denseMtStep (order, m) (tv, tc) = (order.push tv, m.insert tv tc) := by
      simp only [denseMtStep, hcase]
    have hfst : (denseAddCoeff tv tc acc).map Prod.fst = acc.map Prod.fst ++ [tv] := by
      rw [denseAddCoeff_append_of_not_mem tv tc acc hnmem]; simp
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst, Array.toList_push, hord]
    · rw [hfst]
      exact hnod.append (List.nodup_singleton tv) (List.disjoint_singleton.2 hnmem)
    · intro w
      rw [Std.HashMap.getElem?_insert, denseAssocCoeff_addCoeff, habs]
      simp only [beq_iff_eq, Option.getD_none, zero_add]
      by_cases hwv : tv = w
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
        exact hm w
  · have hpres : denseAssocCoeff acc tv = some c0 := by rw [← hmtv, hcase]
    have hmem : tv ∈ acc.map Prod.fst := denseMem_of_assocCoeff_some acc tv c0 hpres
    have hstep : denseMtStep (order, m) (tv, tc) = (order, m.insert tv (c0 + tc)) := by
      simp only [denseMtStep, hcase]
    have hfst : (denseAddCoeff tv tc acc).map Prod.fst = acc.map Prod.fst :=
      denseAddCoeff_map_fst_of_mem tv tc acc hmem
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst]; exact hord
    · rw [hfst]; exact hnod
    · intro w
      rw [Std.HashMap.getElem?_insert, denseAssocCoeff_addCoeff, hpres]
      simp only [beq_iff_eq, Option.getD_some]
      by_cases hwv : tv = w
      · subst hwv; simp
      · rw [if_neg hwv, if_neg (fun he => hwv he.symm)]
        exact hm w

theorem denseMtFold_corr (ts : List (VarId × ZMod p)) :
    ∀ (acc : List (VarId × ZMod p)) (order : Array VarId)
      (m : Std.HashMap VarId (ZMod p)), DenseMergeCorr acc order m →
      DenseMergeCorr (ts.foldl (fun a t => denseAddCoeff t.1 t.2 a) acc)
        (ts.foldl denseMtStep (order, m)).1 (ts.foldl denseMtStep (order, m)).2 := by
  induction ts with
  | nil => intro acc order m h; simpa using h
  | cons t rest ih =>
      intro acc order m h
      simp only [List.foldl_cons]
      exact ih (denseAddCoeff t.1 t.2 acc) (denseMtStep (order, m) t).1
        (denseMtStep (order, m) t).2 (denseMtStep_corr acc order m t h)

theorem denseReconAssoc (acc : List (VarId × ZMod p)) (hnod : (acc.map Prod.fst).Nodup) :
    (acc.map Prod.fst).map (fun v => (v, (denseAssocCoeff acc v).getD 0)) = acc := by
  induction acc with
  | nil => simp
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [List.map_cons] at hnod ⊢
      rw [List.nodup_cons] at hnod
      obtain ⟨hnotin, hnod'⟩ := hnod
      have hhead : (denseAssocCoeff ((v', c') :: rest) v').getD 0 = c' := by simp [denseAssocCoeff]
      have htail : (rest.map Prod.fst).map
          (fun v => (v, (denseAssocCoeff ((v', c') :: rest) v).getD 0))
          = (rest.map Prod.fst).map (fun v => (v, (denseAssocCoeff rest v).getD 0)) := by
        apply List.map_congr_left
        intro v hv
        have hvne : ¬ v' = v := fun he => hnotin (he ▸ hv)
        simp [denseAssocCoeff, if_neg hvne]
      rw [hhead, htail, ih hnod']

theorem denseRecon (acc : List (VarId × ZMod p)) (order : Array VarId)
    (m : Std.HashMap VarId (ZMod p)) (h : DenseMergeCorr acc order m) :
    order.toList.map (fun v => (v, (m[v]?).getD 0)) = acc := by
  obtain ⟨hord, hnod, hm⟩ := h
  rw [hord]
  rw [show (fun v => (v, (m[v]?).getD 0)) = (fun v => (v, (denseAssocCoeff acc v).getD 0)) from
    funext (fun v => by rw [hm v])]
  exact denseReconAssoc acc hnod

/-- Boxed twins of the merge steps: `p` is a runtime value, so each inline `+`/`0` rebuilds the
    whole `CommRing (ZMod p)` chain. Threading a `DenseZModOps p` costs one chain per merged list
    instead of one per term. -/
def denseAddCoeffWith (ops : DenseZModOps p) (v : VarId) (c : ZMod p) :
    List (VarId × ZMod p) → List (VarId × ZMod p)
  | [] => [(v, c)]
  | (v', c') :: rest =>
      if v' = v then (v', ops.add c' c) :: rest
      else (v', c') :: denseAddCoeffWith ops v c rest

theorem denseAddCoeffWith_eq (ops : DenseZModOps p) (v : VarId) (c : ZMod p)
    (ts : List (VarId × ZMod p)) : denseAddCoeffWith ops v c ts = denseAddCoeff v c ts := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeffWith, denseAddCoeff, ops.add_eq, ih]

def denseMtStepWith (ops : DenseZModOps p) (st : Array VarId × Std.HashMap VarId (ZMod p))
    (t : VarId × ZMod p) : Array VarId × Std.HashMap VarId (ZMod p) :=
  match st.2[t.1]? with
  | some c0 => (st.1, st.2.insert t.1 (ops.add c0 t.2))
  | none => (st.1.push t.1, st.2.insert t.1 t.2)

theorem denseMtStepWith_eq (ops : DenseZModOps p) :
    denseMtStepWith (p := p) ops = denseMtStep := by
  funext st t
  simp only [denseMtStepWith, denseMtStep, ops.add_eq]

/-- The dense linear like-term merge. Proven `= denseMergeTerms`; `denseMergeTermsFast` below
    installs it via `@[csimp]`. -/
def denseMergeTermsWith (ops : DenseZModOps p) (ts : List (VarId × ZMod p)) :
    List (VarId × ZMod p) :=
  if ts.length ≤ 32 then
    ts.foldl (fun acc t => denseAddCoeffWith ops t.1 t.2 acc) []
  else
    let st := ts.foldl (denseMtStepWith ops) (#[], ∅)
    st.1.toList.map (fun v => (v, (st.2[v]?).getD ops.zero))

def denseMergeTermsFast (ts : List (VarId × ZMod p)) : List (VarId × ZMod p) :=
  denseMergeTermsWith denseZModOps ts

theorem denseMergeTermsWith_eq (ops : DenseZModOps p) (ts : List (VarId × ZMod p)) :
    denseMergeTermsWith ops ts = denseMergeTerms ts := by
  simp only [denseMergeTermsWith, denseAddCoeffWith_eq, denseMtStepWith_eq, ops.zero_eq]
  split
  · rfl
  · have hbase : DenseMergeCorr ([] : List (VarId × ZMod p)) (#[] : Array VarId)
        (∅ : Std.HashMap VarId (ZMod p)) :=
      ⟨by simp, by simp, fun v => by simp [denseAssocCoeff]⟩
    have hcorr := denseMtFold_corr ts [] #[] ∅ hbase
    exact denseRecon _ _ _ hcorr

@[csimp] theorem denseMergeTerms_eq_fast : @denseMergeTerms = @denseMergeTermsFast := by
  funext p ts
  exact (denseMergeTermsWith_eq denseZModOps ts).symm

/-- The fully-merged normal form of a dense linear form: combine like terms, drop zeros. -/
def DenseLinExpr.norm (l : DenseLinExpr p) : DenseLinExpr p :=
  ⟨l.const, (denseMergeTerms l.terms).filter (fun t => t.2 ≠ 0)⟩

/-- Boxed twin of the zero-drop: without it the `≠ 0` test rebuilds the instance chain per term. -/
def denseDropZeroWith (ops : DenseZModOps p) :
    List (VarId × ZMod p) → List (VarId × ZMod p)
  | [] => []
  | t :: ts => if t.2 = ops.zero then denseDropZeroWith ops ts else t :: denseDropZeroWith ops ts

theorem denseDropZeroWith_eq (ops : DenseZModOps p) (ts : List (VarId × ZMod p)) :
    denseDropZeroWith ops ts = ts.filter (fun t => t.2 ≠ 0) := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      by_cases hz : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using hz)]
        simp only [denseDropZeroWith, ops.zero_eq, if_pos hz, ih]
      · rw [List.filter_cons_of_pos (by simpa using hz)]
        simp only [denseDropZeroWith, ops.zero_eq, if_neg hz, ih]

/-- One `DenseZModOps p` for the whole normal form: the merge and the zero-drop share it. -/
def DenseLinExpr.normWith (ops : DenseZModOps p) (l : DenseLinExpr p) : DenseLinExpr p :=
  ⟨l.const, denseDropZeroWith ops (denseMergeTermsWith ops l.terms)⟩

def DenseLinExpr.normFast (l : DenseLinExpr p) : DenseLinExpr p :=
  DenseLinExpr.normWith denseZModOps l

theorem DenseLinExpr.normWith_eq (ops : DenseZModOps p) (l : DenseLinExpr p) :
    l.normWith ops = l.norm := by
  simp only [DenseLinExpr.normWith, DenseLinExpr.norm, denseMergeTermsWith_eq, denseDropZeroWith_eq]

@[csimp] theorem DenseLinExpr.norm_eq_fast : @DenseLinExpr.norm = @DenseLinExpr.normFast := by
  funext p l
  exact (DenseLinExpr.normWith_eq denseZModOps l).symm

/-! ## The dense normalization traversal -/

/-- Affine normalization: replace each maximal affine subexpression by its merged linear form (like
    terms combined, zero terms dropped), recursing into genuine variable×variable products.
    E.g. `2*x + 3 + x` normalizes to `3 + 3*x`. -/
def DenseExpr.normalize : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var x => .var x
  | .add a b =>
      match denseLinearize (DenseExpr.add a b) with
      | some l => l.norm.toExpr
      | none => .add a.normalize b.normalize
  | .mul a b =>
      match denseLinearize (DenseExpr.mul a b) with
      | some l => l.norm.toExpr
      | none => .mul a.normalize b.normalize

/-! ## Eval-preservation of the merge / normal form

The affine-form eval lemmas (`denseLinearize_eval` etc.) live in `Affine.lean`. -/

theorem denseAddCoeff_eval (v : VarId) (c : ZMod p) (ts : List (VarId × ZMod p))
    (denv : VarId → ZMod p) :
    ((denseAddCoeff v c ts).map (fun t => t.2 * denv t.1)).sum
      = c * denv v + (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => simp [denseAddCoeff]
  | cons t rest ih =>
      simp only [denseAddCoeff]
      split
      · next h => subst h; simp only [List.map_cons, List.sum_cons]; ring
      · simp only [List.map_cons, List.sum_cons, ih]; ring

theorem denseFoldAddCoeff_eval (denv : VarId → ZMod p) (ts acc : List (VarId × ZMod p)) :
    ((ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) acc).map (fun t => t.2 * denv t.1)).sum
      = (acc.map (fun t => t.2 * denv t.1)).sum + (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, denseAddCoeff_eval]
      ring

theorem denseMergeTerms_eval (ts : List (VarId × ZMod p)) (denv : VarId → ZMod p) :
    ((denseMergeTerms ts).map (fun t => t.2 * denv t.1)).sum
      = (ts.map (fun t => t.2 * denv t.1)).sum := by
  simp [denseMergeTerms, denseFoldAddCoeff_eval]

theorem denseDropZero_eval (ts : List (VarId × ZMod p)) (denv : VarId → ZMod p) :
    ((ts.filter (fun t => t.2 ≠ 0)).map (fun t => t.2 * denv t.1)).sum
      = (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons, h]
        simp
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
            List.map_cons, List.sum_cons]

theorem DenseLinExpr.norm_eval (l : DenseLinExpr p) (denv : VarId → ZMod p) :
    l.norm.eval denv = l.eval denv := by
  simp only [DenseLinExpr.norm, DenseLinExpr.eval, denseDropZero_eval, denseMergeTerms_eval]

theorem DenseExpr.normalize_eval (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.normalize.eval denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb =>
      rw [DenseExpr.normalize]
      cases hl : denseLinearize (DenseExpr.add a b) with
      | some l =>
          rw [DenseLinExpr.toExpr_eval, DenseLinExpr.norm_eval, ← denseLinearize_eval _ l hl]
      | none =>
          simp only [DenseExpr.eval, iha, ihb]
  | mul a b iha ihb =>
      rw [DenseExpr.normalize]
      cases hl : denseLinearize (DenseExpr.mul a b) with
      | some l =>
          rw [DenseLinExpr.toExpr_eval, DenseLinExpr.norm_eval, ← denseLinearize_eval _ l hl]
      | none =>
          simp only [DenseExpr.eval, iha, ihb]

/-! ## OutputVariable bounds (`normalize` introduces no new variable) -/

theorem denseAddCoeff_fst (v : VarId) (c : ZMod p) (ts : List (VarId × ZMod p)) (x : VarId)
    (h : x ∈ (denseAddCoeff v c ts).map Prod.fst) : x = v ∨ x ∈ ts.map Prod.fst := by
  induction ts with
  | nil =>
      simp only [denseAddCoeff, List.map_cons, List.map_nil, List.mem_singleton] at h
      exact Or.inl h
  | cons t rest ih =>
      obtain ⟨v', c'⟩ := t
      simp only [denseAddCoeff] at h
      split at h
      · rename_i hv
        simp only [List.map_cons, List.mem_cons] at h ⊢
        tauto
      · simp only [List.map_cons, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact (ih h).imp id (Or.inr ·)

theorem denseFoldAddCoeff_fst (ts : List (VarId × ZMod p)) :
    ∀ (init : List (VarId × ZMod p)) (x : VarId),
      x ∈ (ts.foldl (fun acc t => denseAddCoeff t.1 t.2 acc) init).map Prod.fst →
      x ∈ init.map Prod.fst ∨ x ∈ ts.map Prod.fst := by
  induction ts with
  | nil => intro init x hx; exact Or.inl hx
  | cons t rest ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with h | h
      · rcases denseAddCoeff_fst t.1 t.2 init x h with h | h
        · exact Or.inr (by simp [h])
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem denseMergeTerms_fst (ts : List (VarId × ZMod p)) (x : VarId)
    (h : x ∈ (denseMergeTerms ts).map Prod.fst) : x ∈ ts.map Prod.fst := by
  rcases denseFoldAddCoeff_fst ts [] x h with h | h
  · simp at h
  · exact h

theorem DenseLinExpr.norm_terms_fst (l : DenseLinExpr p) (x : VarId)
    (h : x ∈ l.norm.terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [DenseLinExpr.norm, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact denseMergeTerms_fst l.terms t.1 (List.mem_map.2 ⟨t, List.mem_of_mem_filter ht, rfl⟩)

theorem denseToExpr_foldl_vars (terms : List (VarId × ZMod p)) :
    ∀ (init : DenseExpr p) (x : VarId),
      x ∈ (terms.foldl
          (fun acc t => DenseExpr.add acc (DenseExpr.mul (.const t.2) (.var t.1))) init).vars →
      x ∈ init.vars ∨ x ∈ terms.map Prod.fst := by
  induction terms with
  | nil => intro init x hx; exact Or.inl hx
  | cons t rest ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with h | h
      · simp only [DenseExpr.vars, List.mem_append, List.nil_append, List.mem_singleton] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by subst h; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem DenseLinExpr.toExpr_vars (l : DenseLinExpr p) :
    ∀ x ∈ l.toExpr.vars, x ∈ l.terms.map Prod.fst := by
  intro x hx
  rcases denseToExpr_foldl_vars l.terms _ x hx with h | h
  · simp [DenseExpr.vars] at h
  · exact h

theorem DenseLinExpr.scale_terms_fst (k : ZMod p) (l : DenseLinExpr p) :
    (l.scale k).terms.map Prod.fst = l.terms.map Prod.fst := by
  simp [DenseLinExpr.scale, List.map_map, Function.comp_def]

theorem denseLinearize_vars (e : DenseExpr p) (l : DenseLinExpr p) (h : denseLinearize e = some l) :
    ∀ i ∈ l.terms.map Prod.fst, i ∈ e.vars := by
  induction e generalizing l with
  | const n => simp only [denseLinearize, Option.some.injEq] at h; subst h; simp
  | var y =>
      simp only [denseLinearize, Option.some.injEq] at h; subst h
      intro x hx; simpa [DenseExpr.vars] using hx
  | add a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          simp only [denseLinearize, hla, hlb, Option.some.injEq] at h
          subst h
          intro x hx
          simp only [DenseLinExpr.add, List.map_append, List.mem_append] at hx
          simp only [DenseExpr.vars, List.mem_append]
          exact hx.imp (iha la hla x) (ihb lb hlb x)
  | mul a b iha ihb =>
      cases hla : denseLinearize a with
      | none => simp [denseLinearize, hla] at h
      | some la => cases hlb : denseLinearize b with
        | none => simp [denseLinearize, hla, hlb] at h
        | some lb =>
          by_cases h1 : la.terms.isEmpty = true
          · simp only [denseLinearize, hla, hlb, if_pos h1, Option.some.injEq] at h
            subst h
            intro x hx
            rw [DenseLinExpr.scale_terms_fst] at hx
            exact List.mem_append.2 (Or.inr (ihb lb hlb x hx))
          · by_cases h2 : lb.terms.isEmpty = true
            · simp only [denseLinearize, hla, hlb, if_neg h1, if_pos h2, Option.some.injEq] at h
              subst h
              intro x hx
              rw [DenseLinExpr.scale_terms_fst] at hx
              exact List.mem_append.2 (Or.inl (iha la hla x hx))
            · simp only [denseLinearize, hla, hlb] at h
              rw [if_neg h1, if_neg h2] at h
              exact absurd h (by simp)

theorem DenseExpr.normalize_vars (e : DenseExpr p) : ∀ i ∈ e.normalize.vars, i ∈ e.vars := by
  induction e with
  | const n => intro i hi; simpa [DenseExpr.normalize] using hi
  | var y => intro i hi; simpa [DenseExpr.normalize] using hi
  | add a b iha ihb =>
      intro i hi
      simp only [DenseExpr.normalize] at hi
      split at hi
      · rename_i l hl
        exact denseLinearize_vars _ l hl i (l.norm_terms_fst i (DenseLinExpr.toExpr_vars _ i hi))
      · simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        exact hi.imp (iha i) (ihb i)
  | mul a b iha ihb =>
      intro i hi
      simp only [DenseExpr.normalize] at hi
      split at hi
      · rename_i l hl
        exact denseLinearize_vars _ l hl i (l.norm_terms_fst i (DenseLinExpr.toExpr_vars _ i hi))
      · simp only [DenseExpr.vars, List.mem_append] at hi ⊢
        exact hi.imp (iha i) (ihb i)

/-! ## The runtime walk (`@[csimp]` replacement for `DenseExpr.normalize`)

`DenseExpr.normalize` re-runs `denseLinearize` over the whole node at every node it visits, which
is quadratic. The runtime walk visits each node once, carries the affine content of a node as a
constant plus an *un-merged* term list built onto the caller's accumulator, and materializes
`norm.toExpr` only where a parent cannot absorb it. -/

/-- The walk's result for a compound node. In `lin c n ts`, `ts` is this node's terms in
    left-to-right order consed onto the caller's accumulator and `n` is how many of them are this
    node's — so a sibling that turns out non-affine can still materialize this node from a counted
    prefix. Leaves never reach here: a parent handles `.const`/`.var` children inline (a bare
    variable normalizes to itself, not to `0 + 1·x`). -/
inductive DenseNrm (p : ℕ) where
  | lin (c : ZMod p) (n : Nat) (ts : List (VarId × ZMod p))
  | opq (e : DenseExpr p)

/-- `DenseLinExpr.toExpr`'s spine over merged terms, dropping the zero coefficients on the way, so
    the zero-drop never builds a list of its own. -/
def denseNrmSpine (e : DenseExpr p) : List (VarId × ZMod p) → DenseExpr p
  | [] => e
  | t :: ts =>
      denseNrmSpine (if zmodIsZero t.2 then e else .add e (.mul (.const t.2) (.var t.1))) ts

/-- Materialize an affine node from the first `n` cells of `ts`: merge like terms, drop zeros and
    build the `toExpr` spine. The corpus's affine forms hold 1.6 terms on average, and the constant
    and single-term arms serve those without touching the merge at all. -/
def denseNrmMat (c : ZMod p) (n : Nat) (ts : List (VarId × ZMod p)) : DenseExpr p :=
  match n, ts with
  | 0, _ => .const c
  | 1, t :: _ =>
      if zmodIsZero t.2 then .const c else .add (.const c) (.mul (.const t.2) (.var t.1))
  | n, ts => denseNrmSpine (.const c) (denseMergeTerms (ts.take n))

def DenseNrm.expr : DenseNrm p → DenseExpr p
  | .lin c n ts => denseNrmMat c n ts
  | .opq e => e

/-- `l.map (fun t => (t.1, k * t.2)) ++ rest` on the first `n` cells of `ts`. -/
def denseNrmScale (k : ZMod p) : Nat → List (VarId × ZMod p) → List (VarId × ZMod p)
  | 0, ts => ts
  | _ + 1, [] => []
  | n + 1, t :: ts => (t.1, zmodMul k t.2) :: denseNrmScale k n ts

/-- The walk. Called on compound nodes only; each arm inspects its children's constructors so a
    `.const`/`.var` child costs no result object. -/
def denseNrmGo : DenseExpr p → List (VarId × ZMod p) → DenseNrm p
  | .const n, acc => .lin n 0 acc
  | .var x, acc => .lin (zmodZeroP p) 1 ((x, zmodOneP p) :: acc)
  | .add a b, acc =>
      match b with
      | .const bn =>
          match a with
          | .const an => .lin (zmodAdd an bn) 0 acc
          | .var x => .lin bn 1 ((x, zmodOneP p) :: acc)
          | _ =>
              match denseNrmGo a acc with
              | .lin ca na ts => .lin (zmodAdd ca bn) na ts
              | .opq ea => .opq (.add ea (.const bn))
      | .var y =>
          let acc1 := (y, zmodOneP p) :: acc
          match a with
          | .const an => .lin an 1 acc1
          | .var x => .lin (zmodZeroP p) 2 ((x, zmodOneP p) :: acc1)
          | _ =>
              match denseNrmGo a acc1 with
              | .lin ca na ts => .lin ca (na + 1) ts
              | .opq ea => .opq (.add ea (.var y))
      | _ =>
          match denseNrmGo b acc with
          | .opq eb =>
              match a with
              | .const an => .opq (.add (.const an) eb)
              | .var x => .opq (.add (.var x) eb)
              | _ => .opq (.add (denseNrmGo a []).expr eb)
          | .lin cb nb tsb =>
              match a with
              | .const an => .lin (zmodAdd an cb) nb tsb
              | .var x => .lin cb (nb + 1) ((x, zmodOneP p) :: tsb)
              | _ =>
                  match denseNrmGo a tsb with
                  | .lin ca na tsa => .lin (zmodAdd ca cb) (na + nb) tsa
                  | .opq ea => .opq (.add ea (denseNrmMat cb nb tsb))
  | .mul a b, acc =>
      match a with
      | .const an =>
          match b with
          | .const bn => .lin (zmodMul an bn) 0 acc
          | .var y => .lin (zmodZeroP p) 1 ((y, an) :: acc)
          | _ =>
              match denseNrmGo b acc with
              | .lin cb nb tsb => .lin (zmodMul an cb) nb (denseNrmScale an nb tsb)
              | .opq eb => .opq (.mul (.const an) eb)
      | .var x =>
          match b with
          | .const bn => .lin (zmodZeroP p) 1 ((x, bn) :: acc)
          | .var y => .opq (.mul (.var x) (.var y))
          | _ =>
              match denseNrmGo b [] with
              | .lin cb 0 _ => .lin (zmodZeroP p) 1 ((x, cb) :: acc)
              | .lin cb nb tsb => .opq (.mul (.var x) (denseNrmMat cb nb tsb))
              | .opq eb => .opq (.mul (.var x) eb)
      | _ =>
          match denseNrmGo a acc with
          | .opq ea =>
              match b with
              | .const bn => .opq (.mul ea (.const bn))
              | .var y => .opq (.mul ea (.var y))
              | _ => .opq (.mul ea (denseNrmGo b []).expr)
          | .lin ca 0 tsa =>
              match b with
              | .const bn => .lin (zmodMul ca bn) 0 tsa
              | .var y => .lin (zmodZeroP p) 1 ((y, ca) :: tsa)
              | _ =>
                  match denseNrmGo b tsa with
                  | .lin cb nb tsb => .lin (zmodMul ca cb) nb (denseNrmScale ca nb tsb)
                  | .opq eb => .opq (.mul (.const ca) eb)
          | .lin ca na tsa =>
              match b with
              | .const bn => .lin (zmodMul ca bn) na (denseNrmScale bn na tsa)
              | .var y => .opq (.mul (denseNrmMat ca na tsa) (.var y))
              | _ =>
                  match denseNrmGo b [] with
                  | .lin cb 0 _ => .lin (zmodMul ca cb) na (denseNrmScale cb na tsa)
                  | .lin cb nb tsb =>
                      .opq (.mul (denseNrmMat ca na tsa) (denseNrmMat cb nb tsb))
                  | .opq eb => .opq (.mul (denseNrmMat ca na tsa) eb)

/-- Runtime `DenseExpr.normalize`. -/
def denseNormalizeFast : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var x => .var x
  | e => (denseNrmGo e []).expr

/-! ### The walk computes `DenseExpr.normalize`

`denseNrmMat_eq` pins the materializer to `norm.toExpr` and `denseNrmGo_eq` pins the walk to
(`denseLinearize`, `normalize`); the `@[csimp]` follows by reading both at the root.

The walk's arms inspect their children's constructors so a leaf costs no result object, which would
make the induction a 9-way bash per node. `denseNrmAddU`/`denseNrmMulU` are the same arms with every
child taken through `denseNrmGo` — equal to them by `denseNrmGo_add`/`denseNrmGo_mul`, which is pure
`ZMod`/`Nat` arithmetic — so the induction below only ever sees the uniform shape. -/

/-- One `toExpr` step, the body of the `DenseLinExpr.toExpr` fold. -/
abbrev denseNrmStep (acc : DenseExpr p) (t : VarId × ZMod p) : DenseExpr p :=
  .add acc (.mul (.const t.2) (.var t.1))

theorem denseNrmSpine_eq (ts : List (VarId × ZMod p)) (e : DenseExpr p) :
    denseNrmSpine e ts = (ts.filter (fun t => t.2 ≠ 0)).foldl denseNrmStep e := by
  induction ts generalizing e with
  | nil => rfl
  | cons t ts ih =>
      by_cases h : t.2 = 0
      · rw [List.filter_cons_of_neg (by simpa using h), denseNrmSpine, ih,
          if_pos (by simpa using h)]
      · rw [List.filter_cons_of_pos (by simpa using h), denseNrmSpine, ih,
          if_neg (by simpa using h), List.foldl_cons]

/-- The materializer builds the merged normal form of `⟨c, terms⟩` out of a counted prefix. -/
theorem denseNrmMat_eq (c : ZMod p) (terms acc : List (VarId × ZMod p)) :
    denseNrmMat c terms.length (terms ++ acc) = (DenseLinExpr.mk c terms).norm.toExpr := by
  have hgen : ∀ (l : List (VarId × ZMod p)),
      denseNrmSpine (.const c) (denseMergeTerms l) = (DenseLinExpr.mk c l).norm.toExpr := by
    intro l
    rw [denseNrmSpine_eq]
    rfl
  match terms with
  | [] => simpa [denseNrmMat] using (hgen []).symm
  | [t] =>
      have hm : denseMergeTerms [t] = [t] := by simp [denseMergeTerms, denseAddCoeff]
      by_cases h : t.2 = 0
      · rw [show ([t] : List (VarId × ZMod p)).length = 1 from rfl, List.cons_append,
          denseNrmMat, if_pos (by simpa using h), DenseLinExpr.norm, DenseLinExpr.toExpr, hm,
          List.filter_cons_of_neg (by simpa using h)]
        rfl
      · rw [show ([t] : List (VarId × ZMod p)).length = 1 from rfl, List.cons_append,
          denseNrmMat, if_neg (by simpa using h), DenseLinExpr.norm, DenseLinExpr.toExpr, hm,
          List.filter_cons_of_pos (by simpa using h)]
        rfl
  | t₁ :: t₂ :: rest =>
      have hlen : (t₁ :: t₂ :: rest).length = rest.length + 1 + 1 := by simp [Nat.add_comm]
      rw [hlen,
        show denseNrmMat c (rest.length + 1 + 1) ((t₁ :: t₂ :: rest) ++ acc)
            = denseNrmSpine (.const c)
                (denseMergeTerms (((t₁ :: t₂ :: rest) ++ acc).take (rest.length + 1 + 1)))
          from rfl,
        show ((t₁ :: t₂ :: rest) ++ acc).take (rest.length + 1 + 1) = t₁ :: t₂ :: rest by
          rw [← hlen]; exact List.take_left ..]
      exact hgen _

theorem denseNrmScale_eq (k : ZMod p) (terms acc : List (VarId × ZMod p)) :
    denseNrmScale k terms.length (terms ++ acc)
      = terms.map (fun t => (t.1, k * t.2)) ++ acc := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.length_cons, List.cons_append, denseNrmScale, zmodMul_eq, List.map_cons, ih]

/-- The normal form of a child from its walk result. The *shape* decides, not the linear form: a
    bare variable normalizes to itself, not to `0 + 1·x`. -/
def denseNrmChildExpr (e : DenseExpr p) (c : ZMod p) (n : Nat) (ts : List (VarId × ZMod p)) :
    DenseExpr p :=
  match e with
  | .var x => .var x
  | _ => denseNrmMat c n ts

/-- `denseNrmGo`'s `.add` arm with both children taken through `denseNrmGo`. -/
def denseNrmAddU (a b : DenseExpr p) (acc : List (VarId × ZMod p)) : DenseNrm p :=
  match denseNrmGo b acc with
  | .opq eb => .opq (.add (denseNormalizeFast a) eb)
  | .lin cb nb tsb =>
      match denseNrmGo a tsb with
      | .lin ca na tsa => .lin (zmodAdd ca cb) (na + nb) tsa
      | .opq ea => .opq (.add ea (denseNrmChildExpr b cb nb tsb))

/-- `denseNrmGo`'s `.mul` arm with both children taken through `denseNrmGo`. -/
def denseNrmMulU (a b : DenseExpr p) (acc : List (VarId × ZMod p)) : DenseNrm p :=
  match denseNrmGo a acc with
  | .opq ea => .opq (.mul ea (denseNormalizeFast b))
  | .lin ca 0 tsa =>
      match denseNrmGo b tsa with
      | .lin cb nb tsb => .lin (zmodMul ca cb) nb (denseNrmScale ca nb tsb)
      | .opq eb => .opq (.mul (denseNrmChildExpr a ca 0 tsa) eb)
  | .lin ca na tsa =>
      match denseNrmGo b [] with
      | .lin cb 0 _ => .lin (zmodMul ca cb) na (denseNrmScale cb na tsa)
      | .lin cb nb tsb =>
          .opq (.mul (denseNrmChildExpr a ca na tsa) (denseNrmChildExpr b cb nb tsb))
      | .opq eb => .opq (.mul (denseNrmChildExpr a ca na tsa) eb)

/-- The leaf arms, as rewrite rules that cannot fire on a compound child. Both rewrite by `rfl`,
    so the `simp` uses below leave no trace of them in the proof terms (hence the entries in
    `Scripts/unused-theorems.txt`). -/
@[simp] theorem denseNrmGo_const (n : ZMod p) (acc : List (VarId × ZMod p)) :
    denseNrmGo (.const n) acc = .lin n 0 acc := rfl

@[simp] theorem denseNrmGo_var (x : VarId) (acc : List (VarId × ZMod p)) :
    denseNrmGo (.var x) acc = .lin (zmodZeroP p) 1 ((x, zmodOneP p) :: acc) := rfl

theorem denseNrmGo_add (a b : DenseExpr p) (acc : List (VarId × ZMod p)) :
    denseNrmGo (.add a b) acc = denseNrmAddU a b acc := by
  cases a <;> cases b <;> rw [denseNrmGo, denseNrmAddU] <;>
    simp [denseNrmChildExpr, denseNormalizeFast, denseNrmMat, Nat.add_comm 1]

theorem denseNrmGo_mul (a b : DenseExpr p) (acc : List (VarId × ZMod p)) :
    denseNrmGo (.mul a b) acc = denseNrmMulU a b acc := by
  cases a <;> cases b <;> rw [denseNrmGo, denseNrmMulU] <;>
    simp [denseNrmChildExpr, denseNormalizeFast, denseNrmMat, denseNrmScale]

/-- The walk's contract: on an affine node, the linear form's constant, its term count and its
    terms consed onto `acc`; otherwise the node's normal form. -/
def denseNrmSpec (e : DenseExpr p) (acc : List (VarId × ZMod p)) : DenseNrm p :=
  match denseLinearize e with
  | some l => .lin l.const l.terms.length (l.terms ++ acc)
  | none => .opq e.normalize

/-- A child's normal form, read off its linear form — except for a bare variable, which normalizes
    to itself. -/
theorem denseNrmChildExpr_eq {b : DenseExpr p} {lb : DenseLinExpr p}
    (h : denseLinearize b = some lb) (acc : List (VarId × ZMod p)) :
    denseNrmChildExpr b lb.const lb.terms.length (lb.terms ++ acc) = b.normalize := by
  cases b with
  | var x => rfl
  | const n =>
      simp only [denseLinearize, Option.some.injEq] at h
      subst h
      simp [denseNrmChildExpr, denseNrmMat, DenseExpr.normalize]
  | add a b =>
      show denseNrmMat lb.const lb.terms.length (lb.terms ++ acc) = _
      rw [denseNrmMat_eq, DenseExpr.normalize, h]
  | mul a b =>
      show denseNrmMat lb.const lb.terms.length (lb.terms ++ acc) = _
      rw [denseNrmMat_eq, DenseExpr.normalize, h]

theorem denseNormalizeFast_of {e : DenseExpr p}
    (h : ∀ acc, denseNrmGo e acc = denseNrmSpec e acc) : denseNormalizeFast e = e.normalize := by
  cases e with
  | const n => rfl
  | var x => rfl
  | add a b =>
      show (denseNrmGo (.add a b) []).expr = _
      rw [h []]
      cases hl : denseLinearize (DenseExpr.add a b) with
      | none => simp [denseNrmSpec, hl, DenseNrm.expr, DenseExpr.normalize]
      | some l =>
          simp only [denseNrmSpec, hl, DenseNrm.expr, DenseExpr.normalize]
          rw [denseNrmMat_eq]
  | mul a b =>
      show (denseNrmGo (.mul a b) []).expr = _
      rw [h []]
      cases hl : denseLinearize (DenseExpr.mul a b) with
      | none => simp [denseNrmSpec, hl, DenseNrm.expr, DenseExpr.normalize]
      | some l =>
          simp only [denseNrmSpec, hl, DenseNrm.expr, DenseExpr.normalize]
          rw [denseNrmMat_eq]

theorem denseNrmGo_eq (e : DenseExpr p) : ∀ acc, denseNrmGo e acc = denseNrmSpec e acc := by
  induction e with
  | const n => intro acc; simp [denseNrmSpec, denseLinearize]
  | var x => intro acc; simp [denseNrmSpec, denseLinearize]
  | add a b iha ihb =>
      intro acc
      rw [denseNrmGo_add, denseNrmAddU, ihb acc]
      cases hlb : denseLinearize b with
      | none =>
          cases hla : denseLinearize a with
          | none =>
              simp only [denseNrmSpec, hlb, hla, denseNormalizeFast_of iha, denseLinearize,
                DenseExpr.normalize]
          | some la =>
              simp only [denseNrmSpec, hlb, hla, denseNormalizeFast_of iha, denseLinearize,
                DenseExpr.normalize]
      | some lb =>
          simp only [denseNrmSpec, hlb, iha (lb.terms ++ acc), denseNrmChildExpr_eq hlb]
          cases hla : denseLinearize a with
          | none => simp only [hla, denseLinearize, hlb, DenseExpr.normalize]
          | some la =>
              simp only [hla, denseLinearize, hlb, DenseLinExpr.add,
                List.length_append, List.append_assoc, zmodAdd_eq]
  | mul a b iha ihb =>
      intro acc
      rw [denseNrmGo_mul, denseNrmMulU, iha acc]
      cases hla : denseLinearize a with
      | none =>
          simp only [denseNrmSpec, hla, denseNormalizeFast_of ihb, denseLinearize,
            DenseExpr.normalize]
      | some la =>
          simp only [denseNrmSpec, hla]
          by_cases hta : la.terms = []
          · have hlen : la.terms.length = 0 := by rw [hta]; rfl
            have hceA : denseNrmChildExpr a la.const 0 (la.terms ++ acc) = a.normalize := by
              rw [← hlen]; exact denseNrmChildExpr_eq hla acc
            simp only [hlen, ihb (la.terms ++ acc)]
            cases hlb : denseLinearize b with
            | none =>
                simp only [denseNrmSpec, hlb, hceA, denseLinearize, hla, DenseExpr.normalize]
            | some lb =>
                simp only [denseNrmSpec, hlb, denseNrmScale_eq, denseLinearize, hla,
                  List.isEmpty_iff, hta, if_pos, DenseLinExpr.scale, List.length_map, zmodMul_eq]
                simp
          · obtain ⟨t, rest, hta'⟩ := List.exists_cons_of_ne_nil hta
            have hlen : la.terms.length = rest.length + 1 := by rw [hta']; simp
            have hceA : denseNrmChildExpr a la.const (rest.length + 1) (la.terms ++ acc)
                = a.normalize := by rw [← hlen]; exact denseNrmChildExpr_eq hla acc
            simp only [hlen, ihb []]
            cases hlb : denseLinearize b with
            | none =>
                simp only [denseNrmSpec, hlb, hceA, denseLinearize, hla, DenseExpr.normalize]
            | some lb =>
                by_cases htb : lb.terms = []
                · have hscA : denseNrmScale lb.const (rest.length + 1) (la.terms ++ acc)
                      = la.terms.map (fun t => (t.1, lb.const * t.2)) ++ acc := by
                    rw [← hlen]; exact denseNrmScale_eq lb.const la.terms acc
                  simp only [denseNrmSpec, hlb, htb, List.nil_append, List.length_nil, hscA,
                    denseLinearize, hla, List.isEmpty_iff, hta, if_neg, if_pos,
                    DenseLinExpr.scale, List.length_map, zmodMul_eq, mul_comm, hlen,
                    not_false_eq_true]
                · obtain ⟨t', rest', htb'⟩ := List.exists_cons_of_ne_nil htb
                  have hlenb : lb.terms.length = rest'.length + 1 := by rw [htb']; simp
                  have hceB : denseNrmChildExpr b lb.const (rest'.length + 1) (lb.terms ++ [])
                      = b.normalize := by rw [← hlenb]; exact denseNrmChildExpr_eq hlb []
                  simp only [denseNrmSpec, hlb, hlenb, hceA, hceB, denseLinearize, hla,
                    List.isEmpty_iff, hta, htb, if_neg, DenseExpr.normalize, not_false_eq_true]

theorem denseNormalizeFast_eq (e : DenseExpr p) : denseNormalizeFast e = e.normalize :=
  denseNormalizeFast_of (denseNrmGo_eq e)

@[csimp] theorem DenseExpr_normalize_eq_fast : @DenseExpr.normalize = @denseNormalizeFast := by
  funext q e
  exact (denseNormalizeFast_eq e).symm

/-! ## The dense normalization pass -/

/-- The dense affine-normalization pass (see `DenseExpr.normalize`). -/
def denseNormalizePass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => d.mapExpr DenseExpr.normalize)
    (fun _ _ _ => [])
    (fun _ _ _ _ hcov =>
      DenseConstraintSystem.mapExpr_covered DenseExpr.normalize_vars hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => by
      have hfe : ∀ (e : DenseExpr p) (denv : VarId → ZMod p),
          (DenseExpr.normalize e).eval denv = e.eval denv :=
        fun e denv => DenseExpr.normalize_eval e denv
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- soundness: `(mapExpr normalize).implies d`
        intro denv hsat
        refine ⟨denv, (DenseConstraintSystem.mapExpr_satisfies hfe d bs denv).mp hsat, ?_⟩
        rw [DenseConstraintSystem.mapExpr_sideEffects hfe]
      · -- invariants
        exact fun h => DenseConstraintSystem.mapExpr_guaranteesInvariants hfe h
      · -- no new powdr column
        exact fun i hi _ =>
          DenseConstraintSystem.mapExpr_occ_subset DenseExpr.normalize_vars d i hi
      · -- completeness (witness = input env; no derivations)
        intro denv hadm hsat
        refine ⟨denv, (DenseConstraintSystem.mapExpr_satisfies hfe d bs denv).mpr hsat,
          (DenseConstraintSystem.mapExpr_admissible hfe d bs denv).mpr hadm, ?_, fun _ _ => rfl, ?_⟩
        · rw [DenseConstraintSystem.mapExpr_sideEffects hfe]
        · intro _ _ i hi _
          exact ⟨DenseConstraintSystem.mapExpr_occ_subset DenseExpr.normalize_vars d i hi, rfl⟩)

end ApcOptimizer.Dense
