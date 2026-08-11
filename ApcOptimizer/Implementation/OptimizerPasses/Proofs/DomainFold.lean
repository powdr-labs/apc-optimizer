import ApcOptimizer.Implementation.OptimizerPasses.DomainFoldRuntime
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable

set_option autoImplicit false

/-! # Correctness for the dense `domainFold`

Proves `DensePassCorrect` for the fold of `DomainFoldRuntime.lean`. The fold is a pure rewrite: any
assignment satisfying either system pins the group to a survivor, under which the rewrite agrees
with the identity — so `env' = env` is the completeness witness and no derivations are produced.

`denseFindDomainAlg_sound` / `denseGroupDoms_sound` are the shared domain lemmas other passes use. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Domain soundness -/

theorem denseFindDomainAlg_sound [Fact p.Prime] (denv : VarId → ZMod p) :
    ∀ (all : List (DenseExpr p)) (i : VarId) (dm : List (ZMod p)),
      denseFindDomainAlg all i = some dm → (∀ c ∈ all, c.eval denv = 0) → denv i ∈ dm := by
  intro all
  induction all with
  | nil => intro i dm h _; simp [denseFindDomainAlg] at h
  | cons c rest ih =>
      intro i dm h hsat
      rw [denseFindDomainAlg] at h
      by_cases hm : c.mentions i = true
      · rw [if_pos hm] at h
        cases hr : denseRootsIn i c with
        | some d' =>
            rw [hr] at h; simp only [Option.some.injEq] at h; subst h
            exact denseRootsIn_sound i c d' hr denv (hsat c (List.mem_cons_self ..))
        | none =>
            rw [hr] at h
            exact ih i dm h (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc'))
      · rw [if_neg (by simpa using hm)] at h
        exact ih i dm h (fun c' hc' => hsat c' (List.mem_cons_of_mem _ hc'))

theorem denseGroupDoms_sound [Fact p.Prime] (denv : VarId → ZMod p) (es : List (DenseExpr p))
    (hsat : ∀ c ∈ es, c.eval denv = 0) :
    ∀ (xs : List VarId) (doms : List (VarId × List (ZMod p))),
      denseGroupDoms es xs = some doms → ∀ yd ∈ doms, denv yd.1 ∈ yd.2 := by
  intro xs
  induction xs with
  | nil =>
      intro doms h yd hyd
      simp only [denseGroupDoms, Option.some.injEq] at h; subst h; simp at hyd
  | cons i rest ih =>
      intro doms h yd hyd
      rw [denseGroupDoms] at h
      cases hd : denseFindDomainAlg es i with
      | none => rw [hd] at h; exact absurd h (by simp)
      | some dm =>
          cases hr : denseGroupDoms es rest with
          | none => rw [hd, hr] at h; exact absurd h (by simp)
          | some ds =>
              rw [hd, hr] at h; simp only [Option.some.injEq] at h; subst h
              rcases List.mem_cons.1 hyd with rfl | hmem
              · exact denseFindDomainAlg_sound denv es i dm hd hsat
              · exact ih ds hr yd hmem

/-! # Correctness for the index-keyed `domainFold` engine

The engine (`DomainFoldRuntime.lean`, `dfRun`) folds one target at a time: it re-checks each key's
domain against the current system, enumerates the surviving joint assignments, and rewrites the
touched items through one fused traversal. Correctness rests on two facts, both proven below for an
arbitrary assignment `denv` of the *current* system:

* the key values of `denv` are one of the enumerated survivors (`dfEnumGo_mem`), because every key's
  domain is entailed by a covered constraint and every filter is a covered constraint;
* a `uni` node of the traversal is constant on every survivor, hence equal at `denv`
  (`dfGo_ok`), so the rewrite preserves every evaluation.

Both are established from `DfCovered` — "every covered constraint vanishes" — which holds on either
side of the step, since the fold leaves covered constraints where they are. -/

/-! ## Dictionary-free primitives -/

theorem dfEqZ_eq (a b : ZMod p) : dfEqZ a b = decide (a = b) := by
  unfold dfEqZ
  cases p with
  | zero => simp [dfEqSlow]
  | succ n =>
      simp only [Nat.succ_ne_zero, if_false]
      by_cases h : a = b
      · simp [h]
      · simpa [h] using fun hv => h (ZMod.val_injective (n + 1) hv)

/-- A `uni` vector's entries all equal its constant. -/
theorem dfUni_sound (a : Array (ZMod p)) (c : ZMod p) (h : dfUni a = some c) :
    ∀ x ∈ a, x = c := by
  unfold dfUni at h
  split at h
  · split at h
    · rename_i hall
      obtain rfl : a[0] = c := Option.some.inj h
      intro x hx
      simpa [dfEqZ_eq] using (Array.all_eq_true_iff_forall_mem.1 hall) x hx
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The closure-free evaluator is `denseIExprEvalWithV` on the extended point. -/
theorem dfEvalCons_eq (v : ZMod p) (pt : List (ZMod p)) :
    ∀ ie : IExpr p, dfEvalCons (zmodZeroP p) v pt ie
      = denseIExprEvalWithV denseZModOps (v :: pt) ie := by
  intro ie
  induction ie with
  | const n => rfl
  | ix i => cases i <;> rfl
  | add a b iha ihb => show zmodAddP _ _ = denseZModOps.add _ _; rw [iha, ihb]; rfl
  | mul a b iha ihb => show zmodMulP _ _ = denseZModOps.mul _ _; rw [iha, ihb]; rfl

/-! ## Key slots -/

/-- A found slot names its key. -/
theorem dfSlotGo_spec (keys : Array VarId) (y : Nat) :
    ∀ (n j i : Nat), keys.size - j ≤ n → dfSlotGo keys y j = some i →
      ∃ h : i < keys.size, (keys[i]'h).index = y := by
  intro n
  induction n with
  | zero =>
      intro j i hn h
      rw [dfSlotGo, dif_neg (by omega)] at h
      exact absurd h (by simp)
  | succ n ih =>
      intro j i hn h
      rw [dfSlotGo] at h
      by_cases hj : j < keys.size
      · rw [dif_pos hj] at h
        by_cases hkey : (keys[j].index == y) = true
        · rw [if_pos hkey] at h
          obtain rfl : j = i := Option.some.inj h
          exact ⟨hj, eq_of_beq hkey⟩
        · rw [if_neg hkey] at h
          by_cases hlt : y < keys[j].index
          · rw [if_pos hlt] at h; exact absurd h (by simp)
          · rw [if_neg hlt] at h; exact ih (j + 1) i (by omega) h
      · rw [dif_neg hj] at h; exact absurd h (by simp)

/-- A found slot names its key (the form the proofs use). -/
theorem dfSlot_key (keys : Array VarId) (y : Nat) (i : Nat) (h : dfSlotGo keys y 0 = some i) :
    ∃ hi : i < keys.size, (keys[i]'hi).index = y :=
  dfSlotGo_spec keys y keys.size 0 i (by omega) h

/-- A found `denseVarIx` names a member. -/
theorem denseVarIx_mem (ks : List VarId) (y : VarId) :
    ∀ k : Nat, denseVarIx ks y = some k → y ∈ ks := by
  induction ks with
  | nil => intro k h; simp [denseVarIx] at h
  | cons x rest ih =>
      intro k h
      rw [denseVarIx] at h
      by_cases hx : (y == x) = true
      · exact List.mem_cons.2 (Or.inl (eq_of_beq hx))
      · rw [if_neg hx] at h
        cases hr : denseVarIx rest y with
        | none => rw [hr] at h; exact absurd h (by simp)
        | some k' => exact List.mem_cons_of_mem _ (ih k' hr)

/-- Compiling against a key list needs every variable to be in it. -/
theorem denseCompileE_vars (ks : List VarId) :
    ∀ (e : DenseExpr p) (ie : IExpr p), denseCompileE ks e = some ie → ∀ v ∈ e.vars, v ∈ ks := by
  intro e
  induction e with
  | const n => intro ie _ v hv; simp [DenseExpr.vars] at hv
  | var y =>
      intro ie h v hv
      simp only [DenseExpr.vars, List.mem_singleton] at hv
      subst hv
      rw [denseCompileE] at h
      cases hix : denseVarIx ks v with
      | none => rw [hix] at h; exact absurd h (by simp)
      | some k => exact denseVarIx_mem ks v k hix
  | add a b iha ihb =>
      intro ie h v hv
      rw [denseCompileE] at h
      cases hca : denseCompileE ks a with
      | none => rw [hca] at h; exact absurd h (by simp)
      | some ia =>
        cases hcb : denseCompileE ks b with
        | none => rw [hca, hcb] at h; exact absurd h (by simp)
        | some ib =>
            simp only [DenseExpr.vars, List.mem_append] at hv
            rcases hv with hv | hv
            · exact iha ia hca v hv
            · exact ihb ib hcb v hv
  | mul a b iha ihb =>
      intro ie h v hv
      rw [denseCompileE] at h
      cases hca : denseCompileE ks a with
      | none => rw [hca] at h; exact absurd h (by simp)
      | some ia =>
        cases hcb : denseCompileE ks b with
        | none => rw [hca, hcb] at h; exact absurd h (by simp)
        | some ib =>
            simp only [DenseExpr.vars, List.mem_append] at hv
            rcases hv with hv | hv
            · exact iha ia hca v hv
            · exact ihb ib hcb v hv


/-! ## The reversed key prefix

A partial point at level `j` is the values of the first `j` keys, newest first; the point a level-`j`
filter is checked on is therefore the values of `dfRKeys keys j`, which is the list that filter was
compiled against. -/

/-- The values of the keys below level `j`, newest first. -/
def dfPref (keys : Array VarId) (denv : VarId → ZMod p) : Nat → List (ZMod p)
  | 0 => []
  | j + 1 => denv (keys.getD j ⟨0⟩) :: dfPref keys denv j

theorem dfPref_eq_map (keys : Array VarId) (denv : VarId → ZMod p) :
    ∀ m : Nat, dfPref keys denv (m + 1) = (dfRKeys keys m).map denv := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [dfPref, dfRKeys, List.map_cons, ← ih]

/-- Position `k - 1 - j` of a level-`k` point is key `j`'s value. -/
theorem dfPref_lookup (keys : Array VarId) (denv : VarId → ZMod p) :
    ∀ (k j : Nat), j < k →
      denseLookupIxV (zmodZeroP p) (dfPref keys denv k) (k - 1 - j) = denv (keys.getD j ⟨0⟩) := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
      intro j hj
      rw [dfPref]
      by_cases hjk : j = k
      · rw [show k + 1 - 1 - j = 0 by omega, hjk]
        rfl
      · have hlt : j < k := by omega
        rw [show k + 1 - 1 - j = (k - 1 - j) + 1 by omega, denseLookupIxV]
        exact ih j hlt

/-! ## The survivor enumeration contains the real point -/

theorem dfExtOne_mono (zero : ZMod p) (ies : List (IExpr p)) (pt : List (ZMod p)) :
    ∀ (dom : List (ZMod p)) (out : Array (List (ZMod p))) (x : List (ZMod p)),
      x ∈ out → x ∈ dfExtOne zero ies pt dom out := by
  intro dom
  induction dom with
  | nil => intro out x hx; exact hx
  | cons v vs ih =>
      intro out x hx
      rw [dfExtOne]
      refine ih _ x ?_
      split
      · exact Array.mem_push.2 (Or.inl hx)
      · exact hx

theorem dfExtOne_mem (zero : ZMod p) (ies : List (IExpr p)) (pt : List (ZMod p)) (v : ZMod p)
    (hz : dfAllZero zero v pt ies = true) :
    ∀ (dom : List (ZMod p)) (out : Array (List (ZMod p))), v ∈ dom →
      (v :: pt) ∈ dfExtOne zero ies pt dom out := by
  intro dom
  induction dom with
  | nil => intro out hv; simp at hv
  | cons w ws ih =>
      intro out hv
      rw [dfExtOne]
      rcases List.mem_cons.1 hv with rfl | hmem
      · exact dfExtOne_mono zero ies pt ws _ _ (by rw [if_pos hz]; exact Array.mem_push_self)
      · exact ih _ hmem

theorem dfExtLevel_mono (zero : ZMod p) (ies : List (IExpr p)) (dom : List (ZMod p))
    (pts : Array (List (ZMod p))) :
    ∀ (n i : Nat) (out : Array (List (ZMod p))) (x : List (ZMod p)), pts.size - i ≤ n → x ∈ out →
      x ∈ dfExtLevel zero ies dom i pts out := by
  intro n
  induction n with
  | zero =>
      intro i out x hn hx
      rw [dfExtLevel, dif_neg (by omega)]
      exact hx
  | succ n ih =>
      intro i out x hn hx
      rw [dfExtLevel]
      by_cases hi : i < pts.size
      · rw [dif_pos hi]
        exact ih (i + 1) _ x (by omega) (dfExtOne_mono zero ies pts[i] dom out x hx)
      · rw [dif_neg hi]; exact hx

theorem dfExtLevel_mem (zero : ZMod p) (ies : List (IExpr p)) (dom : List (ZMod p))
    (pts : Array (List (ZMod p))) (i0 : Nat) (hi0 : i0 < pts.size) (v : ZMod p) (hv : v ∈ dom)
    (hz : dfAllZero zero v pts[i0] ies = true) :
    ∀ (n i : Nat) (out : Array (List (ZMod p))), pts.size - i ≤ n → i ≤ i0 →
      (v :: pts[i0]) ∈ dfExtLevel zero ies dom i pts out := by
  intro n
  induction n with
  | zero => intro i out hn hle; omega
  | succ n ih =>
      intro i out hn hle
      rw [dfExtLevel, dif_pos (by omega)]
      by_cases heq : i = i0
      · subst heq
        exact dfExtLevel_mono zero ies dom pts (n + 1) (i + 1) _ _ (by omega)
          (dfExtOne_mem zero ies pts[i] v hz dom out hv)
      · exact ih (i + 1) _ (by omega) (by omega)

/-- The real assignment's key values survive: each key's value is in its domain and every filter
    vanishes on it, so the level-by-level enumeration keeps its prefix at every level. -/
theorem dfEnumGo_mem (byLevel : Array (List (IExpr p))) (doms : Array (List (ZMod p))) (k : Nat)
    (keys : Array VarId) (denv : VarId → ZMod p)
    (hdom : ∀ j, j < k → denv (keys.getD j ⟨0⟩) ∈ doms.getD j [])
    (hfil : ∀ j, j < k →
      dfAllZero (zmodZeroP p) (denv (keys.getD j ⟨0⟩)) (dfPref keys denv j)
        (byLevel.getD j []) = true) :
    ∀ (n j : Nat) (pts : Array (List (ZMod p))), k - j ≤ n → j ≤ k → dfPref keys denv j ∈ pts →
      dfPref keys denv k ∈ dfEnumGo (zmodZeroP p) byLevel doms k j pts := by
  intro n
  induction n with
  | zero =>
      intro j pts hn hjk hmem
      obtain rfl : j = k := by omega
      rw [dfEnumGo]
      rw [if_neg (by
        intro he
        rw [Array.isEmpty_iff] at he
        rw [he] at hmem
        simp at hmem)]
      rw [dif_neg (by omega)]
      exact hmem
  | succ n ih =>
      intro j pts hn hjk hmem
      rw [dfEnumGo]
      rw [if_neg (by
        intro he
        rw [Array.isEmpty_iff] at he
        rw [he] at hmem
        simp at hmem)]
      by_cases hj : j < k
      · rw [dif_pos hj]
        obtain ⟨i0, hi0, hval⟩ := Array.mem_iff_getElem.1 hmem
        refine ih (j + 1) _ (by omega) (by omega) ?_
        show dfPref keys denv (j + 1) ∈ _
        rw [dfPref, ← hval]
        exact dfExtLevel_mem (zmodZeroP p) (byLevel.getD j []) (doms.getD j []) pts i0 hi0 _
          (hdom j hj) (by rw [hval]; exact hfil j hj) (pts.size) 0 #[] (by omega) (by omega)
      · rw [dif_neg hj]
        obtain rfl : j = k := by omega
        exact hmem


/-! ## The fused gate-and-rewrite traversal

`DfOk` is the invariant carried at one survivor index `t`: the node's value class describes its value
under `denv`, and its rewrite — when it has one — evaluates identically and introduces no variable.
A `uni` class is therefore "constant on every survivor", which is exactly what licenses the fold. -/

/-- One-field `VarId`s are equal when their indexes are. -/
theorem dfVarId_eq : ∀ (a b : VarId), a.index = b.index → a = b := by
  intro a b h
  cases a; cases b; simpa using h

/-- The traversal invariant at survivor index `t`. -/
def DfOk (denv : VarId → ZMod p) (t : Nat) (e : DenseExpr p) (r : DfRes p) : Prop :=
  (match r with
   | .uni c _ => e.eval denv = c
   | .vec a _ => a[t]? = some (e.eval denv)
   | _ => True) ∧
  ∀ e' : DenseExpr p, r.e? = some e' →
    e'.eval denv = e.eval denv ∧ ∀ i ∈ e'.vars, i ∈ e.vars

/-- A rebuilt node agrees with the original and introduces no variable. -/
theorem dfRebuild_ok (denv : VarId → ZMod p) (isAdd : Bool)
    (mk : DenseExpr p → DenseExpr p → DenseExpr p)
    (hev : ∀ x y : DenseExpr p, (mk x y).eval denv = dfOp isAdd (x.eval denv) (y.eval denv))
    (hvars : ∀ x y : DenseExpr p, (mk x y).vars = x.vars ++ y.vars)
    (hmk : ∀ x y : DenseExpr p, (if isAdd then DenseExpr.add x y else DenseExpr.mul x y) = mk x y)
    (a b : DenseExpr p) (ea eb : Option (DenseExpr p))
    (hA : ∀ e' : DenseExpr p, ea = some e' → e'.eval denv = a.eval denv ∧ ∀ i ∈ e'.vars, i ∈ a.vars)
    (hB : ∀ e' : DenseExpr p, eb = some e' → e'.eval denv = b.eval denv ∧ ∀ i ∈ e'.vars, i ∈ b.vars) :
    ∀ e' : DenseExpr p, dfRebuild isAdd a b ea eb = some e' →
      e'.eval denv = (mk a b).eval denv ∧ ∀ i ∈ e'.vars, i ∈ (mk a b).vars := by
  intro e' he'
  have hagA : (ea.getD a).eval denv = a.eval denv ∧ ∀ i ∈ (ea.getD a).vars, i ∈ a.vars := by
    cases ea with
    | none => exact ⟨rfl, fun i hi => hi⟩
    | some x => exact hA x rfl
  have hagB : (eb.getD b).eval denv = b.eval denv ∧ ∀ i ∈ (eb.getD b).vars, i ∈ b.vars := by
    cases eb with
    | none => exact ⟨rfl, fun i hi => hi⟩
    | some x => exact hB x rfl
  have hval : e' = mk (ea.getD a) (eb.getD b) := by
    unfold dfRebuild at he'
    cases ea with
    | none =>
        cases eb with
        | none => exact absurd he' (by simp)
        | some y => rw [← hmk]; exact (Option.some.inj he').symm
    | some x => rw [← hmk]; exact (Option.some.inj he').symm
  subst hval
  refine ⟨?_, ?_⟩
  · rw [hev, hev, hagA.1, hagB.1]
  · intro i hi
    rw [hvars] at hi ⊢
    rcases List.mem_append.1 hi with hi | hi
    · exact List.mem_append_left _ (hagA.2 i hi)
    · exact List.mem_append_right _ (hagB.2 i hi)

/-- Combining an operation node's children preserves the invariant; a `uni` result folds the node. -/
theorem dfComb_ok (denv : VarId → ZMod p) (t : Nat) (isAdd : Bool)
    (mk : DenseExpr p → DenseExpr p → DenseExpr p)
    (hev : ∀ x y : DenseExpr p, (mk x y).eval denv = dfOp isAdd (x.eval denv) (y.eval denv))
    (hvars : ∀ x y : DenseExpr p, (mk x y).vars = x.vars ++ y.vars)
    (hmk : ∀ x y : DenseExpr p, (if isAdd then DenseExpr.add x y else DenseExpr.mul x y) = mk x y)
    (a b : DenseExpr p) (ra rb : DfRes p) (hA : DfOk denv t a ra) (hB : DfOk denv t b rb) :
    DfOk denv t (mk a b) (dfComb isAdd a b ra rb) := by
  -- the folded-constant result, shared by the four in-group shapes
  have huni : ∀ c : ZMod p, (mk a b).eval denv = c → DfOk denv t (mk a b) (.uni c true) := by
    intro c hc
    refine ⟨hc, ?_⟩
    intro e' he'
    have hde : (DfRes.uni c true).e? = some (DenseExpr.const c) := by simp [DfRes.e?]
    rw [hde] at he'
    obtain rfl : DenseExpr.const c = e' := Option.some.inj he'
    exact ⟨hc.symm, fun i hi => by simp [DenseExpr.vars] at hi⟩
  -- the out result, shared by every shape with a non-key variable
  have hout : ∀ ea eb : Option (DenseExpr p),
      (∀ e' : DenseExpr p, ea = some e' →
        e'.eval denv = a.eval denv ∧ ∀ i ∈ e'.vars, i ∈ a.vars) →
      (∀ e' : DenseExpr p, eb = some e' →
        e'.eval denv = b.eval denv ∧ ∀ i ∈ e'.vars, i ∈ b.vars) →
      DfOk denv t (mk a b)
        (match dfRebuild isAdd a b ea eb with | none => .out | some e => .outCh e) := by
    intro ea eb hA' hB'
    have hrb := dfRebuild_ok denv isAdd mk hev hvars hmk a b ea eb hA' hB'
    cases hd : dfRebuild isAdd a b ea eb with
    | none => exact ⟨trivial, fun e' he' => by simp [DfRes.e?] at he'⟩
    | some e0 =>
        refine ⟨trivial, ?_⟩
        intro e' he'
        have hde : (DfRes.outCh e0).e? = some e0 := rfl
        rw [hde] at he'
        obtain rfl : e0 = e' := Option.some.inj he'
        exact hrb _ hd
  -- the vector shapes: the combined vector's `t`-th entry is the node's value
  have hvec : ∀ (s : Array (ZMod p)) (ea eb : Option (DenseExpr p)),
      s[t]? = some ((mk a b).eval denv) →
      (∀ e' : DenseExpr p, ea = some e' →
        e'.eval denv = a.eval denv ∧ ∀ i ∈ e'.vars, i ∈ a.vars) →
      (∀ e' : DenseExpr p, eb = some e' →
        e'.eval denv = b.eval denv ∧ ∀ i ∈ e'.vars, i ∈ b.vars) →
      DfOk denv t (mk a b)
        (match dfUni s with
         | some c => .uni c true
         | none => .vec s (dfRebuild isAdd a b ea eb)) := by
    intro s ea eb hs hA' hB'
    have hrb := dfRebuild_ok denv isAdd mk hev hvars hmk a b ea eb hA' hB'
    cases hu : dfUni s with
    | some c =>
        exact huni c (dfUni_sound s c hu _ (Array.mem_iff_getElem?.2 ⟨t, hs⟩))
    | none => exact ⟨hs, hrb⟩
  unfold dfComb
  cases ra with
  | out => cases rb <;> exact hout _ _ hA.2 hB.2
  | outCh ea => cases rb <;> exact hout _ _ hA.2 hB.2
  | uni x fa =>
      cases rb with
      | out => exact hout _ _ hA.2 hB.2
      | outCh eb => exact hout _ _ hA.2 hB.2
      | uni y fb =>
          have hx : a.eval denv = x := hA.1
          have hy : b.eval denv = y := hB.1
          exact huni _ (by rw [hev, hx, hy])
      | vec vb eb =>
          have hx : a.eval denv = x := hA.1
          have hy : vb[t]? = some (b.eval denv) := hB.1
          exact hvec _ _ _ (by rw [Array.getElem?_map, hy, hev, hx]; try rfl) hA.2 hB.2
  | vec va ea =>
      cases rb with
      | out => exact hout _ _ hA.2 hB.2
      | outCh eb => exact hout _ _ hA.2 hB.2
      | uni y fb =>
          have hx : va[t]? = some (a.eval denv) := hA.1
          have hy : b.eval denv = y := hB.1
          exact hvec _ _ _ (by rw [Array.getElem?_map, hx, hev, hy]; try rfl) hA.2 hB.2
      | vec vb eb =>
          have hx : va[t]? = some (a.eval denv) := hA.1
          have hy : vb[t]? = some (b.eval denv) := hB.1
          exact hvec _ _ _ (by rw [Array.getElem?_zipWith, hx, hy, hev]; try rfl) hA.2 hB.2

/-- The traversal is sound at every survivor index, given the key columns are. -/
theorem dfGo_ok (ctx : DfCtx p) (denv : VarId → ZMod p) (t : Nat)
    (hcol : ∀ (j : Nat) (hj : j < ctx.keys.size),
      DfOk denv t (.var (ctx.keys[j]'hj)) (ctx.colRes.getD j .out)) :
    ∀ e : DenseExpr p, DfOk denv t e (dfGo ctx e) := by
  intro e
  induction e with
  | const c => exact ⟨rfl, fun e' he' => by simp [dfGo, DfRes.e?] at he'⟩
  | var y =>
      rw [dfGo]
      cases hslot : dfSlotGo ctx.keys y.index 0 with
      | none => exact ⟨trivial, fun e' he' => by simp [DfRes.e?] at he'⟩
      | some j =>
          obtain ⟨hj, hkey⟩ := dfSlot_key ctx.keys y.index j hslot
          have : (ctx.keys[j]'hj) = y := dfVarId_eq _ _ hkey
          rw [← this]
          exact hcol j hj
  | add a b iha ihb =>
      exact dfComb_ok denv t true DenseExpr.add
        (fun x y => by show x.eval denv + y.eval denv = zmodAddP _ _; rw [zmodAddP_eq])
        (fun _ _ => rfl) (fun _ _ => rfl) a b _ _ iha ihb
  | mul a b iha ihb =>
      exact dfComb_ok denv t false DenseExpr.mul
        (fun x y => by show x.eval denv * y.eval denv = zmodMulP _ _; rw [zmodMulP_eq])
        (fun _ _ => rfl) (fun _ _ => rfl) a b _ _ iha ihb

/-! ## Item-level agreement -/

theorem dfRewrite_ok (ctx : DfCtx p) (denv : VarId → ZMod p) (t : Nat)
    (hcol : ∀ (j : Nat) (hj : j < ctx.keys.size),
      DfOk denv t (.var (ctx.keys[j]'hj)) (ctx.colRes.getD j .out))
    (e e' : DenseExpr p) (h : dfRewrite ctx e = some e') :
    e'.eval denv = e.eval denv ∧ ∀ i ∈ e'.vars, i ∈ e.vars :=
  (dfGo_ok ctx denv t hcol e).2 e' h

theorem dfRewriteList_ok (ctx : DfCtx p) (denv : VarId → ZMod p) (t : Nat)
    (hcol : ∀ (j : Nat) (hj : j < ctx.keys.size),
      DfOk denv t (.var (ctx.keys[j]'hj)) (ctx.colRes.getD j .out)) :
    ∀ (es es' : List (DenseExpr p)), dfRewriteList ctx es = some es' →
      es'.map (fun e => e.eval denv) = es.map (fun e => e.eval denv) ∧
      ∀ (i : VarId), (∃ e' ∈ es', i ∈ e'.vars) → ∃ e ∈ es, i ∈ e.vars := by
  intro es
  induction es with
  | nil => intro es' h; simp [dfRewriteList] at h
  | cons e rest ih =>
      intro es' h
      rw [dfRewriteList] at h
      cases hr : dfRewrite ctx e with
      | none =>
          cases hrs : dfRewriteList ctx rest with
          | none => rw [hr, hrs] at h; exact absurd h (by simp)
          | some rest' =>
              rw [hr, hrs] at h
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨hmap, hvars⟩ := ih rest' hrs
              refine ⟨by simp only [List.map_cons, Option.getD_none, Option.getD_some, hmap], ?_⟩
              intro i hi
              obtain ⟨e', he', hie⟩ := hi
              rcases List.mem_cons.1 he' with rfl | hmem
              · exact ⟨e', List.mem_cons_self .., hie⟩
              · obtain ⟨e0, he0, hie0⟩ := hvars i ⟨e', hmem, hie⟩
                exact ⟨e0, List.mem_cons_of_mem _ he0, hie0⟩
      | some e' =>
          obtain ⟨hev, hvr⟩ := dfRewrite_ok ctx denv t hcol e e' hr
          cases hrs : dfRewriteList ctx rest with
          | none =>
              rw [hr, hrs] at h
              simp only [Option.some.injEq] at h
              subst h
              refine ⟨by simp only [List.map_cons, Option.getD_none, Option.getD_some, hev], ?_⟩
              intro i hi
              obtain ⟨e0, he0, hie⟩ := hi
              rcases List.mem_cons.1 he0 with rfl | hmem
              · exact ⟨e, List.mem_cons_self .., hvr i hie⟩
              · exact ⟨e0, List.mem_cons_of_mem _ hmem, hie⟩
          | some rest' =>
              rw [hr, hrs] at h
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨hmap, hvars⟩ := ih rest' hrs
              refine ⟨by simp only [List.map_cons, Option.getD_some, hev, hmap], ?_⟩
              intro i hi
              obtain ⟨e0, he0, hie⟩ := hi
              rcases List.mem_cons.1 he0 with rfl | hmem
              · exact ⟨e, List.mem_cons_self .., hvr i hie⟩
              · obtain ⟨e1, he1, hie1⟩ := hvars i ⟨e0, hmem, hie⟩
                exact ⟨e1, List.mem_cons_of_mem _ he1, hie1⟩

theorem dfRewriteBi_ok (ctx : DfCtx p) (denv : VarId → ZMod p) (t : Nat)
    (hcol : ∀ (j : Nat) (hj : j < ctx.keys.size),
      DfOk denv t (.var (ctx.keys[j]'hj)) (ctx.colRes.getD j .out))
    (bi bi' : BusInteraction (DenseExpr p)) (h : dfRewriteBi ctx bi = some bi') :
    denseBIEval bi' denv = denseBIEval bi denv ∧
      ∀ i ∈ denseBIVars bi', i ∈ denseBIVars bi := by
  rw [dfRewriteBi] at h
  have hmul : ∀ m', dfRewrite ctx bi.multiplicity = some m' →
      m'.eval denv = bi.multiplicity.eval denv ∧ ∀ i ∈ m'.vars, i ∈ bi.multiplicity.vars :=
    fun m' hm => dfRewrite_ok ctx denv t hcol _ m' hm
  have hpl : ∀ pl', dfRewriteList ctx bi.payload = some pl' →
      pl'.map (fun e => e.eval denv) = bi.payload.map (fun e => e.eval denv) ∧
      ∀ (i : VarId), (∃ e' ∈ pl', i ∈ e'.vars) → ∃ e ∈ bi.payload, i ∈ e.vars :=
    fun pl' hp => dfRewriteList_ok ctx denv t hcol bi.payload pl' hp
  have hshape : bi' = { bi with
      multiplicity := (dfRewrite ctx bi.multiplicity).getD bi.multiplicity,
      payload := (dfRewriteList ctx bi.payload).getD bi.payload } := by
    cases hm : dfRewrite ctx bi.multiplicity with
    | none =>
        cases hp : dfRewriteList ctx bi.payload with
        | none => rw [hm, hp] at h; exact absurd h (by simp)
        | some pl' => rw [hm, hp] at h; exact (Option.some.inj h).symm
    | some m' => rw [hm] at h; exact (Option.some.inj h).symm
  have hmulEq : ((dfRewrite ctx bi.multiplicity).getD bi.multiplicity).eval denv
      = bi.multiplicity.eval denv := by
    cases hm : dfRewrite ctx bi.multiplicity with
    | none => rfl
    | some m' => exact (hmul m' hm).1
  have hplEq : ((dfRewriteList ctx bi.payload).getD bi.payload).map (fun e => e.eval denv)
      = bi.payload.map (fun e => e.eval denv) := by
    cases hp : dfRewriteList ctx bi.payload with
    | none => rfl
    | some pl' => exact (hpl pl' hp).1
  subst hshape
  refine ⟨?_, ?_⟩
  · unfold denseBIEval
    simp only [hmulEq, hplEq]
  · intro i hi
    rw [denseBIVars, List.mem_append] at hi ⊢
    rcases hi with hi | hi
    · refine Or.inl ?_
      cases hm : dfRewrite ctx bi.multiplicity with
      | none => rw [hm] at hi; exact hi
      | some m' => rw [hm] at hi; exact (hmul m' hm).2 i hi
    · rw [List.mem_flatMap] at hi
      obtain ⟨e', he', hie⟩ := hi
      cases hp : dfRewriteList ctx bi.payload with
      | none =>
          rw [hp] at he'
          exact Or.inr (List.mem_flatMap.2 ⟨e', he', hie⟩)
      | some pl' =>
          rw [hp] at he'
          obtain ⟨e0, he0, hie0⟩ := (hpl pl' hp).2 i ⟨e', he', hie⟩
          exact Or.inr (List.mem_flatMap.2 ⟨e0, he0, hie0⟩)


/-! ## Applying a step's changes, position by position -/

theorem dfApplyCs_size : ∀ (ch : List (Nat × DenseExpr p)) (cs : Array (DenseExpr p)),
    (dfApplyCs cs ch).size = cs.size := by
  intro ch
  induction ch with
  | nil => intro cs; rfl
  | cons qe rest ih => intro cs; rw [dfApplyCs, ih]; simp

/-- Each position of the folded array is either untouched or one of the listed changes. -/
theorem dfApplyCs_getElem? : ∀ (ch : List (Nat × DenseExpr p)) (cs : Array (DenseExpr p)) (q : Nat),
    (dfApplyCs cs ch)[q]? = cs[q]? ∨
      ∃ e : DenseExpr p, (q, e) ∈ ch ∧ (dfApplyCs cs ch)[q]? = some e := by
  intro ch
  induction ch with
  | nil => intro cs q; exact Or.inl rfl
  | cons qe rest ih =>
      intro cs q
      obtain ⟨q0, e0⟩ := qe
      rw [dfApplyCs]
      rcases ih (cs.setIfInBounds q0 e0) q with h | ⟨e, hmem, he⟩
      · by_cases hq : q0 = q
        · subst hq
          by_cases hlt : q0 < cs.size
          · exact Or.inr ⟨e0, List.mem_cons_self .., by
              rw [h, Array.getElem?_setIfInBounds, if_pos rfl, if_pos hlt]⟩
          · refine Or.inl ?_
            rw [h, Array.getElem?_setIfInBounds, if_pos rfl, if_neg hlt]
            exact (Array.getElem?_eq_none_iff.2 (by omega)).symm
        · refine Or.inl ?_
          rw [h, Array.getElem?_setIfInBounds, if_neg hq]
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ hmem, he⟩

/-- Setting positions to values with the same `f`-image leaves the mapped list alone. Stated against
    the *original* array, so a position listed twice is no obstacle. -/
theorem dfApplyBis_map {β : Type} (f : BusInteraction (DenseExpr p) → β)
    (bis0 : Array (BusInteraction (DenseExpr p))) :
    ∀ (ch : List (Nat × BusInteraction (DenseExpr p))) (bis : Array (BusInteraction (DenseExpr p))),
      bis.size = bis0.size →
      (∀ (q : Nat) (bi bi0 : BusInteraction (DenseExpr p)),
        bis[q]? = some bi → bis0[q]? = some bi0 → f bi = f bi0) →
      (∀ qb ∈ ch, ∀ bi0, bis0[qb.1]? = some bi0 → f qb.2 = f bi0) →
      (dfApplyBis bis ch).toList.map f = bis0.toList.map f := by
  intro ch
  induction ch with
  | nil =>
      intro bis hsize hinv _
      rw [dfApplyBis]
      refine List.ext_getElem? (fun i => ?_)
      rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
      cases hb : bis[i]? with
      | none =>
          have hn : bis0[i]? = none := by
            rw [Array.getElem?_eq_none_iff]
            rw [Array.getElem?_eq_none_iff] at hb
            omega
          rw [hn]
      | some bi =>
          have hlt : i < bis0.size := by
            obtain ⟨h1, _⟩ := Array.getElem?_eq_some_iff.1 hb
            omega
          rw [Array.getElem?_eq_getElem hlt, Option.map_some, Option.map_some,
            hinv i bi _ hb (Array.getElem?_eq_getElem hlt)]
  | cons qb rest ih =>
      intro bis hsize hinv hall
      obtain ⟨q0, b0⟩ := qb
      have hq0 : ∀ bi0, bis0[q0]? = some bi0 → f b0 = f bi0 := hall (q0, b0) (List.mem_cons_self ..)
      rw [dfApplyBis]
      refine ih (bis.setIfInBounds q0 b0) (by simp [hsize]) ?_
        (fun qb' hqb' => hall qb' (List.mem_cons_of_mem _ hqb'))
      intro q bi bi0 hbi hbi0
      rw [Array.getElem?_setIfInBounds] at hbi
      by_cases hq : q0 = q
      · rw [if_pos hq] at hbi
        by_cases hlt : q0 < bis.size
        · rw [if_pos hlt] at hbi
          obtain hb : b0 = bi := Option.some.inj hbi
          rw [← hb, hq0 bi0 (by rw [hq]; exact hbi0)]
        · rw [if_neg hlt] at hbi; exact absurd hbi (by simp)
      · rw [if_neg hq] at hbi
        exact hinv q bi bi0 hbi hbi0

/-- Same, for the variable sets: a rewritten interaction introduces no variable. -/
theorem dfApplyBis_vars (bis0 : Array (BusInteraction (DenseExpr p))) :
    ∀ (ch : List (Nat × BusInteraction (DenseExpr p))) (bis : Array (BusInteraction (DenseExpr p))),
      bis.size = bis0.size →
      (∀ (q : Nat) (bi bi0 : BusInteraction (DenseExpr p)),
        bis[q]? = some bi → bis0[q]? = some bi0 → ∀ i ∈ denseBIVars bi, i ∈ denseBIVars bi0) →
      (∀ qb ∈ ch, ∀ bi0, bis0[qb.1]? = some bi0 →
        ∀ i ∈ denseBIVars qb.2, i ∈ denseBIVars bi0) →
      ∀ (q : Nat) (bi' : BusInteraction (DenseExpr p)), (dfApplyBis bis ch)[q]? = some bi' →
        ∃ bi0, bis0[q]? = some bi0 ∧ ∀ i ∈ denseBIVars bi', i ∈ denseBIVars bi0 := by
  intro ch
  induction ch with
  | nil =>
      intro bis hsize hinv _ q bi' hbi'
      rw [dfApplyBis] at hbi'
      have hlt : q < bis0.size := by
        obtain ⟨h1, _⟩ := Array.getElem?_eq_some_iff.1 hbi'
        omega
      exact ⟨bis0[q], Array.getElem?_eq_getElem hlt,
        hinv q bi' _ hbi' (Array.getElem?_eq_getElem hlt)⟩
  | cons qb rest ih =>
      intro bis hsize hinv hall
      obtain ⟨q0, b0⟩ := qb
      have hq0 : ∀ bi0, bis0[q0]? = some bi0 → ∀ i ∈ denseBIVars b0, i ∈ denseBIVars bi0 :=
        hall (q0, b0) (List.mem_cons_self ..)
      rw [dfApplyBis]
      refine ih (bis.setIfInBounds q0 b0) (by simp [hsize]) ?_
        (fun qb' hqb' => hall qb' (List.mem_cons_of_mem _ hqb'))
      intro q bi bi0 hbi hbi0
      rw [Array.getElem?_setIfInBounds] at hbi
      by_cases hq : q0 = q
      · rw [if_pos hq] at hbi
        by_cases hlt : q0 < bis.size
        · rw [if_pos hlt] at hbi
          obtain hb : b0 = bi := Option.some.inj hbi
          rw [← hb]
          exact hq0 bi0 (by rw [hq]; exact hbi0)
        · rw [if_neg hlt] at hbi; exact absurd hbi (by simp)
      · rw [if_neg hq] at hbi
        exact hinv q bi bi0 hbi hbi0


/-! ## A positional rewrite is a `DensePassCorrect` step

The step rewrites items *by position*, so the output is not a `map` of the input and
`DensePassCorrect.ofEvalAgree` does not apply. What does hold — and is all four obligations need — is
that the two lists have the same length and agree position by position: on the constraint side up to
evaluation under an anchor `A`, on the bus side up to the evaluated message. -/

/-- Side effects read the interactions only through their evaluated messages. -/
theorem dfSideEffects_map (bs : BusSemantics p) (denv : VarId → ZMod p) :
    ∀ l : List (BusInteraction (DenseExpr p)),
      (l.filter (fun bi => bs.isStateful bi.busId)).map
          (fun bi => let m := denseBIEval bi denv; ((m.busId, m.payload), m.multiplicity))
        = ((l.map (fun bi => denseBIEval bi denv)).filter (fun m => bs.isStateful m.busId)).map
          (fun m => ((m.busId, m.payload), m.multiplicity)) := by
  intro l
  induction l with
  | nil => rfl
  | cons bi rest ih =>
      rw [List.filter_cons, List.map_cons, List.filter_cons]
      have hid : (denseBIEval bi denv).busId = bi.busId := rfl
      by_cases hb : bs.isStateful bi.busId = true
      · rw [if_pos hb, if_pos (by rw [hid]; exact hb), List.map_cons, List.map_cons, ih]
      · rw [if_neg hb, if_neg (by rw [hid]; exact hb), ih]

/-- Constraint lists of equal length whose entries evaluate alike vanish together. -/
theorem dfCsZero_iff (cs cs' : Array (DenseExpr p)) (denv : VarId → ZMod p)
    (hsize : cs'.size = cs.size)
    (hev : ∀ (q : Nat) (c c' : DenseExpr p), cs[q]? = some c → cs'[q]? = some c' →
      c'.eval denv = c.eval denv) :
    (∀ c ∈ cs.toList, c.eval denv = 0) ↔ (∀ c' ∈ cs'.toList, c'.eval denv = 0) := by
  constructor
  · intro hall c' hc'
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hc'
    rw [Array.getElem?_toList] at hq
    have hlt : q < cs.size := by
      obtain ⟨h1, _⟩ := Array.getElem?_eq_some_iff.1 hq
      omega
    rw [hev q cs[q] c' (Array.getElem?_eq_getElem hlt) hq]
    exact hall cs[q] (List.mem_iff_getElem?.2 ⟨q, by
      rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hlt⟩)
  · intro hall c hc
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hc
    rw [Array.getElem?_toList] at hq
    have hlt : q < cs'.size := by
      obtain ⟨h1, _⟩ := Array.getElem?_eq_some_iff.1 hq
      omega
    rw [← hev q c cs'[q] hq (Array.getElem?_eq_getElem hlt)]
    exact hall cs'[q] (List.mem_iff_getElem?.2 ⟨q, by
      rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hlt⟩)

/-- The step's `DensePassCorrect`, from position-wise agreement. -/
theorem dfStep_general (bs : BusSemantics p) (isInput : VarId → Bool)
    (cs : Array (DenseExpr p)) (bis : Array (BusInteraction (DenseExpr p)))
    (chCs : List (Nat × DenseExpr p)) (chBis : List (Nat × BusInteraction (DenseExpr p)))
    (A : (VarId → ZMod p) → Prop)
    (hAout : ∀ denv, (∀ c ∈ (dfApplyCs cs chCs).toList, c.eval denv = 0) → A denv)
    (hAin : ∀ denv, (∀ c ∈ cs.toList, c.eval denv = 0) → A denv)
    (hcs : ∀ denv, A denv → ∀ (q : Nat) (e : DenseExpr p), (q, e) ∈ chCs →
      ∀ c : DenseExpr p, cs[q]? = some c → e.eval denv = c.eval denv)
    (hcsV : ∀ (q : Nat) (e : DenseExpr p), (q, e) ∈ chCs →
      ∀ c : DenseExpr p, cs[q]? = some c → ∀ i ∈ e.vars, i ∈ c.vars)
    (hbis : ∀ denv, A denv → ∀ (q : Nat) (b : BusInteraction (DenseExpr p)), (q, b) ∈ chBis →
      ∀ bi, bis[q]? = some bi → denseBIEval b denv = denseBIEval bi denv)
    (hbisV : ∀ (q : Nat) (b : BusInteraction (DenseExpr p)), (q, b) ∈ chBis →
      ∀ bi, bis[q]? = some bi → ∀ i ∈ denseBIVars b, i ∈ denseBIVars bi) :
    DensePassCorrect isInput ⟨cs.toList, bis.toList⟩
      ⟨(dfApplyCs cs chCs).toList, (dfApplyBis bis chBis).toList⟩ [] bs := by
  set out : DenseConstraintSystem p :=
    ⟨(dfApplyCs cs chCs).toList, (dfApplyBis bis chBis).toList⟩ with hout
  set inp : DenseConstraintSystem p := ⟨cs.toList, bis.toList⟩ with hinp
  -- constraint side: positions agree under `A`
  have hcsEv : ∀ denv, A denv → ∀ (q : Nat) (c c' : DenseExpr p), cs[q]? = some c →
      (dfApplyCs cs chCs)[q]? = some c' → c'.eval denv = c.eval denv := by
    intro denv hA q c c' hc hc'
    rcases dfApplyCs_getElem? chCs cs q with h | ⟨e, hmem, he⟩
    · rw [h, hc] at hc'
      rw [Option.some.inj hc']
    · rw [he] at hc'
      obtain he2 : e = c' := Option.some.inj hc'
      rw [← he2]
      exact hcs denv hA q e hmem c hc
  have hcsVars : ∀ (q : Nat) (c c' : DenseExpr p), cs[q]? = some c →
      (dfApplyCs cs chCs)[q]? = some c' → ∀ i ∈ c'.vars, i ∈ c.vars := by
    intro q c c' hc hc'
    rcases dfApplyCs_getElem? chCs cs q with h | ⟨e, hmem, he⟩
    · rw [h, hc] at hc'
      rw [Option.some.inj hc']
      exact fun i hi => hi
    · rw [he] at hc'
      obtain he2 : e = c' := Option.some.inj hc'
      rw [← he2]
      exact hcsV q e hmem c hc
  have hsatCs : ∀ denv, A denv →
      ((∀ c ∈ cs.toList, c.eval denv = 0) ↔ (∀ c' ∈ (dfApplyCs cs chCs).toList, c'.eval denv = 0)) :=
    fun denv hA => dfCsZero_iff cs (dfApplyCs cs chCs) denv (dfApplyCs_size chCs cs)
      (hcsEv denv hA)
  -- bus side: the evaluated messages agree under `A`, and no variable is introduced
  have hbisMap : ∀ denv, A denv →
      (dfApplyBis bis chBis).toList.map (fun bi => denseBIEval bi denv)
        = bis.toList.map (fun bi => denseBIEval bi denv) := by
    intro denv hA
    refine dfApplyBis_map (fun bi => denseBIEval bi denv) bis chBis bis rfl ?_ ?_
    · intro q bi bi0 h1 h2
      rw [h1] at h2
      rw [Option.some.inj h2]
    · intro qb hqb bi0 hbi0
      exact hbis denv hA qb.1 qb.2 hqb bi0 hbi0
  have hbisVars : ∀ (q : Nat) (bi' : BusInteraction (DenseExpr p)),
      (dfApplyBis bis chBis)[q]? = some bi' →
      ∃ bi, bis[q]? = some bi ∧ ∀ i ∈ denseBIVars bi', i ∈ denseBIVars bi := by
    refine dfApplyBis_vars bis chBis bis rfl ?_ ?_
    · intro q bi bi0 h1 h2
      rw [h1] at h2
      rw [Option.some.inj h2]
      exact fun i hi => hi
    · intro qb hqb bi0 hbi0
      exact hbisV qb.1 qb.2 hqb bi0 hbi0
  have hsatBis : ∀ denv, A denv → ((∀ bi ∈ bis.toList, (denseBIEval bi denv).multiplicity ≠ 0 →
        bs.accepts (denseBIEval bi denv)) ↔
      (∀ bi' ∈ (dfApplyBis bis chBis).toList, (denseBIEval bi' denv).multiplicity ≠ 0 →
        bs.accepts (denseBIEval bi' denv))) := by
    intro denv hA
    have hmap := hbisMap denv hA
    constructor
    · intro hall bi' hbi'
      have : denseBIEval bi' denv ∈ bis.toList.map (fun bi => denseBIEval bi denv) := by
        rw [← hmap]; exact List.mem_map.2 ⟨bi', hbi', rfl⟩
      obtain ⟨bi, hbi, heq⟩ := List.mem_map.1 this
      rw [← heq]; exact hall bi hbi
    · intro hall bi hbi
      have : denseBIEval bi denv
          ∈ (dfApplyBis bis chBis).toList.map (fun bi => denseBIEval bi denv) := by
        rw [hmap]; exact List.mem_map.2 ⟨bi, hbi, rfl⟩
      obtain ⟨bi', hbi', heq⟩ := List.mem_map.1 this
      rw [← heq]; exact hall bi' hbi'
  have hsatIff : ∀ denv, A denv → (out.satisfies bs denv ↔ inp.satisfies bs denv) := by
    intro denv hA
    constructor
    · rintro ⟨hc, hb⟩
      exact ⟨(hsatCs denv hA).2 hc, fun bi hbi => (hsatBis denv hA).2 hb bi hbi⟩
    · rintro ⟨hc, hb⟩
      exact ⟨(hsatCs denv hA).1 hc, fun bi' hbi' => (hsatBis denv hA).1 hb bi' hbi'⟩
  have hside : ∀ denv, A denv → out.sideEffects bs denv = inp.sideEffects bs denv := by
    intro denv hA
    unfold DenseConstraintSystem.sideEffects
    refine funext (fun message => congrArg (multiplicitySum message) ?_)
    show (((dfApplyBis bis chBis).toList.filter (fun bi => bs.isStateful bi.busId)).map _) = _
    rw [dfSideEffects_map bs denv, dfSideEffects_map bs denv, hbisMap denv hA]
  have hadm : ∀ denv, A denv → (out.admissible bs denv ↔ inp.admissible bs denv) := by
    intro denv hA
    unfold DenseConstraintSystem.admissible
    show bs.admissible (((dfApplyBis bis chBis).toList.map _).filter _) ↔ _
    rw [hbisMap denv hA]
  have hsub : ∀ i ∈ out.occ, i ∈ inp.occ := by
    intro i hi
    simp only [hout, DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi
    rcases hi with ⟨c', hc', hic⟩ | ⟨bi', hbi', hib⟩
    · obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hc'
      rw [Array.getElem?_toList] at hq
      have hlt : q < cs.size := by
        obtain ⟨h1, _⟩ := Array.getElem?_eq_some_iff.1 hq
        rw [dfApplyCs_size] at h1; omega
      refine DenseConstraintSystem.mem_occ_of_constraint (d := inp)
        (List.mem_iff_getElem?.2 ⟨q, by
          rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hlt⟩) ?_
      exact hcsVars q cs[q] c' (Array.getElem?_eq_getElem hlt) hq i hic
    · obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hbi'
      rw [Array.getElem?_toList] at hq
      obtain ⟨bi, hbi, hvars⟩ := hbisVars q bi' hq
      refine DenseConstraintSystem.mem_occ_of_bi (d := inp)
        (List.mem_iff_getElem?.2 ⟨q, by rw [Array.getElem?_toList]; exact hbi⟩) (hvars i hib)
  refine DensePassCorrect.ofEnvEq ?_ ?_ hsub ?_
  · intro denv hsatout
    have hA := hAout denv hsatout.1
    exact ⟨denv, (hsatIff denv hA).1 hsatout, hside denv hA⟩
  · intro hgi denv hsatout bi' hbi'
    have hA := hAout denv hsatout.1
    have hsatd := (hsatIff denv hA).1 hsatout
    have hmap := hbisMap denv hA
    have : denseBIEval bi' denv ∈ bis.toList.map (fun bi => denseBIEval bi denv) := by
      rw [← hmap]; exact List.mem_map.2 ⟨bi', hbi', rfl⟩
    obtain ⟨bi, hbi, heq⟩ := List.mem_map.1 this
    rw [show denseBIEval bi' denv = denseBIEval bi denv from heq.symm ▸ rfl]
    exact hgi denv hsatd bi hbi
  · intro denv hadmd hsatd
    have hA := hAin denv hsatd.1
    exact ⟨(hsatIff denv hA).2 hsatd, (hadm denv hA).2 hadmd, (hside denv hA).symm⟩


/-! ## The domain table is entailed by the system it was built from -/

theorem dfDoms_sound (cs : Array (DenseExpr p)) (isTgt : Array Bool) :
    ∀ (sv : List (Nat × VarId)) (doms : Array (Option (DfDom p))) (src : Array Nat),
      (∀ (v : VarId) (dm : DfDom p), doms[v.index]? = some (some dm) →
        denseRootsIn v dm.src = some dm.vals ∧ ∃ q : Nat, cs[q]? = some dm.src) →
      ∀ (v : VarId) (dm : DfDom p), (dfDoms cs isTgt sv doms src).1[v.index]? = some (some dm) →
        denseRootsIn v dm.src = some dm.vals ∧ ∃ q : Nat, cs[q]? = some dm.src := by
  intro sv
  induction sv with
  | nil => intro doms src h v dm hv; exact h v dm hv
  | cons qx rest ih =>
      intro doms src h v dm hv
      obtain ⟨q, x⟩ := qx
      rw [dfDoms] at hv
      split at hv
      · split at hv
        · rename_i hlt
          split at hv
          · rename_i ds hds
            refine ih _ _ ?_ v dm hv
            intro w dm' hw
            rw [Array.getElem?_setIfInBounds] at hw
            by_cases hwx : x.index = w.index
            · rw [if_pos hwx] at hw
              split at hw
              · obtain hdm : (⟨ds, q, cs[q]⟩ : DfDom p) = dm' :=
                  Option.some.inj (Option.some.inj hw)
                obtain rfl : x = w := dfVarId_eq x w hwx
                rw [← hdm]
                exact ⟨hds, ⟨q, Array.getElem?_eq_getElem hlt⟩⟩
              · exact absurd hw (by simp)
            · rw [if_neg hwx] at hw
              exact h w dm' hw
          · exact ih _ _ h v dm hv
        · exact ih _ _ h v dm hv
      · exact ih _ _ h v dm hv

/-! ## The per-key domains, re-checked against the current system -/

theorem dfKeyDomsGo_spec (tbl : Array (Option (DfDom p))) (keys : Array VarId)
    (cs : Array (DenseExpr p)) :
    ∀ (l : List VarId) (ds : List (List (ZMod p))), dfKeyDomsGo tbl keys cs l = some ds →
      ∀ (t : Nat) (v : VarId), l[t]? = some v → ∃ dm : DfDom p,
        tbl[v.index]? = some (some dm) ∧ ds[t]? = some dm.vals ∧
        cs[dm.pos]? = some dm.src ∧ dfCoveredBy keys dm.src = true := by
  intro l
  induction l with
  | nil => intro ds _ t v hv; simp at hv
  | cons w rest ih =>
      intro ds h t v hv
      rw [dfKeyDomsGo] at h
      cases htbl : tbl.getD w.index none with
      | none => rw [htbl] at h; exact absurd h (by simp)
      | some dm =>
          simp only [htbl] at h
          split at h
          · rename_i hchk
            cases hrest : dfKeyDomsGo tbl keys cs rest with
            | none => rw [hrest] at h; exact absurd h (by simp)
            | some ds' =>
                rw [hrest, Option.map_some] at h
                obtain rfl : dm.vals :: ds' = ds := Option.some.inj h
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
                obtain ⟨⟨hpos, hbeq⟩, hcov⟩ := hchk
                cases t with
                | zero =>
                    obtain hwv : w = v := by simpa using hv
                    refine ⟨dm, ?_, rfl, ?_, hcov⟩
                    · rw [← hwv]
                      have hgd : (tbl[w.index]?).getD none = some dm := by
                        rw [← Array.getD_eq_getD_getElem?]; exact htbl
                      cases hg : tbl[w.index]? with
                      | none => rw [hg] at hgd; exact absurd hgd (by simp)
                      | some o =>
                          rw [hg] at hgd
                          exact congrArg some hgd
                    · rw [Array.getElem?_eq_getElem hpos]
                      refine congrArg some (eq_of_beq ?_)
                      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos] at hbeq
                      exact hbeq
                | succ t =>
                    simp only [List.getElem?_cons_succ] at hv ⊢
                    exact ih ds' hrest t v hv
          · exact absurd h (by simp)

theorem dfKeyDoms_spec (tbl : Array (Option (DfDom p))) (keys : Array VarId)
    (cs : Array (DenseExpr p)) (doms : Array (List (ZMod p)))
    (h : dfKeyDoms tbl keys cs = some doms) :
    ∀ (j : Nat) (hj : j < keys.size), ∃ dm : DfDom p,
      tbl[(keys[j]'hj).index]? = some (some dm) ∧ doms.getD j [] = dm.vals ∧
      cs[dm.pos]? = some dm.src ∧ dfCoveredBy keys dm.src = true := by
  intro j hj
  rw [dfKeyDoms] at h
  cases hgo : dfKeyDomsGo tbl keys cs keys.toList with
  | none => rw [hgo] at h; exact absurd h (by simp)
  | some ds =>
      rw [hgo, Option.map_some] at h
      obtain rfl : ds.toArray = doms := Option.some.inj h
      obtain ⟨dm, htbl, hds, hsrc, hcov⟩ :=
        dfKeyDomsGo_spec tbl keys cs keys.toList ds hgo j (keys[j]'hj) (by
          rw [List.getElem?_eq_getElem (by simpa using hj)]
          simp)
      refine ⟨dm, htbl, ?_, hsrc, hcov⟩
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, hds]
      rfl

/-- A key slot is in range. -/
theorem dfMaxSlot_lt (keys : Array VarId) :
    ∀ (e : DenseExpr p) (m : Nat), dfMaxSlot keys e = some m → m < keys.size := by
  intro e
  induction e with
  | const n => intro m h; simp [dfMaxSlot] at h
  | var y =>
      intro m h
      rw [dfMaxSlot] at h
      obtain ⟨hj, _⟩ := dfSlot_key keys y.index m h
      exact hj
  | add a b iha ihb =>
      intro m h
      rw [dfMaxSlot] at h
      cases hma : dfMaxSlot keys a with
      | none => rw [hma] at h; exact ihb m (by simpa using h)
      | some x =>
        cases hmb : dfMaxSlot keys b with
        | none =>
            rw [hma, hmb] at h
            obtain hxm : x = m := Option.some.inj h
            rw [← hxm]
            exact iha x hma
        | some y =>
            rw [hma, hmb] at h
            obtain hxy : max x y = m := Option.some.inj h
            rw [← hxy]
            exact Nat.max_lt.2 ⟨iha x hma, ihb y hmb⟩
  | mul a b iha ihb =>
      intro m h
      rw [dfMaxSlot] at h
      cases hma : dfMaxSlot keys a with
      | none => rw [hma] at h; exact ihb m (by simpa using h)
      | some x =>
        cases hmb : dfMaxSlot keys b with
        | none =>
            rw [hma, hmb] at h
            obtain hxm : x = m := Option.some.inj h
            rw [← hxm]
            exact iha x hma
        | some y =>
            rw [hma, hmb] at h
            obtain hxy : max x y = m := Option.some.inj h
            rw [← hxy]
            exact Nat.max_lt.2 ⟨iha x hma, ihb y hmb⟩

/-! ## The covered scan -/

theorem dfCovScan_fold (keys : Array VarId) (src : Array Nat) (cs : Array (DenseExpr p))
    (touched : Array Nat) :
    ∀ (n i : Nat) (fold : List Nat) (filters : List (Nat × IExpr p)), touched.size - i ≤ n →
      (∀ q ∈ fold, dfCoveredBy keys (cs.getD q (.const (zmodZeroP p))) = false) →
      ∀ q ∈ (dfCovScan keys src cs touched i fold filters).1,
        dfCoveredBy keys (cs.getD q (.const (zmodZeroP p))) = false := by
  intro n
  induction n with
  | zero =>
      intro i fold filters hn hfold q hq
      rw [dfCovScan, dif_neg (by omega)] at hq
      exact hfold q hq
  | succ n ih =>
      intro i fold filters hn hfold q hq
      rw [dfCovScan] at hq
      by_cases hi : i < touched.size
      · rw [dif_pos hi] at hq
        by_cases hcov : dfCoveredBy keys (cs.getD touched[i] (.const (zmodZeroP p))) = true
        · rw [if_pos hcov] at hq
          split at hq
          · exact ih (i + 1) fold filters (by omega) hfold q hq
          · split at hq
            · split at hq
              · exact ih (i + 1) fold _ (by omega) hfold q hq
              · exact ih (i + 1) fold filters (by omega) hfold q hq
            · exact ih (i + 1) fold filters (by omega) hfold q hq
        · rw [if_neg hcov] at hq
          refine ih (i + 1) _ filters (by omega) ?_ q hq
          intro q' hq'
          rcases List.mem_cons.1 hq' with rfl | hmem
          · simpa using hcov
          · exact hfold q' hmem
      · rw [dif_neg hi] at hq; exact hfold q hq

theorem dfCovScan_filters (keys : Array VarId) (src : Array Nat) (cs : Array (DenseExpr p))
    (touched : Array Nat) :
    ∀ (n i : Nat) (fold : List Nat) (filters : List (Nat × IExpr p)), touched.size - i ≤ n →
      (∀ mie ∈ filters, mie.1 < keys.size ∧ ∃ c : DenseExpr p, (∃ q : Nat, cs[q]? = some c) ∧
        dfCoveredBy keys c = true ∧ denseCompileE (dfRKeys keys mie.1) c = some mie.2) →
      ∀ mie ∈ (dfCovScan keys src cs touched i fold filters).2,
        mie.1 < keys.size ∧ ∃ c : DenseExpr p,
        (∃ q : Nat, cs[q]? = some c) ∧ dfCoveredBy keys c = true ∧
        denseCompileE (dfRKeys keys mie.1) c = some mie.2 := by
  intro n
  induction n with
  | zero =>
      intro i fold filters hn hfil mie hmie
      rw [dfCovScan, dif_neg (by omega)] at hmie
      exact hfil mie hmie
  | succ n ih =>
      intro i fold filters hn hfil mie hmie
      rw [dfCovScan] at hmie
      by_cases hi : i < touched.size
      · rw [dif_pos hi] at hmie
        by_cases hcov : dfCoveredBy keys (cs.getD touched[i] (.const (zmodZeroP p))) = true
        · rw [if_pos hcov] at hmie
          split at hmie
          · exact ih (i + 1) fold filters (by omega) hfil mie hmie
          · split at hmie
            · rename_i m hm
              split at hmie
              · rename_i ie hie
                refine ih (i + 1) fold _ (by omega) ?_ mie hmie
                intro mie' hmie'
                rcases List.mem_cons.1 hmie' with rfl | hmem
                · refine ⟨dfMaxSlot_lt keys _ _ hm, cs.getD touched[i] (.const (zmodZeroP p)), ?_, hcov, hie⟩
                  -- a covered constraint is in range, so it is an element of `cs`
                  by_cases hq : touched[i] < cs.size
                  · exact ⟨touched[i], by
                      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq]; rfl⟩
                  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.2 (by omega)] at hcov
                    simp [dfCoveredBy, dfCovGo] at hcov
                · exact hfil mie' hmem
              · exact ih (i + 1) fold filters (by omega) hfil mie hmie
            · exact ih (i + 1) fold filters (by omega) hfil mie hmie
        · rw [if_neg hcov] at hmie
          exact ih (i + 1) _ filters (by omega) hfil mie hmie
      · rw [dif_neg hi] at hmie; exact hfil mie hmie


/-! ## Levels, columns and the collected changes -/

/-- Every filter parked at a level was compiled against that level's reversed key prefix. -/
theorem dfLevels_spec (k : Nat) (P : Nat → IExpr p → Prop) :
    ∀ (l : List (Nat × IExpr p)) (a : Array (List (IExpr p))),
      (∀ mie ∈ l, mie.1 < k ∧ P mie.1 mie.2) →
      (∀ (j : Nat) (ie : IExpr p), ie ∈ a.getD j [] → P j ie) →
      ∀ (j : Nat) (ie : IExpr p), ie ∈ (dfLevels k l a).getD j [] → P j ie := by
  intro l
  induction l with
  | nil => intro a _ ha j ie hie; exact ha j ie hie
  | cons mie rest ih =>
      intro a hall ha j ie hie
      refine ih _ (fun mie' hmie' => hall mie' (List.mem_cons_of_mem _ hmie')) ?_ j ie hie
      intro j' ie' hie'
      obtain ⟨hlt, hP⟩ := hall mie (List.mem_cons_self ..)
      have hmin : min mie.1 (k - 1) = mie.1 := by omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hmin] at hie'
      by_cases hj : mie.1 = j'
      · rw [if_pos hj] at hie'
        cases hg : a[j']? with
        | none => rw [hg] at hie'; simp at hie'
        | some l0 =>
            rw [hg, Option.map_some] at hie'
            rcases List.mem_cons.1 hie' with rfl | hmem
            · rw [← hj]; exact hP
            · exact ha j' ie' (by rw [Array.getD_eq_getD_getElem?, hg]; exact hmem)
      · rw [if_neg hj] at hie'
        exact ha j' ie' (by rw [Array.getD_eq_getD_getElem?]; exact hie')

/-- The filter check passes when every filter of the level vanishes on the point. -/
theorem dfAllZero_of (v : ZMod p) (pt : List (ZMod p)) :
    ∀ ies : List (IExpr p),
      (∀ ie ∈ ies, denseIExprEvalWithV denseZModOps (v :: pt) ie = 0) →
      dfAllZero (zmodZeroP p) v pt ies = true := by
  intro ies
  induction ies with
  | nil => intro _; rfl
  | cons ie rest ih =>
      intro hall
      rw [dfAllZero, Bool.and_eq_true]
      refine ⟨?_, ih (fun ie' hie' => hall ie' (List.mem_cons_of_mem _ hie'))⟩
      rw [dfEvalCons_eq, hall ie (List.mem_cons_self ..), zmodIsZero_eq]
      simp

/-- The key columns describe the real point at its survivor index. -/
theorem dfColRes_ok (survs : Array (List (ZMod p))) (keys : Array VarId) (denv : VarId → ZMod p)
    (t : Nat) (hsurv : survs[t]? = some (dfPref keys denv keys.size)) :
    ∀ (j : Nat) (hj : j < keys.size),
      DfOk denv t (.var (keys[j]'hj)) ((dfColRes survs keys.size).getD j .out) := by
  intro j hj
  have hcol : (dfColRes survs keys.size).getD j (.out) =
      (match dfUni (survs.map (fun s => denseLookupIxV (zmodZeroP p) s (keys.size - 1 - j))) with
       | some c => .uni c false
       | none => .vec (survs.map (fun s => denseLookupIxV (zmodZeroP p) s (keys.size - 1 - j))) none) := by
    rw [dfColRes, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_range]
    rw [if_pos hj]
    rfl
  have hval : (survs.map (fun s => denseLookupIxV (zmodZeroP p) s (keys.size - 1 - j)))[t]?
      = some (denv (keys[j]'hj)) := by
    rw [Array.getElem?_map, hsurv, Option.map_some,
      dfPref_lookup keys denv keys.size j hj, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hj]
    rfl
  rw [hcol]
  cases hu : dfUni (survs.map (fun s => denseLookupIxV (zmodZeroP p) s (keys.size - 1 - j))) with
  | some c =>
      refine ⟨?_, fun e' he' => by simp [DfRes.e?] at he'⟩
      show denv (keys[j]'hj) = c
      exact dfUni_sound _ c hu _ (Array.mem_iff_getElem?.2 ⟨t, hval⟩)
  | none => exact ⟨hval, fun e' he' => by simp [DfRes.e?] at he'⟩

theorem dfCollectCs_spec (ctx : DfCtx p) (cs : Array (DenseExpr p)) (all : List Nat) :
    ∀ (fold : List Nat) (acc : List (Nat × DenseExpr p)), (∀ q ∈ fold, q ∈ all) →
      (∀ qe ∈ acc, qe.1 ∈ all ∧
        dfRewrite ctx (cs.getD qe.1 (.const (zmodZeroP p))) = some qe.2) →
      ∀ qe ∈ dfCollectCs ctx cs fold acc, qe.1 ∈ all ∧
        dfRewrite ctx (cs.getD qe.1 (.const (zmodZeroP p))) = some qe.2 := by
  intro fold
  induction fold with
  | nil => intro acc _ hacc qe hqe; exact hacc qe hqe
  | cons q rest ih =>
      intro acc hsub hacc qe hqe
      rw [dfCollectCs] at hqe
      cases hr : dfRewrite ctx (cs.getD q (.const (zmodZeroP p))) with
      | none =>
          rw [hr] at hqe
          exact ih acc (fun q' h => hsub q' (List.mem_cons_of_mem _ h)) hacc qe hqe
      | some e =>
          rw [hr] at hqe
          refine ih ((q, e) :: acc) (fun q' h => hsub q' (List.mem_cons_of_mem _ h)) ?_ qe hqe
          intro qe' hqe'
          rcases List.mem_cons.1 hqe' with rfl | hmem
          · exact ⟨hsub q (List.mem_cons_self ..), hr⟩
          · exact hacc qe' hmem

theorem dfCollectCs_mem_fold (ctx : DfCtx p) (cs : Array (DenseExpr p)) (fold : List Nat)
    (qe : Nat × DenseExpr p) (hqe : qe ∈ dfCollectCs ctx cs fold []) :
    qe.1 ∈ fold ∧ dfRewrite ctx (cs.getD qe.1 (.const (zmodZeroP p))) = some qe.2 :=
  dfCollectCs_spec ctx cs fold fold [] (fun _ h => h) (fun _ h => by simp at h) qe hqe

theorem dfCollectBis_spec (ctx : DfCtx p) (bis : Array (BusInteraction (DenseExpr p)))
    (touched : Array Nat) :
    ∀ (n i : Nat) (acc : List (Nat × BusInteraction (DenseExpr p))), touched.size - i ≤ n →
      (∀ qb ∈ acc, ∃ bi, bis[qb.1]? = some bi ∧ dfRewriteBi ctx bi = some qb.2) →
      ∀ qb ∈ dfCollectBis ctx bis i touched acc,
        ∃ bi, bis[qb.1]? = some bi ∧ dfRewriteBi ctx bi = some qb.2 := by
  intro n
  induction n with
  | zero =>
      intro i acc hn hacc qb hqb
      rw [dfCollectBis, dif_neg (by omega)] at hqb
      exact hacc qb hqb
  | succ n ih =>
      intro i acc hn hacc qb hqb
      rw [dfCollectBis] at hqb
      by_cases hi : i < touched.size
      · rw [dif_pos hi] at hqb
        by_cases hq : touched[i] < bis.size
        · rw [dif_pos hq] at hqb
          cases hr : dfRewriteBi ctx bis[touched[i]] with
          | none => rw [hr] at hqb; exact ih (i + 1) acc (by omega) hacc qb hqb
          | some b =>
              rw [hr] at hqb
              refine ih (i + 1) _ (by omega) ?_ qb hqb
              intro qb' hqb'
              rcases List.mem_cons.1 hqb' with rfl | hmem
              · exact ⟨bis[touched[i]], Array.getElem?_eq_getElem hq, hr⟩
              · exact hacc qb' hmem
        · rw [dif_neg hq] at hqb; exact ih (i + 1) acc (by omega) hacc qb hqb
      · rw [dif_neg hi] at hqb; exact hacc qb hqb


/-! ## OutputVariable containment, independent of any assignment -/

theorem dfRebuild_vars (isAdd : Bool) (mk : DenseExpr p → DenseExpr p → DenseExpr p)
    (hvars : ∀ x y : DenseExpr p, (mk x y).vars = x.vars ++ y.vars)
    (hmk : ∀ x y : DenseExpr p, (if isAdd then DenseExpr.add x y else DenseExpr.mul x y) = mk x y)
    (a b : DenseExpr p) (ea eb : Option (DenseExpr p))
    (hA : ∀ e' : DenseExpr p, ea = some e' → ∀ i ∈ e'.vars, i ∈ a.vars)
    (hB : ∀ e' : DenseExpr p, eb = some e' → ∀ i ∈ e'.vars, i ∈ b.vars) :
    ∀ e' : DenseExpr p, dfRebuild isAdd a b ea eb = some e' →
      ∀ i ∈ e'.vars, i ∈ (mk a b).vars := by
  intro e' he' i hi
  have hagA : ∀ i ∈ (ea.getD a).vars, i ∈ a.vars := by
    cases ea with
    | none => exact fun i hi => hi
    | some x => exact hA x rfl
  have hagB : ∀ i ∈ (eb.getD b).vars, i ∈ b.vars := by
    cases eb with
    | none => exact fun i hi => hi
    | some x => exact hB x rfl
  have hval : e' = mk (ea.getD a) (eb.getD b) := by
    unfold dfRebuild at he'
    cases ea with
    | none =>
        cases eb with
        | none => exact absurd he' (by simp)
        | some y => rw [← hmk]; exact (Option.some.inj he').symm
    | some x => rw [← hmk]; exact (Option.some.inj he').symm
  subst hval
  rw [hvars] at hi ⊢
  rcases List.mem_append.1 hi with hi | hi
  · exact List.mem_append_left _ (hagA i hi)
  · exact List.mem_append_right _ (hagB i hi)

theorem dfComb_vars (isAdd : Bool) (mk : DenseExpr p → DenseExpr p → DenseExpr p)
    (hvars : ∀ x y : DenseExpr p, (mk x y).vars = x.vars ++ y.vars)
    (hmk : ∀ x y : DenseExpr p, (if isAdd then DenseExpr.add x y else DenseExpr.mul x y) = mk x y)
    (a b : DenseExpr p) (ra rb : DfRes p)
    (hA : ∀ e' : DenseExpr p, ra.e? = some e' → ∀ i ∈ e'.vars, i ∈ a.vars)
    (hB : ∀ e' : DenseExpr p, rb.e? = some e' → ∀ i ∈ e'.vars, i ∈ b.vars) :
    ∀ e' : DenseExpr p, (dfComb isAdd a b ra rb).e? = some e' →
      ∀ i ∈ e'.vars, i ∈ (mk a b).vars := by
  have hconst : ∀ (c : ZMod p) (e' : DenseExpr p), (DfRes.uni c true).e? = some e' →
      ∀ i ∈ e'.vars, i ∈ (mk a b).vars := by
    intro c e' he' i hi
    have hde : (DfRes.uni c true).e? = some (DenseExpr.const c) := by simp [DfRes.e?]
    rw [hde] at he'
    obtain rfl : DenseExpr.const c = e' := Option.some.inj he'
    simp [DenseExpr.vars] at hi
  have hout : ∀ ea eb : Option (DenseExpr p),
      (∀ e' : DenseExpr p, ea = some e' → ∀ i ∈ e'.vars, i ∈ a.vars) →
      (∀ e' : DenseExpr p, eb = some e' → ∀ i ∈ e'.vars, i ∈ b.vars) →
      ∀ e' : DenseExpr p,
        (match dfRebuild isAdd a b ea eb with | none => DfRes.out | some e => DfRes.outCh e).e?
          = some e' → ∀ i ∈ e'.vars, i ∈ (mk a b).vars := by
    intro ea eb hA' hB' e' he'
    have hreb := dfRebuild_vars isAdd mk hvars hmk a b ea eb hA' hB'
    cases hd : dfRebuild isAdd a b ea eb with
    | none => rw [hd] at he'; simp [DfRes.e?] at he'
    | some e0 =>
        rw [hd] at he'
        have hde : (DfRes.outCh e0).e? = some e0 := rfl
        rw [hde] at he'
        obtain rfl : e0 = e' := Option.some.inj he'
        exact hreb _ hd
  have hvec : ∀ (s : Array (ZMod p)) (ea eb : Option (DenseExpr p)),
      (∀ e' : DenseExpr p, ea = some e' → ∀ i ∈ e'.vars, i ∈ a.vars) →
      (∀ e' : DenseExpr p, eb = some e' → ∀ i ∈ e'.vars, i ∈ b.vars) →
      ∀ e' : DenseExpr p,
        (match dfUni s with
         | some c => DfRes.uni c true
         | none => DfRes.vec s (dfRebuild isAdd a b ea eb)).e? = some e' →
        ∀ i ∈ e'.vars, i ∈ (mk a b).vars := by
    intro s ea eb hA' hB' e' he'
    have hreb := dfRebuild_vars isAdd mk hvars hmk a b ea eb hA' hB'
    cases hu : dfUni s with
    | some c => rw [hu] at he'; exact hconst c e' he'
    | none =>
        rw [hu] at he'
        have hde : (DfRes.vec s (dfRebuild isAdd a b ea eb)).e? = dfRebuild isAdd a b ea eb := rfl
        rw [hde] at he'
        exact hreb e' he'
  unfold dfComb
  cases ra with
  | out => cases rb <;> exact hout _ _ hA hB
  | outCh ea => cases rb <;> exact hout _ _ hA hB
  | uni x fa =>
      cases rb with
      | out => exact hout _ _ hA hB
      | outCh eb => exact hout _ _ hA hB
      | uni y fb => exact hconst _
      | vec vb eb => exact hvec _ _ _ hA hB
  | vec va ea =>
      cases rb with
      | out => exact hout _ _ hA hB
      | outCh eb => exact hout _ _ hA hB
      | uni y fb => exact hvec _ _ _ hA hB
      | vec vb eb => exact hvec _ _ _ hA hB

/-- The classified columns carry no rewrite. -/
theorem dfColRes_e? (survs : Array (List (ZMod p))) (k : Nat) (j : Nat) :
    ((dfColRes survs k).getD j (.out : DfRes p)).e? = none := by
  rw [dfColRes, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases hj : j < k
  · rw [if_pos hj]
    show ((match dfUni (survs.map (fun s => denseLookupIxV (zmodZeroP p) s (k - 1 - j))) with
      | some c => DfRes.uni c false
      | none => DfRes.vec _ none) : DfRes p).e? = none
    cases hu : dfUni (survs.map (fun s => denseLookupIxV (zmodZeroP p) s (k - 1 - j))) <;> rfl
  · rw [if_neg hj]; rfl

/-- The traversal introduces no variable. -/
theorem dfGo_vars (ctx : DfCtx p) (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none) :
    ∀ (e e' : DenseExpr p), (dfGo ctx e).e? = some e' → ∀ i ∈ e'.vars, i ∈ e.vars := by
  intro e
  induction e with
  | const c => intro e' he'; simp [dfGo, DfRes.e?] at he'
  | var y =>
      intro e' he'
      rw [dfGo] at he'
      cases hslot : dfSlotGo ctx.keys y.index 0 with
      | none => rw [hslot] at he'; simp [DfRes.e?] at he'
      | some j => rw [hslot, hcol j] at he'; exact absurd he' (by simp)
  | add a b iha ihb =>
      intro e' he'
      rw [dfGo] at he'
      exact dfComb_vars true DenseExpr.add (fun _ _ => rfl) (fun _ _ => rfl) a b _ _ iha ihb e' he'
  | mul a b iha ihb =>
      intro e' he'
      rw [dfGo] at he'
      exact dfComb_vars false DenseExpr.mul (fun _ _ => rfl) (fun _ _ => rfl) a b _ _ iha ihb e' he'

theorem dfRewrite_vars (ctx : DfCtx p) (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none)
    (e e' : DenseExpr p) (h : dfRewrite ctx e = some e') : ∀ i ∈ e'.vars, i ∈ e.vars :=
  dfGo_vars ctx hcol e e' h

theorem dfRewriteList_vars (ctx : DfCtx p)
    (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none) :
    ∀ (es es' : List (DenseExpr p)), dfRewriteList ctx es = some es' →
      ∀ (i : VarId), (∃ e' ∈ es', i ∈ e'.vars) → ∃ e ∈ es, i ∈ e.vars := by
  intro es
  induction es with
  | nil => intro es' h; simp [dfRewriteList] at h
  | cons e rest ih =>
      intro es' h
      rw [dfRewriteList] at h
      cases hr : dfRewrite ctx e with
      | none =>
          cases hrs : dfRewriteList ctx rest with
          | none => rw [hr, hrs] at h; exact absurd h (by simp)
          | some rest' =>
              rw [hr, hrs] at h
              simp only [Option.some.injEq] at h
              subst h
              intro i hi
              obtain ⟨e0, he0, hie⟩ := hi
              rcases List.mem_cons.1 he0 with rfl | hmem
              · exact ⟨e0, List.mem_cons_self .., hie⟩
              · obtain ⟨e1, he1, hie1⟩ := ih rest' hrs i ⟨e0, hmem, hie⟩
                exact ⟨e1, List.mem_cons_of_mem _ he1, hie1⟩
      | some e' =>
          cases hrs : dfRewriteList ctx rest with
          | none =>
              rw [hr, hrs] at h
              simp only [Option.some.injEq] at h
              subst h
              intro i hi
              obtain ⟨e0, he0, hie⟩ := hi
              rcases List.mem_cons.1 he0 with rfl | hmem
              · exact ⟨e, List.mem_cons_self .., dfRewrite_vars ctx hcol e _ hr i hie⟩
              · exact ⟨e0, List.mem_cons_of_mem _ hmem, hie⟩
          | some rest' =>
              rw [hr, hrs] at h
              simp only [Option.some.injEq] at h
              subst h
              intro i hi
              obtain ⟨e0, he0, hie⟩ := hi
              rcases List.mem_cons.1 he0 with rfl | hmem
              · exact ⟨e, List.mem_cons_self .., dfRewrite_vars ctx hcol e _ hr i hie⟩
              · obtain ⟨e1, he1, hie1⟩ := ih rest' hrs i ⟨e0, hmem, hie⟩
                exact ⟨e1, List.mem_cons_of_mem _ he1, hie1⟩

theorem dfRewriteBi_vars (ctx : DfCtx p)
    (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none)
    (bi bi' : BusInteraction (DenseExpr p)) (h : dfRewriteBi ctx bi = some bi') :
    ∀ i ∈ denseBIVars bi', i ∈ denseBIVars bi := by
  rw [dfRewriteBi] at h
  have hshape : bi' = { bi with
      multiplicity := (dfRewrite ctx bi.multiplicity).getD bi.multiplicity,
      payload := (dfRewriteList ctx bi.payload).getD bi.payload } := by
    cases hm : dfRewrite ctx bi.multiplicity with
    | none =>
        cases hp : dfRewriteList ctx bi.payload with
        | none => rw [hm, hp] at h; exact absurd h (by simp)
        | some pl' => rw [hm, hp] at h; exact (Option.some.inj h).symm
    | some m' => rw [hm] at h; exact (Option.some.inj h).symm
  subst hshape
  intro i hi
  rw [denseBIVars, List.mem_append] at hi ⊢
  rcases hi with hi | hi
  · refine Or.inl ?_
    cases hm : dfRewrite ctx bi.multiplicity with
    | none => rw [hm] at hi; exact hi
    | some m' => rw [hm] at hi; exact dfRewrite_vars ctx hcol _ m' hm i hi
  · rw [List.mem_flatMap] at hi
    obtain ⟨e', he', hie⟩ := hi
    cases hp : dfRewriteList ctx bi.payload with
    | none =>
        rw [hp] at he'
        exact Or.inr (List.mem_flatMap.2 ⟨e', he', hie⟩)
    | some pl' =>
        rw [hp] at he'
        obtain ⟨e0, he0, hie0⟩ := dfRewriteList_vars ctx hcol bi.payload pl' hp i ⟨e', he', hie⟩
        exact Or.inr (List.mem_flatMap.2 ⟨e0, he0, hie0⟩)

/-! ## One target's fold -/

/-- Every covered constraint vanishes — the anchor both sides of a step supply, since the fold
    leaves covered constraints exactly where they are. -/
def DfCovered (keys : Array VarId) (cs : Array (DenseExpr p)) (denv : VarId → ZMod p) : Prop :=
  ∀ c ∈ cs, dfCoveredBy keys c = true → c.eval denv = 0

/-- Under the anchor, the real assignment's key values are one of the enumerated survivors, so the
    traversal's columns describe it. -/
theorem dfPlan_colRes [Fact p.Prime] (ix : DfIdx p) (keys : Array VarId)
    (cs : Array (DenseExpr p)) (doms : Array (List (ZMod p))) (denv : VarId → ZMod p)
    (htbl : ∀ (v : VarId) (dm : DfDom p), ix.doms[v.index]? = some (some dm) →
      denseRootsIn v dm.src = some dm.vals)
    (hkd : dfKeyDoms ix.doms keys cs = some doms)
    (hA : DfCovered keys cs denv)
    (filters : List (Nat × IExpr p))
    (hfilters : ∀ mie ∈ filters, mie.1 < keys.size ∧ ∃ c : DenseExpr p,
      (∃ q : Nat, cs[q]? = some c) ∧ dfCoveredBy keys c = true ∧
      denseCompileE (dfRKeys keys mie.1) c = some mie.2) :
    ∃ t : Nat, ∀ (j : Nat) (hj : j < keys.size),
      DfOk denv t (.var (keys[j]'hj))
        ((dfColRes (dfEnumGo (zmodZeroP p) (dfLevels keys.size filters
          (Array.replicate keys.size [])) doms keys.size 0 #[[]]) keys.size).getD j .out) := by
  -- each key's value lies in its domain, because the entailing constraint is covered and present
  have hdom : ∀ j, j < keys.size → denv (keys.getD j ⟨0⟩) ∈ doms.getD j [] := by
    intro j hj
    obtain ⟨dm, htblj, hvals, hsrc, hcov⟩ := dfKeyDoms_spec ix.doms keys cs doms hkd j hj
    have hroots : denseRootsIn (keys[j]'hj) dm.src = some dm.vals := htbl _ dm htblj
    have hzero : dm.src.eval denv = 0 :=
      hA dm.src (Array.mem_iff_getElem?.2 ⟨dm.pos, hsrc⟩) hcov
    rw [hvals, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    exact denseRootsIn_sound _ dm.src dm.vals hroots denv hzero
  -- every filter of a level vanishes on the real prefix of that level
  have hfil : ∀ j, j < keys.size →
      dfAllZero (zmodZeroP p) (denv (keys.getD j ⟨0⟩)) (dfPref keys denv j)
        ((dfLevels keys.size filters (Array.replicate keys.size [])).getD j []) = true := by
    intro j hj
    refine dfAllZero_of _ _ _ ?_
    intro ie hie
    have hP : ∀ (j' : Nat) (ie' : IExpr p), ie' ∈ (dfLevels keys.size filters
        (Array.replicate keys.size [])).getD j' [] →
        ∃ c : DenseExpr p, dfCoveredBy keys c = true ∧ c.eval denv = 0 ∧
          denseCompileE (dfRKeys keys j') c = some ie' := by
      refine dfLevels_spec keys.size
        (fun j' ie' => ∃ c : DenseExpr p, dfCoveredBy keys c = true ∧ c.eval denv = 0 ∧
          denseCompileE (dfRKeys keys j') c = some ie') filters _ ?_ ?_
      · intro mie hmie
        obtain ⟨hlt, c, ⟨q, hq⟩, hcov, hce⟩ := hfilters mie hmie
        exact ⟨hlt, c, hcov, hA c (Array.mem_iff_getElem?.2 ⟨q, hq⟩) hcov, hce⟩
      · intro j' ie' hie'
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hie'
        split at hie' <;> simp at hie'
    obtain ⟨c, hcov, hzero, hce⟩ := hP j ie hie
    -- the level-`j` point is the values of `dfRKeys keys j`, the list `ie` was compiled against
    have hpt : denv (keys.getD j ⟨0⟩) :: dfPref keys denv j = (dfRKeys keys j).map denv := by
      rw [← dfPref_eq_map keys denv j]; rfl
    rw [hpt, denseCompileE_evalV denseZModOps (dfRKeys keys j) _ c ie hce]
    rw [DenseExpr.eval_congr c _ denv (fun v hv =>
      denseEnvOfKeysV_map denv (dfRKeys keys j) v (denseCompileE_vars (dfRKeys keys j) c ie hce v hv))]
    exact hzero
  -- so the real point survives the enumeration
  have hmem : dfPref keys denv keys.size ∈ dfEnumGo (zmodZeroP p)
      (dfLevels keys.size filters (Array.replicate keys.size [])) doms keys.size 0 #[[]] :=
    dfEnumGo_mem _ doms keys.size keys denv hdom hfil keys.size 0 #[[]] (by omega) (by omega)
      (by show dfPref keys denv 0 ∈ (#[[]] : Array (List (ZMod p))); simp [dfPref])
  obtain ⟨t, ht⟩ := Array.mem_iff_getElem?.1 hmem
  exact ⟨t, dfColRes_ok _ keys denv t ht⟩

/-- One target is a correct step. -/
theorem dfPlan_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (ix : DfIdx p) (keys : Array VarId) (cs : Array (DenseExpr p))
    (bis : Array (BusInteraction (DenseExpr p)))
    (htbl : ∀ (v : VarId) (dm : DfDom p), ix.doms[v.index]? = some (some dm) →
      denseRootsIn v dm.src = some dm.vals) :
    DensePassCorrect isInput ⟨cs.toList, bis.toList⟩
      ⟨(dfApplyCs cs (dfPlan ix keys cs bis).1).toList,
       (dfApplyBis bis (dfPlan ix keys cs bis).2).toList⟩ [] bs := by
  rw [dfPlan]
  split
  · exact DensePassCorrect_refl isInput _ bs
  · rename_i doms hkd
    split
    · exact DensePassCorrect_refl isInput _ bs
    · dsimp only
      split
      · exact DensePassCorrect_refl isInput _ bs
      · rename_i hbox _
        set touched := dfTouched ix.csB keys with htouched
        set fs := dfCovScan keys ix.src cs touched 0 [] [] with hfs
        set survs := dfEnumGo (zmodZeroP p)
          (dfLevels keys.size fs.2 (Array.replicate keys.size [])) doms keys.size 0 #[[]]
          with hsurvs
        set ctx : DfCtx p := ⟨keys, dfColRes survs keys.size⟩ with hctx
        -- the filters are covered constraints of the current system
        have hfilters : ∀ mie ∈ fs.2, mie.1 < keys.size ∧ ∃ c : DenseExpr p,
            (∃ q : Nat, cs[q]? = some c) ∧ dfCoveredBy keys c = true ∧
            denseCompileE (dfRKeys keys mie.1) c = some mie.2 :=
          dfCovScan_filters keys ix.src cs touched touched.size 0 [] [] (by omega)
            (fun _ h => by simp at h)
        -- the anchor: every covered constraint vanishes, on either side of the step
        have hcovNotFold : ∀ q ∈ fs.1,
            dfCoveredBy keys (cs.getD q (.const (zmodZeroP p))) = false :=
          dfCovScan_fold keys ix.src cs touched touched.size 0 [] [] (by omega)
            (fun _ h => by simp at h)
        have hAin : ∀ denv : VarId → ZMod p, (∀ c ∈ cs.toList, c.eval denv = 0) →
            DfCovered keys cs denv := by
          intro denv hall c hc _
          exact hall c (by simpa using hc)
        have hAout : ∀ denv : VarId → ZMod p,
            (∀ c ∈ (dfApplyCs cs (dfCollectCs ctx cs fs.1 [])).toList, c.eval denv = 0) →
            DfCovered keys cs denv := by
          intro denv hall c hc hcov
          obtain ⟨q, hq⟩ := Array.mem_iff_getElem?.1 hc
          have hqnot : ∀ e : DenseExpr p, (q, e) ∉ dfCollectCs ctx cs fs.1 [] := by
            intro e hmem
            obtain ⟨hin, _⟩ := dfCollectCs_mem_fold ctx cs fs.1 (q, e) hmem
            have hf := hcovNotFold q hin
            rw [Array.getD_eq_getD_getElem?, hq] at hf
            simp only [Option.getD_some] at hf
            rw [hf] at hcov
            exact absurd hcov (by simp)
          rcases dfApplyCs_getElem? (dfCollectCs ctx cs fs.1 []) cs q with h | ⟨e, hmem, he⟩
          · refine hall c (List.mem_iff_getElem?.2 ⟨q, ?_⟩)
            rw [Array.getElem?_toList, h, hq]
          · exact absurd hmem (hqnot e)
        refine dfStep_general bs isInput cs bis _ _ (DfCovered keys cs) hAout hAin ?_ ?_ ?_ ?_
        · -- constraint agreement
          intro denv hA q e hmem c hc
          obtain ⟨_, hrw⟩ := dfCollectCs_mem_fold ctx cs fs.1 (q, e) hmem
          obtain ⟨t, hcol⟩ := dfPlan_colRes ix keys cs doms denv htbl hkd hA fs.2 hfilters
          rw [Array.getD_eq_getD_getElem?, hc] at hrw
          exact (dfRewrite_ok ctx denv t (by rw [hctx]; exact hcol) c e hrw).1
        · -- constraint variables
          intro q e hmem c hc
          obtain ⟨_, hrw⟩ := dfCollectCs_mem_fold ctx cs fs.1 (q, e) hmem
          rw [Array.getD_eq_getD_getElem?, hc] at hrw
          exact dfGo_vars ctx (fun j => by rw [hctx]; exact dfColRes_e? _ _ j) c e hrw
        · -- interaction agreement
          intro denv hA q b hmem bi hbi
          obtain ⟨bi0, hbi0, hrw⟩ := dfCollectBis_spec ctx bis (dfTouched ix.bisB keys)
            (dfTouched ix.bisB keys).size 0 [] (by omega) (fun _ h => by simp at h) (q, b) hmem
          rw [hbi] at hbi0
          obtain rfl : bi = bi0 := Option.some.inj hbi0
          obtain ⟨t, hcol⟩ := dfPlan_colRes ix keys cs doms denv htbl hkd hA fs.2 hfilters
          exact (dfRewriteBi_ok ctx denv t (by rw [hctx]; exact hcol) bi b hrw).1
        · -- interaction variables
          intro q b hmem bi hbi
          obtain ⟨bi0, hbi0, hrw⟩ := dfCollectBis_spec ctx bis (dfTouched ix.bisB keys)
            (dfTouched ix.bisB keys).size 0 [] (by omega) (fun _ h => by simp at h) (q, b) hmem
          rw [hbi] at hbi0
          obtain rfl : bi = bi0 := Option.some.inj hbi0
          exact dfRewriteBi_vars ctx (fun j => by rw [hctx]; exact dfColRes_e? _ _ j) bi b hrw


/-! ## The target loop -/

theorem dfLoop_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (csB bisB : Array (Array Nat)) (tbl : Array (Option (DfDom p))) (src : Array Nat)
    (htbl : ∀ (v : VarId) (dm : DfDom p), tbl[v.index]? = some (some dm) →
      denseRootsIn v dm.src = some dm.vals) :
    ∀ (targets : List (Array VarId)) (cs : Array (DenseExpr p))
      (bis : Array (BusInteraction (DenseExpr p))) (ch : Bool),
      DensePassCorrect isInput ⟨cs.toList, bis.toList⟩
        ⟨(dfLoop ⟨csB, bisB, tbl, src⟩ targets cs bis ch).1.toList,
         (dfLoop ⟨csB, bisB, tbl, src⟩ targets cs bis ch).2.1.toList⟩ [] bs := by
  intro targets
  induction targets with
  | nil => intro cs bis ch; exact DensePassCorrect_refl isInput _ bs
  | cons keys rest ih =>
      intro cs bis ch
      rw [dfLoop]
      by_cases hempty : ((dfPlan ⟨csB, bisB, tbl, src⟩ keys cs bis).1.isEmpty &&
          (dfPlan ⟨csB, bisB, tbl, src⟩ keys cs bis).2.isEmpty) = true
      · rw [if_pos hempty]
        exact ih cs bis ch
      · rw [if_neg hempty]
        exact DensePassCorrect.trans
          (dfPlan_correct bs isInput ⟨csB, bisB, tbl, src⟩ keys cs bis htbl) (ih _ _ true)

/-! ## Coverage preservation -/

theorem dfRewrite_covered (reg : VarRegistry) (ctx : DfCtx p)
    (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none)
    {e e' : DenseExpr p} (h : dfRewrite ctx e = some e') (hc : e.CoveredBy reg) :
    e'.CoveredBy reg :=
  fun i hi => hc i (dfRewrite_vars ctx hcol e e' h i hi)

theorem dfApplyCs_covered (reg : VarRegistry) (ctx : DfCtx p)
    (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none) (cs : Array (DenseExpr p))
    (fold : List Nat) (hcs : ∀ c ∈ cs.toList, c.CoveredBy reg) :
    ∀ c ∈ (dfApplyCs cs (dfCollectCs ctx cs fold [])).toList, c.CoveredBy reg := by
  intro c hc
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hc
  rw [Array.getElem?_toList] at hq
  rcases dfApplyCs_getElem? (dfCollectCs ctx cs fold []) cs q with h | ⟨e, hmem, he⟩
  · rw [h] at hq
    exact hcs c (List.mem_iff_getElem?.2 ⟨q, by rw [Array.getElem?_toList]; exact hq⟩)
  · rw [he] at hq
    obtain hec : e = c := Option.some.inj hq
    rw [hec] at hmem
    obtain ⟨_, hrw⟩ := dfCollectCs_mem_fold ctx cs fold (q, c) hmem
    have hin : q < cs.size := by
      by_contra hcon
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.2 (by omega)] at hrw
      simp [dfRewrite, dfGo, DfRes.e?] at hrw
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hin] at hrw
    exact dfRewrite_covered reg ctx hcol hrw
      (hcs cs[q] (List.mem_iff_getElem?.2 ⟨q, by
        rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hin⟩))

theorem dfApplyBis_covered (reg : VarRegistry) (ctx : DfCtx p)
    (hcol : ∀ j : Nat, ((ctx.colRes.getD j .out).e?) = none)
    (bis : Array (BusInteraction (DenseExpr p))) (touched : Array Nat)
    (hbis : ∀ bi ∈ bis.toList, bi.multiplicity.CoveredBy reg ∧
      ∀ e ∈ bi.payload, e.CoveredBy reg) :
    ∀ bi ∈ (dfApplyBis bis (dfCollectBis ctx bis 0 touched [])).toList,
      bi.multiplicity.CoveredBy reg ∧ ∀ e ∈ bi.payload, e.CoveredBy reg := by
  intro bi' hbi'
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hbi'
  rw [Array.getElem?_toList] at hq
  obtain ⟨bi0, hbi0, hsub⟩ :=
    dfApplyBis_vars bis (dfCollectBis ctx bis 0 touched []) bis rfl
      (fun q bi bi0 h1 h2 => by rw [h1] at h2; rw [Option.some.inj h2]; exact fun i hi => hi)
      (fun qb hqb bi0 hbi0 => by
        obtain ⟨bi1, hbi1, hrw⟩ := dfCollectBis_spec ctx bis touched touched.size 0 []
          (by omega) (fun _ h => by simp at h) qb hqb
        rw [hbi0] at hbi1
        obtain rfl : bi0 = bi1 := Option.some.inj hbi1
        exact dfRewriteBi_vars ctx hcol bi0 qb.2 hrw)
      q bi' hq
  obtain ⟨hm, hp⟩ := hbis bi0 (List.mem_iff_getElem?.2 ⟨q, by
    rw [Array.getElem?_toList]; exact hbi0⟩)
  refine ⟨fun i hi => ?_, fun e he i hi => ?_⟩
  · refine (by
      rcases List.mem_append.1 (hsub i (by rw [denseBIVars, List.mem_append]; exact Or.inl hi))
        with h1 | h1
      · exact hm i h1
      · obtain ⟨e0, he0, hie0⟩ := List.mem_flatMap.1 h1
        exact hp e0 he0 i hie0)
  · refine (by
      rcases List.mem_append.1 (hsub i (by
        rw [denseBIVars, List.mem_append]
        exact Or.inr (List.mem_flatMap.2 ⟨e, he, hi⟩))) with h1 | h1
      · exact hm i h1
      · obtain ⟨e0, he0, hie0⟩ := List.mem_flatMap.1 h1
        exact hp e0 he0 i hie0)

theorem dfLoop_covered (reg : VarRegistry) (csB bisB : Array (Array Nat))
    (tbl : Array (Option (DfDom p))) (src : Array Nat) :
    ∀ (targets : List (Array VarId)) (cs : Array (DenseExpr p))
      (bis : Array (BusInteraction (DenseExpr p))) (ch : Bool),
      (∀ c ∈ cs.toList, c.CoveredBy reg) →
      (∀ bi ∈ bis.toList, bi.multiplicity.CoveredBy reg ∧ ∀ e ∈ bi.payload, e.CoveredBy reg) →
      (∀ c ∈ (dfLoop ⟨csB, bisB, tbl, src⟩ targets cs bis ch).1.toList, c.CoveredBy reg) ∧
      (∀ bi ∈ (dfLoop ⟨csB, bisB, tbl, src⟩ targets cs bis ch).2.1.toList,
        bi.multiplicity.CoveredBy reg ∧ ∀ e ∈ bi.payload, e.CoveredBy reg) := by
  intro targets
  induction targets with
  | nil => intro cs bis ch hcs hbis; exact ⟨hcs, hbis⟩
  | cons keys rest ih =>
      intro cs bis ch hcs hbis
      rw [dfLoop]
      by_cases hempty : ((dfPlan ⟨csB, bisB, tbl, src⟩ keys cs bis).1.isEmpty &&
          (dfPlan ⟨csB, bisB, tbl, src⟩ keys cs bis).2.isEmpty) = true
      · rw [if_pos hempty]; exact ih cs bis ch hcs hbis
      · rw [if_neg hempty]
        refine ih _ _ true ?_ ?_
        · -- the constraint side of one step
          rw [dfPlan]
          split
          · exact hcs
          · split
            · exact hcs
            · dsimp only
              split
              · exact hcs
              · exact dfApplyCs_covered reg _ (fun j => dfColRes_e? _ _ j) cs _ hcs
        · rw [dfPlan]
          split
          · exact hbis
          · split
            · exact hbis
            · dsimp only
              split
              · exact hbis
              · exact dfApplyBis_covered reg _ (fun j => dfColRes_e? _ _ j) bis _ hbis

/-! ## The pass -/

theorem dfRunWith_correct [Fact p.Prime] (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (n : Nat) (svRev : List (Nat × VarId))
    (dvs : Array (Option (List VarId))) (targets : List (Array VarId)) :
    DensePassCorrect isInput d (dfRunWith d n svRev dvs targets) [] bs := by
  rw [dfRunWith]
  set isTgt := dfMarkKeys targets (Array.replicate n false) with hisTgt
  set cs := d.algebraicConstraints.toArray with hcsDef
  set tbl := dfDoms cs isTgt svRev (Array.replicate n none) (Array.replicate n 0) with htblDef
  set csB := dfCsBuckets isTgt dvs 0 d.algebraicConstraints (Array.replicate n #[]) with hcsB
  set bisB := dfBisBuckets isTgt 0 d.busInteractions (Array.replicate n #[]) with hbisB
  have htbl : ∀ (v : VarId) (dm : DfDom p), tbl.1[v.index]? = some (some dm) →
      denseRootsIn v dm.src = some dm.vals := by
    intro v dm hv
    rw [htblDef] at hv
    exact (dfDoms_sound cs isTgt svRev _ _ (fun w dm' hw => by
      rw [Array.getElem?_replicate] at hw
      split at hw <;> simp at hw) v dm hv).1
  split
  · have hstep := dfLoop_correct bs isInput csB bisB tbl.1 tbl.2 htbl targets cs
      d.busInteractions.toArray false
    simpa [hcsDef] using hstep
  · exact DensePassCorrect_refl isInput d bs

theorem dfRunWith_covered (reg : VarRegistry) (d : DenseConstraintSystem p) (n : Nat)
    (svRev : List (Nat × VarId)) (dvs : Array (Option (List VarId)))
    (targets : List (Array VarId)) (hcov : d.CoveredBy reg) :
    (dfRunWith d n svRev dvs targets).CoveredBy reg := by
  rw [dfRunWith]
  set isTgt := dfMarkKeys targets (Array.replicate n false) with hisTgt
  set cs := d.algebraicConstraints.toArray with hcsDef
  set tbl := dfDoms cs isTgt svRev (Array.replicate n none) (Array.replicate n 0) with htblDef
  set csB := dfCsBuckets isTgt dvs 0 d.algebraicConstraints (Array.replicate n #[]) with hcsB
  set bisB := dfBisBuckets isTgt 0 d.busInteractions (Array.replicate n #[]) with hbisB
  split
  · have h := dfLoop_covered reg csB bisB tbl.1 tbl.2 targets cs d.busInteractions.toArray false
      (by rw [hcsDef]; simpa using hcov.1) (by simpa using hcov.2)
    exact ⟨by simpa using h.1, by simpa using h.2⟩
  · exact hcov

theorem dfRun_correct (pw : PrimeWitness p) (bs : BusSemantics p) (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) : DensePassCorrect isInput d (dfRun pw d) [] bs := by
  rw [dfRun]
  split
  · rename_i hprime
    haveI : Fact p.Prime := ⟨pw.correct hprime⟩
    dsimp only
    split
    · exact DensePassCorrect_refl isInput d bs
    · exact dfRunWith_correct bs isInput d _ _ _ _
  · exact DensePassCorrect_refl isInput d bs

theorem dfRun_covered (pw : PrimeWitness p) (reg : VarRegistry) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) : (dfRun pw d).CoveredBy reg := by
  rw [dfRun]
  split
  · dsimp only
    split
    · exact hcov
    · exact dfRunWith_covered reg d _ _ _ _ hcov
  · exact hcov

/-- The registered domain-fold pass (transform `dfRun`, `DomainFoldRuntime.lean`). -/
def denseDomainFoldPassV (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (fun _ _ d => dfRun pw d)
    (fun _ _ _ => [])
    (fun reg _ _ d hcov => dfRun_covered pw reg d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs _ d _ => dfRun_correct pw bs reg.isInput d)

end ApcOptimizer.Dense
