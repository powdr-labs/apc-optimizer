import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.ByteCheckPack

set_option autoImplicit false

/-! # Correctness of the `domainBatch` pass

The pass owes one obligation, `dbDomainBatchσ_entailed`: every `var := const` it emits holds in
every satisfying assignment. It is discharged in five layers.

1. **Representation.** The scan runs on `ZMod.val`s, so `dbEval` mirrors `DenseExpr.eval` through
   `ZMod.val` (`dbEval_eval`). Everything above works with field elements again.
2. **Domains.** Each entry of the table contains the value every satisfying assignment gives its
   variable (`DbTabSound`, established phase by phase).
3. **Items.** A gathered item's `dbItemOk` holds at such an assignment (`dbCompileBi_ok`).
4. **Scan.** Enumerating a box and intersecting the mask over survivors keeps, for every key still
   alive, exactly the value a satisfying assignment gives it (`dbScanLoop_reach`).
5. **Assembly.** The context is sound (`dbBuildCtx_good`), so each preflighted plan answers soundly
   (`dbPreflight_sound`) and the run's forced lists fold into an entailed solution map. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

universe u v

/-! ## 1. The `Nat` representation of the scan

The register file holds `ZMod.val`s. Addition is a conditional subtraction and multiplication a
single reduction, so each mirrors `ZMod.val_add` / `ZMod.val_mul`. -/

theorem dbAddN_eq_mod (p a b : ℕ) (ha : a < p) (hb : b < p) : dbAddN p a b = (a + b) % p := by
  unfold dbAddN
  by_cases h : a + b < p
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have hp : p ≤ a + b := Nat.le_of_not_lt h
    rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)]

theorem dbAddN_val [NeZero p] (a b : ZMod p) : dbAddN p a.val b.val = (a + b).val := by
  rw [dbAddN_eq_mod p a.val b.val (ZMod.val_lt a) (ZMod.val_lt b), ZMod.val_add]

theorem dbMulN_val [NeZero p] (a b : ZMod p) : dbMulN p a.val b.val = (a * b).val := by
  rw [dbMulN, ZMod.val_mul]

/-- The register file agrees with `denv` on every variable of interest. -/
def DbRegsAgree (denv : VarId → ZMod p) (regs : Array ℕ) (vs : List VarId) : Prop :=
  ∀ i ∈ vs, regs.getD i.index 0 = (denv i).val

theorem dbEval_eval [NeZero p] (denv : VarId → ZMod p) (regs : Array ℕ) :
    ∀ (e : DenseExpr p), DbRegsAgree denv regs e.vars →
      dbEval p regs e = (e.eval denv).val := by
  intro e
  induction e with
  | const c => intro _; rfl
  | var i => intro h; exact h i (by simp [DenseExpr.vars])
  | add a b iha ihb =>
    intro h
    have ha : DbRegsAgree denv regs a.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    have hb : DbRegsAgree denv regs b.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    simp only [dbEval, iha ha, ihb hb, DenseExpr.eval]
    exact dbAddN_val _ _
  | mul a b iha ihb =>
    intro h
    have ha : DbRegsAgree denv regs a.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    have hb : DbRegsAgree denv regs b.vars := fun i hi =>
      h i (by simp [DenseExpr.vars, hi])
    simp only [dbEval, iha ha, ihb hb, DenseExpr.eval]
    exact dbMulN_val _ _

/-- `dbEval` is zero exactly when the expression evaluates to zero. -/
theorem dbEval_zero [NeZero p] (denv : VarId → ZMod p) (regs : Array ℕ)
    (e : DenseExpr p) (h : DbRegsAgree denv regs e.vars) :
    (dbEval p regs e == 0) = decide (e.eval denv = 0) := by
  rw [dbEval_eval denv regs e h]
  by_cases hz : e.eval denv = 0
  · simp [hz]
  · simp [hz]

theorem dbGetD_lt {α : Type u} (vs : Array α) (k : ℕ) (dflt : α) (h : k < vs.size) :
    vs.getD k dflt = vs[k] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

theorem dbSetD_at {α : Type} (a : Array α) (k : ℕ) (v dflt : α) :
    (a.set! k v).getD k dflt = if k < a.size then v else dflt := by
  rw [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self]
  split <;> rfl

theorem dbGetD_replicate {α : Type} (n : ℕ) (x : α) (q : ℕ) (dflt : α) :
    (Array.replicate n x).getD q dflt = if q < n then x else dflt := by
  rw [Array.getD_eq_getD_getElem?]
  split
  · next h => rw [Array.getElem?_eq_getElem (by simpa using h), Array.getElem_replicate]; rfl
  · next h => rw [Array.getElem?_eq_none (by simpa using h)]; rfl

theorem zmodOfNatP_eq [NeZero p] (n : ℕ) : zmodOfNatP p n = (n : ZMod p) := by
  cases p with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ m =>
    refine ZMod.val_injective (m + 1) ?_
    rw [ZMod.val_natCast]
    rfl

theorem zmodOfNatP_val [NeZero p] (x : ZMod p) : zmodOfNatP p x.val = x := by
  rw [zmodOfNatP_eq, ZMod.natCast_val, ZMod.cast_id]

/-! ## 2a. Affine roots

The pass reads a constraint's affine form out of six `ZMod.val` slots: `st[1]` the constant,
`st[2+j]` the coefficient of `vs[j]`, `st[5]` a spill for a variable outside `vs` (which the caller
rules out) and `st[0]` a "still affine" flag. `dbAffOf` is the form those slots denote, and
`dbAffAcc_spec` says the walk adds `k · e` to it — so a state that survives with a single live
coefficient is an affine equation in one variable, whose root is the value every satisfying
assignment gives it. -/

theorem dbAddN_lt (p a b : ℕ) [NeZero p] (ha : a < p) (hb : b < p) : dbAddN p a b < p := by
  simp only [dbAddN]; split <;> omega

theorem dbMulN_lt (p a b : ℕ) [NeZero p] : dbMulN p a b < p :=
  Nat.mod_lt _ (Nat.pos_of_neZero p)

theorem dbAddN_cast [NeZero p] (a b : ℕ) (ha : a < p) (hb : b < p) :
    ((dbAddN p a b : ℕ) : ZMod p) = (a : ZMod p) + (b : ZMod p) := by
  rw [dbAddN_eq_mod p a b ha hb, ZMod.natCast_mod, Nat.cast_add]

theorem dbMulN_cast [NeZero p] (a b : ℕ) :
    ((dbMulN p a b : ℕ) : ZMod p) = (a : ZMod p) * (b : ZMod p) := by
  rw [dbMulN, ZMod.natCast_mod, Nat.cast_mul]

/-- A `ZMod.val` below `p` casts back to a nonzero element unless it is `0`. -/
theorem dbCast_ne_zero [NeZero p] (n : ℕ) (hn : n < p) (h0 : n ≠ 0) : (n : ZMod p) ≠ 0 := by
  intro hz
  have : (n : ZMod p).val = n := ZMod.val_natCast_of_lt hn
  rw [hz] at this
  exact h0 (by simpa using this.symm)

/-- One coefficient's contribution to the form. -/
def dbAffTerm (vs : Array VarId) (st : Array ℕ) (denv : VarId → ZMod p) (t : ℕ) : ZMod p :=
  (st.getD (2 + t) 0 : ZMod p) * denv (vs.getD t default)

/-- The affine form the six slots denote. Slots the walk never writes stay `0`, so summing all three
    coefficient slots is harmless. -/
def dbAffOf (vs : Array VarId) (st : Array ℕ) (denv : VarId → ZMod p) : ZMod p :=
  (st.getD 1 0 : ZMod p)
    + dbAffTerm vs st denv 0 + dbAffTerm vs st denv 1 + dbAffTerm vs st denv 2

/-- Every slot holds a `ZMod.val`. -/
def DbAffInv (p : ℕ) (st : Array ℕ) : Prop := st.size = 6 ∧ ∀ k, st.getD k 0 < p

theorem dbModify_getD (a : Array ℕ) (i j : ℕ) (f : ℕ → ℕ) (hi : i < a.size) :
    (a.modify i f).getD j 0 = if i = j then f (a.getD i 0) else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · next h => subst h; rw [Array.getElem?_eq_getElem hi]; rfl
  · rfl

theorem dbSetD_zero (st : Array ℕ) (hsz : 0 < st.size) : (st.set! 0 0).getD 0 0 = 0 := by
  rw [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self, if_pos hsz]
  rfl

theorem dbSetD_other (st : Array ℕ) (j : ℕ) (hj : j ≠ 0) :
    (st.set! 0 0).getD j 0 = st.getD j 0 := by
  rw [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hj),
    Array.getD_eq_getD_getElem?]

/-- The queried slot of a variable of `vs` names that variable. -/
theorem dbSlotOf_spec (vs : Array VarId) (i : VarId) :
    ∀ k, (∃ m, k ≤ m ∧ ∃ h : m < vs.size, vs[m] = i) →
      dbSlotOf vs i k < vs.size ∧ vs.getD (dbSlotOf vs i k) default = i := by
  intro k
  induction hn : vs.size - k generalizing k with
  | zero => intro ⟨m, hkm, hm, _⟩; omega
  | succ n ih =>
    intro hex
    have hk : k < vs.size := by omega
    rw [dbSlotOf, dif_pos hk]
    by_cases hveq : vs[k] == i
    · rw [if_pos hveq]
      exact ⟨hk, by rw [dbGetD_lt vs k default hk]; exact eq_of_beq hveq⟩
    · rw [if_neg hveq]
      refine ih (k + 1) (by omega) ?_
      obtain ⟨m, hkm, hm, hvm⟩ := hex
      refine ⟨m, ?_, hm, hvm⟩
      rcases Nat.eq_or_lt_of_le hkm with rfl | h
      · exact absurd (beq_iff_eq.mpr hvm) hveq
      · omega

theorem dbSlotOf_of_mem (vs : Array VarId) (i : VarId) (h : i ∈ vs) :
    dbSlotOf vs i 0 < vs.size ∧ vs.getD (dbSlotOf vs i 0) default = i := by
  obtain ⟨m, hm, hvm⟩ := Array.getElem_of_mem h
  exact dbSlotOf_spec vs i 0 ⟨m, Nat.zero_le _, hm, hvm⟩

theorem dbAffInv_modify [NeZero p] (st : Array ℕ) (hst : DbAffInv p st) (i : ℕ) (hi : i < st.size)
    (f : ℕ → ℕ) (hf : ∀ v, v < p → f v < p) : DbAffInv p (st.modify i f) := by
  obtain ⟨hsz, hlt⟩ := hst
  refine ⟨by simpa using hsz, fun j => ?_⟩
  rw [dbModify_getD st i j f hi]
  split
  · have h := hlt i
    rw [dbGetD_lt st i 0 hi] at h
    exact hf _ h
  · exact hlt j

/-- Writing into coefficient slot `s` adds `k · denv vs[s]` to the form. -/
theorem dbAffOf_modify [NeZero p] (vs : Array VarId) (st : Array ℕ) (denv : VarId → ZMod p)
    (s : ℕ) (hs : s < 3) (hidx : 2 + s < st.size) (k : ℕ)
    (hlt : st.getD (2 + s) 0 < p) (hk : k < p) :
    dbAffOf vs (st.modify (2 + s) (fun v => dbAddN p v k)) denv
      = dbAffOf vs st denv + (k : ZMod p) * denv (vs.getD s default) := by
  have hsame : dbAffTerm vs (st.modify (2 + s) (fun v => dbAddN p v k)) denv s
      = dbAffTerm vs st denv s + (k : ZMod p) * denv (vs.getD s default) := by
    rw [dbAffTerm, dbAffTerm, dbModify_getD st (2 + s) (2 + s) _ hidx,
      if_pos (rfl : 2 + s = 2 + s), dbAddN_cast _ _ hlt hk]
    ring
  have hoth : ∀ t, t ≠ s → dbAffTerm vs (st.modify (2 + s) (fun v => dbAddN p v k)) denv t
      = dbAffTerm vs st denv t := by
    intro t ht
    rw [dbAffTerm, dbAffTerm, dbModify_getD st (2 + s) (2 + t) _ hidx,
      if_neg (show ¬(2 + s = 2 + t) by omega)]
  have hc : (st.modify (2 + s) (fun v => dbAddN p v k)).getD 1 0 = st.getD 1 0 := by
    rw [dbModify_getD st (2 + s) 1 _ hidx, if_neg (show ¬(2 + s = 1) by omega)]
  rcases (show s = 0 ∨ s = 1 ∨ s = 2 from by omega) with h | h | h <;> subst h
  · rw [dbAffOf, dbAffOf, hc, hsame, hoth 1 (by omega), hoth 2 (by omega)]; ring
  · rw [dbAffOf, dbAffOf, hc, hsame, hoth 0 (by omega), hoth 2 (by omega)]; ring
  · rw [dbAffOf, dbAffOf, hc, hsame, hoth 0 (by omega), hoth 1 (by omega)]; ring

/-- Adding `k` to the coefficient slot of `i` adds `k · denv i` to the form. -/
theorem dbAffOf_var [NeZero p] (vs : Array VarId) (hvs : vs.size ≤ 3) (st : Array ℕ)
    (hst : DbAffInv p st) (i : VarId) (hi : i ∈ vs) (k : ℕ) (hk : k < p)
    (denv : VarId → ZMod p) :
    dbAffOf vs (st.modify (2 + dbSlotOf vs i 0) (fun v => dbAddN p v k)) denv
      = dbAffOf vs st denv + (k : ZMod p) * denv i := by
  obtain ⟨hsz, hlt⟩ := hst
  obtain ⟨hslt, hsv⟩ := dbSlotOf_of_mem vs i hi
  rw [dbAffOf_modify vs st denv _ (by omega) (by omega) k (hlt _) hk, hsv]

/-- The walk adds `k · e` to the form, provided the flag survives. -/
theorem dbAffAcc_spec [NeZero p] (vs : Array VarId) (hvs : vs.size ≤ 3)
    (denv : VarId → ZMod p) :
    ∀ (e : DenseExpr p) (k : ℕ) (st : Array ℕ), DbAffInv p st → k < p →
      (∀ v ∈ e.vars, v ∈ vs) →
      DbAffInv p (dbAffAcc vs e k st) ∧
      ((dbAffAcc vs e k st).getD 0 0 ≠ 0 →
        st.getD 0 0 ≠ 0 ∧
        dbAffOf vs (dbAffAcc vs e k st) denv
          = dbAffOf vs st denv + (k : ZMod p) * e.eval denv) := by
  have hcv : ∀ (c : ZMod p), ((c.val : ℕ) : ZMod p) = c := fun c => by
    rw [← zmodOfNatP_eq, zmodOfNatP_val]
  intro e
  induction e with
  | const c =>
    intro k st hst hk _
    obtain ⟨hsz, hlt⟩ := hst
    have h1 : (1 : ℕ) < st.size := by omega
    have hmod : ∀ j, (st.modify 1 (fun v => dbAddN p v (dbMulN p k c.val))).getD j 0
        = if 1 = j then dbAddN p (st.getD 1 0) (dbMulN p k c.val) else st.getD j 0 :=
      fun j => dbModify_getD st 1 j _ h1
    have hcast : ((dbAddN p (st.getD 1 0) (dbMulN p k c.val) : ℕ) : ZMod p)
        = (st.getD 1 0 : ZMod p) + (k : ZMod p) * c := by
      rw [dbAddN_cast _ _ (hlt 1) (dbMulN_lt p _ _), dbMulN_cast, hcv]
    have hinv : DbAffInv p (dbAffAcc vs (DenseExpr.const c) k st) := by
      rw [dbAffAcc]
      exact dbAffInv_modify (p := p) st ⟨hsz, hlt⟩ 1 h1 _
        (fun v hv => dbAddN_lt p v _ hv (dbMulN_lt p _ _))
    refine ⟨hinv, fun _ => ⟨?_, ?_⟩⟩
    · rw [dbAffAcc, hmod 0, if_neg (by omega)] at *; assumption
    · have hterm : ∀ t, dbAffTerm vs (st.modify 1 (fun v => dbAddN p v (dbMulN p k c.val))) denv t
          = dbAffTerm vs st denv t := by
        intro t
        rw [dbAffTerm, dbAffTerm, dbModify_getD st 1 (2 + t) _ h1,
          if_neg (show ¬(1 = 2 + t) by omega)]
      have hc1 : (st.modify 1 (fun v => dbAddN p v (dbMulN p k c.val))).getD 1 0
          = dbAddN p (st.getD 1 0) (dbMulN p k c.val) := by
        rw [dbModify_getD st 1 1 _ h1, if_pos (rfl : (1 : ℕ) = 1)]
      rw [dbAffAcc]
      simp only [dbAffOf, hterm, hc1, hcast, DenseExpr.eval]
      ring
  | var i =>
    intro k st hst hk hsub
    have hi : i ∈ vs := hsub i (by simp [DenseExpr.vars])
    obtain ⟨hsz, hlt⟩ := hst
    obtain ⟨hslt, _⟩ := dbSlotOf_of_mem vs i hi
    have hidx : 2 + dbSlotOf vs i 0 < st.size := by omega
    have hmod : ∀ j, (st.modify (2 + dbSlotOf vs i 0) (fun v => dbAddN p v k)).getD j 0
        = if 2 + dbSlotOf vs i 0 = j then dbAddN p (st.getD (2 + dbSlotOf vs i 0) 0) k
          else st.getD j 0 := fun j => dbModify_getD st _ j _ hidx
    have hinv : DbAffInv p (dbAffAcc vs (DenseExpr.var (p := p) i) k st) := by
      rw [dbAffAcc]
      exact dbAffInv_modify (p := p) st ⟨hsz, hlt⟩ _ hidx (fun v => dbAddN p v k)
        (fun v hv => dbAddN_lt p v k hv hk)
    refine ⟨hinv, fun _ => ⟨?_, ?_⟩⟩
    · rw [dbAffAcc, hmod 0, if_neg (by omega)] at *; assumption
    · rw [dbAffAcc, dbAffOf_var vs hvs st ⟨hsz, hlt⟩ i hi k hk denv, DenseExpr.eval]
  | add a b iha ihb =>
    intro k st hst hk hsub
    have hsa : ∀ v ∈ a.vars, v ∈ vs := fun v hv => hsub v (by simp [DenseExpr.vars, hv])
    have hsb : ∀ v ∈ b.vars, v ∈ vs := fun v hv => hsub v (by simp [DenseExpr.vars, hv])
    obtain ⟨hia, hea⟩ := iha k st hst hk hsa
    obtain ⟨hib, heb⟩ := ihb k (dbAffAcc vs a k st) hia hk hsb
    refine ⟨by rw [dbAffAcc]; exact hib, fun hflag => ?_⟩
    rw [dbAffAcc] at hflag
    obtain ⟨hf1, he1⟩ := heb hflag
    obtain ⟨hf0, he0⟩ := hea hf1
    refine ⟨hf0, ?_⟩
    rw [dbAffAcc, he1, he0, DenseExpr.eval]
    ring
  | mul a b iha ihb =>
    intro k st hst hk hsub
    have hsa : ∀ v ∈ a.vars, v ∈ vs := fun v hv => hsub v (by simp [DenseExpr.vars, hv])
    have hsb : ∀ v ∈ b.vars, v ∈ vs := fun v hv => hsub v (by simp [DenseExpr.vars, hv])
    obtain ⟨hsz, hlt⟩ := hst
    rw [dbAffAcc]
    rcases hca : a.constValue? with _ | ca
    · rcases hcb : b.constValue? with _ | cb
      · -- neither factor is constant: the form is abandoned
        refine ⟨⟨by simp [Array.set!, hsz], fun j => ?_⟩, fun hflag => ?_⟩
        · by_cases hj : j = 0
          · subst hj; rw [dbSetD_zero st (by omega)]; exact Nat.pos_of_neZero p
          · rw [dbSetD_other st j hj]; exact hlt _
        · exact absurd (dbSetD_zero st (by omega)) hflag
      · -- the right factor is constant
        obtain ⟨hia, hea⟩ := iha (dbMulN p k cb.val) st ⟨hsz, hlt⟩ (dbMulN_lt p _ _) hsa
        refine ⟨hia, fun hflag => ?_⟩
        obtain ⟨hf, he⟩ := hea hflag
        refine ⟨hf, ?_⟩
        rw [he, DenseExpr.eval, DenseExpr.constValue?_sound b cb hcb denv, dbMulN_cast, hcv]
        ring
    · -- the left factor is constant
      obtain ⟨hib, heb⟩ := ihb (dbMulN p k ca.val) st ⟨hsz, hlt⟩ (dbMulN_lt p _ _) hsb
      refine ⟨hib, fun hflag => ?_⟩
      obtain ⟨hf, he⟩ := heb hflag
      refine ⟨hf, ?_⟩
      rw [he, DenseExpr.eval, DenseExpr.constValue?_sound a ca hca denv, dbMulN_cast, hcv]
      ring

/-- The initial state denotes the zero form. -/
theorem dbAffInit [NeZero p] (hp : 1 < p) (vs : Array VarId) (denv : VarId → ZMod p) :
    DbAffInv p #[1, 0, 0, 0, 0, 0] ∧ dbAffOf vs (#[1, 0, 0, 0, 0, 0] : Array ℕ) denv = 0 := by
  refine ⟨⟨rfl, fun k => ?_⟩, by simp [dbAffOf, dbAffTerm]⟩
  match k with
  | 0 => simpa using hp
  | 1 | 2 | 3 | 4 | 5 => simpa using Nat.pos_of_neZero p
  | _ + 6 => simpa using Nat.pos_of_neZero p

/-- The roots of `c + a·x = 0` contain every `x` that solves it. -/
theorem dbAffRootsOf_sound [Fact p.Prime] [NeZero p] (an cn : ℕ) (han : an < p) (hcn : cn < p)
    (x : ZMod p) (hx : (cn : ZMod p) + (an : ZMod p) * x = 0)
    (roots : List (ZMod p)) (h : dbAffRootsOf p an cn = some roots) : x ∈ roots := by
  have hcv : ∀ n : ℕ, zmodOfNatP p n = (n : ZMod p) := fun n => zmodOfNatP_eq n
  rw [dbAffRootsOf] at h
  by_cases ha0 : an == 0
  · rw [if_pos ha0] at h
    have haz : ((an : ℕ) : ZMod p) = 0 := by rw [show an = 0 from by simpa using ha0]; simp
    rw [haz, zero_mul, add_zero] at hx
    by_cases hc0 : cn == 0
    · rw [if_pos hc0] at h; exact absurd h (by simp)
    · exact absurd hx (dbCast_ne_zero cn hcn (by simpa using hc0))
  · rw [if_neg ha0] at h
    have hane : ((an : ℕ) : ZMod p) ≠ 0 := dbCast_ne_zero an han (by simpa using ha0)
    simp only [hcv] at h
    by_cases h1 : zmodIsOne ((an : ℕ) : ZMod p)
    · rw [if_pos h1] at h
      rw [← Option.some.inj h]
      have hone : ((an : ℕ) : ZMod p) = 1 := by simpa using h1
      rw [hone, one_mul] at hx
      simp only [List.mem_singleton, zmodNegP_eq]
      linear_combination hx
    · rw [if_neg h1] at h
      by_cases hchk : zmodIsZero (zmodAddP (zmodMulP ((an : ℕ) : ZMod p)
          (zmodNegP (zmodMulP (((an : ℕ) : ZMod p))⁻¹ ((cn : ℕ) : ZMod p))))
          ((cn : ℕ) : ZMod p))
      · rw [if_pos hchk] at h
        rw [← Option.some.inj h]
        simp only [List.mem_singleton, zmodNegP_eq, zmodMulP_eq]
        have h2 : (an : ZMod p) * x = -(cn : ZMod p) := by linear_combination hx
        rw [show x = ((an : ZMod p))⁻¹ * ((an : ZMod p) * x) from
          (inv_mul_cancel_left₀ hane x).symm, h2]
        ring
      · rw [if_neg hchk] at h; exact absurd h (by simp)

/-- The roots `dbAffRoots` reports for `vs[j]` contain the value every satisfying assignment gives
    it: the surviving form is `c + a·vs[j]`, and it vanishes at that assignment. -/
theorem dbAffRoots_sound [Fact p.Prime] [NeZero p] (vs : Array VarId) (hvs : vs.size ≤ 3)
    (j : ℕ) (hj : j < vs.size) (e : DenseExpr p) (hsub : ∀ v ∈ e.vars, v ∈ vs)
    (roots : List (ZMod p)) (h : dbAffRoots vs j e = some roots)
    (denv : VarId → ZMod p) (he : e.eval denv = 0) : denv vs[j] ∈ roots := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨hinv0, hzero⟩ := dbAffInit (p := p) hp vs denv
  obtain ⟨hinv, hspec⟩ := dbAffAcc_spec vs hvs denv e 1 _ hinv0 hp hsub
  set st := dbAffAcc vs e 1 (#[1, 0, 0, 0, 0, 0] : Array ℕ) with hst
  rw [dbAffRoots] at h
  by_cases hgate : st.getD 0 0 == 0 || dbOtherLive st j
  · rw [if_pos hgate] at h; exact absurd h (by simp)
  rw [if_neg hgate] at h
  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hgate
  obtain ⟨hflag, hoth⟩ := hgate
  obtain ⟨_, hform⟩ := hspec hflag
  rw [hzero, he] at hform
  simp only [Nat.cast_one, mul_zero, zero_add] at hform
  obtain ⟨hsz, hlt⟩ := hinv
  have hdead : ∀ k, k < 3 → k ≠ j → st.getD (2 + k) 0 = 0 := by
    intro k hk hkj
    simp only [dbOtherLive, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      not_or] at hoth
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, _⟩ := hoth
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with h' | h' | h' <;> subst h'
    · by_contra hc; exact h0 ⟨by omega, hc⟩
    · by_contra hc; exact h1 ⟨by omega, hc⟩
    · by_contra hc; exact h2 ⟨by omega, hc⟩
  have hjv : vs.getD j default = vs[j] := dbGetD_lt vs j default hj
  have hj3 : j < 3 := by omega
  have hcol : dbAffOf vs st denv
      = (st.getD 1 0 : ZMod p) + (st.getD (2 + j) 0 : ZMod p) * denv vs[j] := by
    rw [← hjv]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 from by omega) with h' | h' | h' <;> subst h'
    · simp only [dbAffOf, dbAffTerm, hdead 1 (by omega) (by omega),
        hdead 2 (by omega) (by omega)]; push_cast; ring
    · simp only [dbAffOf, dbAffTerm, hdead 0 (by omega) (by omega),
        hdead 2 (by omega) (by omega)]; push_cast; ring
    · simp only [dbAffOf, dbAffTerm, hdead 0 (by omega) (by omega),
        hdead 1 (by omega) (by omega)]; push_cast; ring
  rw [hcol] at hform
  exact dbAffRootsOf_sound _ _ (hlt _) (hlt 1) _ hform roots h

/-- `denseRootsIn`'s union over the product spine, over the accumulator. -/
theorem dbRootsAt_sound [Fact p.Prime] [NeZero p] (vs : Array VarId) (hvs : vs.size ≤ 3)
    (j : ℕ) (hj : j < vs.size) :
    ∀ (e : DenseExpr p), (∀ v ∈ e.vars, v ∈ vs) → ∀ (roots : List (ZMod p)),
      dbRootsAt vs j e = some roots → ∀ (denv : VarId → ZMod p), e.eval denv = 0 →
        denv vs[j] ∈ roots := by
  intro e
  induction e with
  | const c => intro hsub roots h denv he; exact dbAffRoots_sound vs hvs j hj _ hsub _ h denv he
  | var i => intro hsub roots h denv he; exact dbAffRoots_sound vs hvs j hj _ hsub _ h denv he
  | add a b _ _ => intro hsub roots h denv he
                   exact dbAffRoots_sound vs hvs j hj _ hsub _ h denv he
  | mul a b iha ihb =>
    intro hsub roots h denv he
    have hsa : ∀ v ∈ a.vars, v ∈ vs := fun v hv => hsub v (by simp [DenseExpr.vars, hv])
    have hsb : ∀ v ∈ b.vars, v ∈ vs := fun v hv => hsub v (by simp [DenseExpr.vars, hv])
    rw [dbRootsAt] at h
    split at h
    · next r haff =>
      rw [show roots = r from (Option.some.inj h).symm]
      exact dbAffRoots_sound vs hvs j hj _ hsub r haff denv he
    · split at h
      · next ra rb hra hrb =>
        rw [show roots = ra ++ rb from (Option.some.inj h).symm]
        have he' : a.eval denv * b.eval denv = 0 := he
        rcases mul_eq_zero.mp he' with hz | hz
        · exact List.mem_append.2 (Or.inl (iha hsa ra hra denv hz))
        · exact List.mem_append.2 (Or.inr (ihb hsb rb hrb denv hz))
      all_goals exact absurd h (by simp)

/-! ## 2b. Domain membership

A domain is never materialized, so membership is "some in-range index yields the value". This is the
form the scan needs: the enumeration reaches a value exactly when it has an index. -/

/-- `v` is the `k`-th element of `dm`, for some in-range `k`. -/
def DbDomMem (p : ℕ) (dm : DbDom) (v : ℕ) : Prop := ∃ k, k < dm.size ∧ DbDom.at p dm k = v

theorem dbDomMem_explicit (vs : Array ℕ) (v : ℕ) (h : v ∈ vs) : DbDomMem p (.explicit vs) v := by
  obtain ⟨k, hk, hv⟩ := Array.getElem_of_mem h
  refine ⟨k, hk, ?_⟩
  simp only [DbDom.at]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some, hv]

theorem dbDomMem_range [NeZero p] (bound v : ℕ) (hvp : v < p) (h : v < bound) :
    DbDomMem p (.range bound) v :=
  ⟨v, h, by simp only [DbDom.at, if_pos hvp]⟩

/-! ## 2c. Soundness of the table

`DbTabSound` is the invariant every insertion preserves: an entry's domain contains the value the
assignment gives its variable. `DbTab.insert` keeps whichever of the two domains is smaller, so it
preserves the invariant as long as the incoming domain is itself sound. -/

def DbTabSound (p : ℕ) (denv : VarId → ZMod p) (T : DbTab p) : Prop :=
  ∀ i dm, T.get i = some dm → DbDomMem p dm (denv ⟨i⟩).val

theorem dbTab_get_replicate (n i : ℕ) : (⟨Array.replicate n none⟩ : DbTab p).get i = none := by
  rw [DbTab.get, Array.getD_eq_getD_getElem?]
  rcases lt_or_ge i n with hi | hi
  · rw [Array.getElem?_eq_getElem (by simpa using hi), Array.getElem_replicate]; rfl
  · rw [Array.getElem?_eq_none (by simpa using hi)]; rfl

/-- An entry surviving an insertion is either the incoming domain, at the incoming index, or one the
    table already held. -/
theorem dbTab_get_insert_cases (T : DbTab p) (i j : ℕ) (dm dj : DbDom)
    (h : (T.insert i dm).get j = some dj) : (j = i ∧ dj = dm) ∨ T.get j = some dj := by
  rcases T with ⟨dom⟩
  have hset : ∀ w : Option DbDom, (⟨dom.set! i w⟩ : DbTab p).get j = some dj →
      (j = i ∧ some dj = w) ∨ (⟨dom⟩ : DbTab p).get j = some dj := by
    intro w hw
    rw [DbTab.get, Array.getD_eq_getD_getElem?] at hw
    rcases lt_or_ge j (dom.set! i w).size with hlt | hge
    · by_cases hji : j = i
      · subst hji
        rw [Array.set!, Array.getElem?_setIfInBounds_self,
          if_pos (by simpa using hlt)] at hw
        exact Or.inl ⟨rfl, hw.symm⟩
      · rw [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hji)] at hw
        exact Or.inr (by rw [DbTab.get, Array.getD_eq_getD_getElem?, hw])
    · rw [Array.getElem?_eq_none hge] at hw; exact absurd hw (by simp)
  rw [DbTab.insert] at h
  rcases hold : dom.getD i none with _ | d0
  · rw [hold] at h
    dsimp only at h
    rcases hset _ h with ⟨hji, hdj⟩ | hr
    · exact Or.inl ⟨hji, Option.some.inj hdj⟩
    · exact Or.inr hr
  · rw [hold] at h
    dsimp only at h
    by_cases hsm : dm.size < d0.size
    · rw [if_pos hsm] at h
      rcases hset _ h with ⟨hji, hdj⟩ | hr
      · exact Or.inl ⟨hji, Option.some.inj hdj⟩
      · exact Or.inr hr
    · rw [if_neg hsm] at h; exact Or.inr h

theorem dbTabSound_empty (denv : VarId → ZMod p) (n : ℕ) :
    DbTabSound p denv ⟨Array.replicate n none⟩ := by
  intro i dm h
  rw [dbTab_get_replicate] at h
  exact absurd h (by simp)

theorem dbTabSound_insert (denv : VarId → ZMod p) (T : DbTab p) (i : ℕ) (dm : DbDom)
    (hT : DbTabSound p denv T) (hdm : DbDomMem p dm (denv ⟨i⟩).val) :
    DbTabSound p denv (T.insert i dm) := by
  intro j dj hj
  rcases dbTab_get_insert_cases T i j dm dj hj with ⟨hji, hdj⟩ | hr
  · subst hji; subst hdj; exact hdm
  · exact hT j dj hr

/-- Bus slot bounds: the fact's own soundness, specialised to the constant multiplicity and the
    constant-slot pattern the engine precomputes. -/
theorem dbSlotBound_sound {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (slot bound : ℕ) (i : VarId)
    (hslot : bi.payload[slot]? = some (.var i))
    (h : dbSlotBound facts bi bi.multiplicity.constValue?
      (bi.payload.map DenseExpr.constValue?) slot = some bound)
    (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    (denv i).val < bound := by
  rw [dbSlotBound.eq_def] at h
  rcases hm : bi.multiplicity.constValue? with _ | mval
  · rw [hm] at h; exact absurd h (by simp)
  · rw [hm] at h
    dsimp only at h
    by_cases hmz : zmodIsZero mval
    · rw [if_pos hmz] at h; exact absurd h (by simp)
    · rw [if_neg hmz] at h
      have hmeval : (denseBIEval bi denv).multiplicity = mval :=
        bi.multiplicity.constValue?_sound mval hm denv
      have hmne : mval ≠ 0 := by
        simpa [zmodIsZero_eq] using hmz
      have hviol : bs.accepts (denseBIEval bi denv) := hob (by rw [hmeval]; exact hmne)
      have hget : (denseBIEval bi denv).payload[slot]? = some (denv i) := by
        show (bi.payload.map (fun e => e.eval denv))[slot]? = some (denv i)
        rw [List.getElem?_map, hslot]; rfl
      rw [← hmeval] at h
      exact facts.slotBound_sound (denseBIEval bi denv)
        (bi.payload.map DenseExpr.constValue?) slot bound (denv i) h
        (denseMatches_evalPattern bi.payload denv) hviol hget

/-! ### Byte-operand domains

A byte operand's domain is the `bound`-element coset `{(v + negB) * aInv}`, streamed rather than
materialized, with `negB` and `aInv` stored as `val`s. -/

theorem dbDom_at_coset [NeZero p] (bound negB aInv k : ℕ) :
    DbDom.at p (.coset bound negB aInv) k = dbMulN p (dbAddN p (k % p) negB) aInv := by
  simp only [DbDom.at]
  by_cases hk : k < p
  · rw [if_pos hk, Nat.mod_eq_of_lt hk]
  · rw [if_neg hk]

theorem dbDomMem_coset [NeZero p] (bound : ℕ) (b ainv : ZMod p) (v : ZMod p) (k : ℕ)
    (hk : k < bound) (hv : v = ((k : ZMod p) - b) * ainv) :
    DbDomMem p (.coset bound (zmodNegP b).val ainv.val) v.val := by
  refine ⟨k, hk, ?_⟩
  rw [dbDom_at_coset, ← ZMod.val_natCast (n := p) k, dbAddN_val, dbMulN_val, hv,
    zmodNegP_eq, sub_eq_add_neg]

/-- `denseByteOperandCosetMem` as an index into the coset. -/
theorem dbByteOperand_cosetIndex [Fact p.Prime] [NeZero p] (e : DenseExpr p) (bound : ℕ)
    (x : VarId) (a b : ZMod p) (haff : denseAffineOfExpr e = some (x, a, b))
    (denv : VarId → ZMod p) (hbnd : (e.eval denv).val < bound) :
    ∃ k, k < bound ∧ denv x = ((k : ZMod p) - b) * a⁻¹ := by
  have hmem := denseByteOperandCosetMem e bound x a b haff denv hbnd
  rw [List.map_map, List.mem_map] at hmem
  obtain ⟨k, hk, hveq⟩ := hmem
  exact ⟨k, List.mem_range.mp hk, hveq.symm⟩

/-- An operand domain contains the value a satisfying assignment gives its variable, given the
    operand is below the byte bound. -/
theorem dbByteOperand_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (e : DenseExpr p) (bound i : ℕ) (dm : DbDom)
    (h : dbByteOperand e bound = some (i, dm))
    (hbnd : (e.eval denv).val < bound) : DbDomMem p dm (denv ⟨i⟩).val := by
  unfold dbByteOperand at h
  cases e with
  | var j =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact dbDomMem_range bound _ (ZMod.val_lt _) hbnd
  | const c =>
    rcases haff : denseAffineOfExpr (.const c : DenseExpr p) with _ | ⟨x, a, b⟩
    · rw [haff] at h; exact absurd h (by simp)
    · rw [haff] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k, hk, hveq⟩ := dbByteOperand_cosetIndex (.const c) bound x a b haff denv hbnd
      exact dbDomMem_coset bound b a⁻¹ (denv x) k hk hveq
  | add ea eb =>
    rcases haff : denseAffineOfExpr (.add ea eb) with _ | ⟨x, a, b⟩
    · rw [haff] at h; exact absurd h (by simp)
    · rw [haff] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k, hk, hveq⟩ := dbByteOperand_cosetIndex (.add ea eb) bound x a b haff denv hbnd
      exact dbDomMem_coset bound b a⁻¹ (denv x) k hk hveq
  | mul ea eb =>
    rcases haff : denseAffineOfExpr (.mul ea eb) with _ | ⟨x, a, b⟩
    · rw [haff] at h; exact absurd h (by simp)
    · rw [haff] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨k, hk, hveq⟩ := dbByteOperand_cosetIndex (.mul ea eb) bound x a b haff denv hbnd
      exact dbDomMem_coset bound b a⁻¹ (denv x) k hk hveq

/-! ### The `busId`-keyed fact cache -/

/-- The cache answers the bus-only facts it stands for, at one bus id. -/
structure DbBusCacheOk {p : ℕ} {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (b : ℕ) : Prop where
  usable : bc.usable.getD b false = !bs.isStateful b
  varRange : bc.varRange.getD b false = facts.varRangeBus b
  tuple : bc.tuple.getD b none = facts.tupleRangeBus b
  byteSpec : bc.byteSpec.getD b none = facts.byteXorSpec b
  alwaysOk0 : bc.alwaysOk0.getD b false = facts.neverViolates b
  neverViol : bc.neverViol.getD b false = facts.neverViolates b

theorem dbGetD_rangeMap {β : Type u} (nb : ℕ) (f : ℕ → β) (b : ℕ) (hb : b < nb) (dflt : β) :
    ((Array.range nb).map f).getD b dflt = f b := by
  rw [dbGetD_lt _ _ _ (by simpa using hb), Array.getElem_map, Array.getElem_range]

theorem dbBusCacheOf_ok {bs : BusSemantics p} (facts : BusFacts p bs) (nb b : ℕ) (hb : b < nb) :
    DbBusCacheOk facts (dbBusCacheOf facts nb) b :=
  ⟨dbGetD_rangeMap nb _ b hb false, dbGetD_rangeMap nb _ b hb false,
    dbGetD_rangeMap nb _ b hb none, dbGetD_rangeMap nb _ b hb none,
    dbGetD_rangeMap nb _ b hb false, dbGetD_rangeMap nb _ b hb false⟩

/-! ### Linking a precomputed view to its interaction

`DbBiPre` caches the `BusFacts` answers for one interaction; these say the cache is faithful. -/

def DbBytePreOf {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (b : DbBytePre p) : Prop :=
  facts.byteXorSpec bi.busId = some b.spec ∧
    ∃ op, b.spec.decode bi.payload = some (op, b.o1, b.o2, b.result) ∧ b.op? = op.constValue?

def DbBiPreOf {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) : Prop :=
  e.mult? = bi.multiplicity.constValue? ∧ e.pat = bi.payload.map DenseExpr.constValue? ∧
    (∀ b, e.byte? = some b → DbBytePreOf facts bi b) ∧
    (e.varRange = true → facts.varRangeBus bi.busId = true) ∧
    (∀ t, e.tuple? = some t → facts.tupleRangeBus bi.busId = some t) ∧
    (∀ t, e.rangeAt? = some t → facts.rangeCheckAt bi.busId e.pat = some t)

theorem dbAddByteOperand_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (e : DenseExpr p) (bound : ℕ) (T : DbTab p) (hT : DbTabSound p denv T)
    (hbnd : (e.eval denv).val < bound) : DbTabSound p denv (dbAddByteOperand e bound T) := by
  unfold dbAddByteOperand
  rcases hv : dbByteOperandVar e with _ | i
  · exact hT
  · dsimp only
    rcases hg : T.get i with _ | d0
    · exact hT
    · dsimp only
      by_cases hlt : bound < d0.size
      · rw [if_pos hlt]
        rcases hbo : dbByteOperand e bound with _ | ⟨i', dm⟩
        · exact hT
        · dsimp only
          exact dbTabSound_insert denv T i' dm hT
            (dbByteOperand_sound denv e bound i' dm hbo hbnd)
      · rw [if_neg hlt]; exact hT

theorem dbAddByteBi_sound [Fact p.Prime] [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (T : DbTab p) (hT : DbTabSound p denv T) : DbTabSound p denv (dbAddByteBi e T) := by
  obtain ⟨hmult, _, hbyte, _, _, _⟩ := hpre
  rw [dbAddByteBi]
  rcases hm : e.mult? with _ | mult
  · exact hT
  · dsimp only
    by_cases hmz : zmodIsZero mult
    · rw [if_pos hmz]; exact hT
    · rw [if_neg hmz]
      rcases hb : e.byte? with _ | b
      · exact hT
      · dsimp only
        rcases hop : b.op? with _ | opv
        · exact hT
        · dsimp only
          by_cases hbnds : denseByteOpBounds b.spec opv
          · rw [if_pos hbnds]
            obtain ⟨hspec, op, hdec, hopc⟩ := hbyte b hb
            have hmz' : mult ≠ 0 := by simpa [zmodIsZero_eq] using hmz
            obtain ⟨h1, h2⟩ := denseByteOperandBound bs facts bi denv mult
              (by rw [← hmult, hm]) hmz' b.spec hspec op b.o1 b.o2 b.result hdec opv
              (by rw [← hopc, hop]) hbnds hob
            exact dbAddByteOperand_sound denv b.o2 b.spec.bound _
              (dbAddByteOperand_sound denv b.o1 b.spec.bound T hT h1) h2
          · rw [if_neg hbnds]; exact hT

theorem dbBytePhase_sound [Fact p.Prime] [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (pre : Array (DbBiPre p))
    (hpre : ∀ k, ∀ hk : k < pre.size, ∃ bi, DbBiPreOf facts bi pre[k] ∧
      ((denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))) :
    ∀ (k : ℕ) (T : DbTab p), DbTabSound p denv T →
      DbTabSound p denv (dbBytePhase pre k T) := by
  intro k
  induction hk : pre.size - k generalizing k with
  | zero => intro T hT; rw [dbBytePhase, dif_neg (by omega)]; exact hT
  | succ n ih =>
    intro T hT
    have hlt : k < pre.size := by omega
    rw [dbBytePhase, dif_pos hlt]
    obtain ⟨bi, hbi, hob⟩ := hpre k hlt
    exact ih (k + 1) (by omega) _ (dbAddByteBi_sound facts bi pre[k] hbi denv hob T hT)

/-! ## 3. Items

A gathered item's obligation holds at a satisfying assignment. Only this direction is needed: the
mask is an intersection over *survivors*, so it suffices that the assignment's own point survives. -/

/-- Agreement on a bus interaction's variables restricts to each of its expressions. -/
theorem dbRegsAgree_mult (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (h : DbRegsAgree denv regs (denseBIVars bi)) :
    DbRegsAgree denv regs bi.multiplicity.vars := fun i hi =>
  h i (by rw [denseBIVars]; exact List.mem_append_left _ hi)

theorem dbRegsAgree_payload (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (h : DbRegsAgree denv regs (denseBIVars bi))
    (x : DenseExpr p) (hx : x ∈ bi.payload) : DbRegsAgree denv regs x.vars := fun i hi =>
  h i (by
    rw [denseBIVars]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hi⟩))

/-- The evaluated message of `bi`, spelled out. -/
theorem denseBIEval_mk (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) :
    denseBIEval bi denv =
      { busId := bi.busId, multiplicity := bi.multiplicity.eval denv,
        payload := bi.payload.map (fun e => e.eval denv) } := rfl

section Items
variable {bs : BusSemantics p}

/-- The evaluated payload of the fallback message is the interaction's own evaluated payload. -/
theorem dbFallback_payload [NeZero p] (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (hagree : DbRegsAgree denv regs (denseBIVars bi)) :
    bi.payload.map (fun t => zmodOfNatP p (dbEval p regs t))
      = bi.payload.map (fun ex => ex.eval denv) := by
  refine List.map_congr_left ?_
  intro x hx
  rw [dbEval_eval denv regs x (dbRegsAgree_payload denv regs bi hagree x hx),
    zmodOfNatP_val]

theorem dbFallback_ok [NeZero p] (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    dbItemOk facts regs
      (.fallback bi.busId bi.multiplicity bi.payload) = true := by
  have hmv : dbEval p regs (bi.multiplicity) = (bi.multiplicity.eval denv).val :=
    dbEval_eval denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
  simp only [dbItemOk]
  by_cases hz : dbEval p regs (bi.multiplicity) = 0
  · simp [hz]
  · have hne : bi.multiplicity.eval denv ≠ 0 := by
      intro h0; exact hz (by rw [hmv, h0, ZMod.val_zero])
    have hmsg : (⟨bi.busId, zmodOfNatP p (dbEval p regs (bi.multiplicity)),
        bi.payload.map (fun t => zmodOfNatP p (dbEval p regs t))⟩ :
          BusInteraction (ZMod p)) = denseBIEval bi denv := by
      rw [denseBIEval_mk, hmv, zmodOfNatP_val, dbFallback_payload denv regs bi hagree]
    simp only [beq_iff_eq, hz, if_false]
    rw [hmsg]
    exact (facts.acceptsDec_iff _).mpr (hob (by rw [denseBIEval_mk]; exact hne))

theorem dbCompileRange_ok [Fact p.Prime] [NeZero p] (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (item : DbItem p) (h : dbCompileRange bi e bi.multiplicity = some item) :
    dbItemOk facts regs item = true := by
  obtain ⟨hmult?, hpat, _, _, _, hra⟩ := hpre
  rw [dbCompileRange] at h
  rcases hm : e.mult? with _ | m
  · rw [hm] at h; exact absurd h (by simp)
  · rw [hm] at h
    dsimp only at h
    by_cases hone : zmodIsOne m
    · rw [if_pos hone] at h
      rcases hr : e.rangeAt? with _ | ⟨slot, bound⟩
      · rw [hr] at h; exact absurd h (by simp)
      · rw [hr] at h
        dsimp only at h
        rcases hv : bi.payload[slot]? with _ | value
        · rw [hv] at h; exact absurd h (by simp)
        · rw [hv] at h
          simp only [Option.some.injEq] at h
          subst h
          have hm1 : m = 1 := by simpa [zmodIsOne_eq] using hone
          have hmc : bi.multiplicity.constValue? = some 1 := by rw [← hmult?, hm, hm1]
          have hmeval : bi.multiplicity.eval denv = 1 :=
            bi.multiplicity.constValue?_sound 1 hmc denv
          have hvmem : value ∈ bi.payload := List.mem_of_getElem? hv
          have hvv : dbEval p regs (value) = (value.eval denv).val :=
            dbEval_eval denv regs value (dbRegsAgree_payload denv regs bi hagree value hvmem)
          have hmv : dbEval p regs (bi.multiplicity) = (bi.multiplicity.eval denv).val :=
            dbEval_eval denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
          obtain ⟨_, hrc⟩ := facts.rangeCheckAt_sound bi.busId
            (bi.payload.map DenseExpr.constValue?) slot bound (by rw [← hpat]; exact hra _ hr)
          obtain ⟨_, hiff⟩ := hrc (denseBIEval bi denv) rfl (by rw [denseBIEval_mk]; exact hmeval)
            (denseMatches_evalPattern bi.payload denv)
          have hpl : (denseBIEval bi denv).payload[slot]? = some (value.eval denv) := by
            show (bi.payload.map (fun x => x.eval denv))[slot]? = _
            rw [List.getElem?_map, hv]; rfl
          have hacc : bs.accepts (denseBIEval bi denv) := by
            refine hob ?_
            rw [denseBIEval_mk, hmeval]; exact one_ne_zero
          simp only [dbItemOk, hvv, hmv, hmeval]
          by_cases hz : (1 : ZMod p).val = 0
          · simp [hz]
          · simp only [beq_iff_eq, hz, if_false, decide_eq_true_eq]
            exact (hiff (value.eval denv) hpl).mp hacc
    · rw [if_neg hone] at h; exact absurd h (by simp)

/-- The byte arm: bounds and the bitwise relation come from the spec's own soundness. -/
theorem dbByteItem_ok [NeZero p] (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (o1 o2 r : DenseExpr p) (h1m : o1 ∈ bi.payload) (h2m : o2 ∈ bi.payload)
    (hrm : r ∈ bi.payload) (bound : ℕ) (kind : DenseBytePredKind)
    (hrel : bs.accepts (denseBIEval bi denv) →
      (o1.eval denv).val < bound ∧ (o2.eval denv).val < bound ∧
        dbByteRel kind (o1.eval denv).val (o2.eval denv).val (r.eval denv).val = true) :
    dbItemOk facts regs (.byte bi.multiplicity o1 o2 r bound kind) = true := by
  have hmv : dbEval p regs (bi.multiplicity) = (bi.multiplicity.eval denv).val :=
    dbEval_eval denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
  have e1 : dbEval p regs (o1) = (o1.eval denv).val :=
    dbEval_eval denv regs o1 (dbRegsAgree_payload denv regs bi hagree o1 h1m)
  have e2 : dbEval p regs (o2) = (o2.eval denv).val :=
    dbEval_eval denv regs o2 (dbRegsAgree_payload denv regs bi hagree o2 h2m)
  have er : dbEval p regs (r) = (r.eval denv).val :=
    dbEval_eval denv regs r (dbRegsAgree_payload denv regs bi hagree r hrm)
  simp only [dbItemOk, hmv, e1, e2, er]
  by_cases hz : (bi.multiplicity.eval denv).val = 0
  · simp [hz]
  · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
    obtain ⟨hb1, hb2, hrl⟩ := hrel (hob (by rw [denseBIEval_mk]; exact hne))
    simp [hz, hb1, hb2, hrl]

theorem dbCompileByte_ok [NeZero p] (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (e : DbBiPre p) (hpre : DbBiPreOf facts bi e) (denv : VarId → ZMod p) (regs : Array ℕ)
    (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv))
    (item : DbItem p) (h : dbCompileByte e bi.multiplicity = some item) :
    dbItemOk facts regs item = true := by
  obtain ⟨_, _, hbyte, _, _, _⟩ := hpre
  rw [dbCompileByte] at h
  rcases hb : e.byte? with _ | b
  · rw [hb] at h; exact absurd h (by simp)
  · rw [hb] at h
    dsimp only at h
    rcases hop : b.op? with _ | opv
    · rw [hop] at h; exact absurd h (by simp)
    · rw [hop] at h
      dsimp only at h
      obtain ⟨hspec, op, hdec, hopc⟩ := hbyte b hb
      obtain ⟨h1m, h2m, hrm⟩ := b.spec.decode_mem bi.payload op b.o1 b.o2 b.result hdec
      have hopeval : op.eval denv = opv := op.constValue?_sound opv (by rw [← hopc, hop]) denv
      obtain ⟨hxor, hpair⟩ :=
        denseByteXorSpec_decode_iff bs facts b.spec bi hspec op b.o1 b.o2 b.result hdec denv
      obtain ⟨hor, hand⟩ :=
        denseByteBoolSound_decode_iff bs facts b.spec bi hspec op b.o1 b.o2 b.result hdec denv
      have mk : ∀ kind, (bs.accepts (denseBIEval bi denv) →
          (b.o1.eval denv).val < b.spec.bound ∧ (b.o2.eval denv).val < b.spec.bound ∧
            dbByteRel kind (b.o1.eval denv).val (b.o2.eval denv).val
              (b.result.eval denv).val = true) →
          dbItemOk facts regs (.byte bi.multiplicity b.o1 b.o2 b.result b.spec.bound kind) = true :=
        fun kind hrel => dbByteItem_ok facts bi denv regs hagree hob b.o1 b.o2 b.result
          h1m h2m hrm b.spec.bound kind hrel
      by_cases hxo : opv = b.spec.xorOp
      · rw [if_pos hxo] at h
        simp only [Option.some.injEq] at h; subst h
        refine mk .xor (fun hacc => ?_)
        obtain ⟨u1, u2, u3⟩ := (hxor (by rw [hopeval, hxo])).mp hacc
        exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
      · rw [if_neg hxo] at h
        by_cases hpo : opv = b.spec.pairOp
        · rw [if_pos hpo] at h
          simp only [Option.some.injEq] at h; subst h
          refine mk .pair (fun hacc => ?_)
          obtain ⟨u1, u2, u3⟩ := (hpair (by rw [hopeval, hpo])).mp hacc
          exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
        · rw [if_neg hpo] at h
          rcases hoo : b.spec.orOp with _ | oop
          · rw [hoo] at h
            dsimp only at h
            rcases hao : b.spec.andOp with _ | aop
            · rw [hao] at h; exact absurd h (by simp)
            · rw [hao] at h
              dsimp only at h
              by_cases hae : opv = aop
              · rw [if_pos hae] at h
                simp only [Option.some.injEq] at h; subst h
                refine mk .and (fun hacc => ?_)
                obtain ⟨u1, u2, u3⟩ := (hand aop hao (by rw [hopeval, hae])).mp hacc
                exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
              · rw [if_neg hae] at h; exact absurd h (by simp)
          · rw [hoo] at h
            dsimp only at h
            by_cases hoe : opv = oop
            · rw [if_pos hoe] at h
              simp only [Option.some.injEq] at h; subst h
              refine mk .or (fun hacc => ?_)
              obtain ⟨u1, u2, u3⟩ := (hor oop hoo (by rw [hopeval, hoe])).mp hacc
              exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
            · rw [if_neg hoe] at h
              rcases hao : b.spec.andOp with _ | aop
              · rw [hao] at h; exact absurd h (by simp)
              · rw [hao] at h
                dsimp only at h
                by_cases hae : opv = aop
                · rw [if_pos hae] at h
                  simp only [Option.some.injEq] at h; subst h
                  refine mk .and (fun hacc => ?_)
                  obtain ⟨u1, u2, u3⟩ := (hand aop hao (by rw [hopeval, hae])).mp hacc
                  exact ⟨u1, u2, by simp [dbByteRel, u3]⟩
                · rw [if_neg hae] at h; exact absurd h (by simp)

theorem dbCompileOther_ok [Fact p.Prime] [NeZero p] (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    dbItemOk facts regs (dbCompileOther bi e bi.multiplicity) = true := by
  rw [dbCompileOther]
  rcases hr : dbCompileRange bi e bi.multiplicity with _ | item
  · dsimp only
    rcases hb : dbCompileByte e bi.multiplicity with _ | item2
    · exact dbFallback_ok facts bi denv regs hagree hob
    · exact dbCompileByte_ok facts bi e hpre denv regs hagree hob item2 hb
  · exact dbCompileRange_ok facts bi e hpre denv regs hagree hob item hr

theorem dbCompileBi_ok [Fact p.Prime] [NeZero p] (facts : BusFacts p bs) (bc : DbBusCache p)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (hpre : DbBiPreOf facts bi e)
    (denv : VarId → ZMod p) (regs : Array ℕ) (hagree : DbRegsAgree denv regs (denseBIVars bi))
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    dbItemOk facts regs (dbCompileBi facts bc bi e) = true := by
  obtain ⟨_, _, _, hvrf, htuf, _⟩ := hpre
  have hmv : dbEval p regs (bi.multiplicity) = (bi.multiplicity.eval denv).val :=
    dbEval_eval denv regs bi.multiplicity (dbRegsAgree_mult denv regs bi hagree)
  rw [dbCompileBi]
  by_cases hok : dbBiAlwaysOk facts bc bi
  · rw [if_pos hok]; rfl
  · rw [if_neg hok]
    dsimp only
    split
    · next x width heq =>
      have hx : x ∈ bi.payload := by rw [heq]; simp
      have hw : width ∈ bi.payload := by rw [heq]; simp
      have ex : dbEval p regs (x) = (x.eval denv).val :=
        dbEval_eval denv regs x (dbRegsAgree_payload denv regs bi hagree x hx)
      have ew : dbEval p regs (width) = (width.eval denv).val :=
        dbEval_eval denv regs width (dbRegsAgree_payload denv regs bi hagree width hw)
      have hmsg : denseBIEval bi denv =
          ⟨bi.busId, bi.multiplicity.eval denv, [x.eval denv, width.eval denv]⟩ := by
        rw [denseBIEval_mk, heq]; rfl
      by_cases hvr : e.varRange
      · rw [if_pos hvr]
        obtain ⟨_, hiff⟩ := facts.varRangeBus_sound bi.busId (hvrf hvr)
        have hkey : bi.multiplicity.eval denv ≠ 0 →
            (width.eval denv).val ≤ 17 ∧ (x.eval denv).val < 2 ^ (width.eval denv).val := by
          intro hne
          exact (hiff (x.eval denv) (width.eval denv) (bi.multiplicity.eval denv)).mp
            (by rw [← hmsg]; exact hob (by rw [hmsg]; exact hne))
        rcases hwc : width.constValue? with _ | widthValue
        · dsimp only
          simp only [dbItemOk, hmv, ex, ew]
          by_cases hz : (bi.multiplicity.eval denv).val = 0
          · simp [hz]
          · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
            obtain ⟨u1, u2⟩ := hkey hne
            simp [hz, u1, u2]
        · dsimp only
          have hweval : width.eval denv = widthValue := width.constValue?_sound _ hwc denv
          by_cases hle : widthValue.val ≤ 17
          · rw [if_pos hle]
            simp only [dbItemOk, hmv, ex]
            by_cases hz : (bi.multiplicity.eval denv).val = 0
            · simp [hz]
            · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
              obtain ⟨_, u2⟩ := hkey hne
              rw [hweval] at u2
              simp [hz, u2]
          · rw [if_neg hle]
            simp only [dbItemOk, hmv, ex, ew]
            by_cases hz : (bi.multiplicity.eval denv).val = 0
            · simp [hz]
            · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
              obtain ⟨u1, u2⟩ := hkey hne
              simp [hz, u1, u2]
      · rw [if_neg hvr]
        rcases ht : e.tuple? with _ | ⟨bx, byy⟩
        · dsimp only
          exact dbCompileOther_ok facts bi e ⟨‹_›, ‹_›, ‹_›, hvrf, htuf, ‹_›⟩ denv regs hagree hob
        · dsimp only
          obtain ⟨_, _, hiff⟩ := facts.tupleRangeBus_sound bi.busId bx byy (htuf _ ht)
          simp only [dbItemOk, hmv, ex, ew]
          by_cases hz : (bi.multiplicity.eval denv).val = 0
          · simp [hz]
          · have hne : bi.multiplicity.eval denv ≠ 0 := fun h0 => hz (by rw [h0, ZMod.val_zero])
            obtain ⟨u1, u2⟩ := (hiff (x.eval denv) (width.eval denv)
              (bi.multiplicity.eval denv)).mp (by rw [← hmsg]; exact hob (by rw [hmsg]; exact hne))
            simp [hz, u1, u2]
    · exact dbCompileOther_ok facts bi e ⟨‹_›, ‹_›, ‹_›, hvrf, htuf, ‹_›⟩ denv regs hagree hob

end Items

/-! ## 4. The scan

The mask is an intersection over surviving points, so the key facts are: absorbing *any* point can
only kill keys, and absorbing the assignment's own point makes every surviving key carry the
assignment's value. Reaching that point is an induction over the box dimensions. -/

/-- The register file carries the assignment's values on the target's keys. -/
def DbRegsAt (denv : VarId → ZMod p) (keys : Array ℕ) (regs : Array ℕ) : Prop :=
  ∀ d, d < keys.size → regs.getD (keys.getD d 0) 0 = (denv ⟨keys.getD d 0⟩).val

/-- Every key the mask still calls forced carries the assignment's value. -/
def DbMaskAgree (denv : VarId → ZMod p) (keys : Array ℕ) (st : DbScanSt) : Prop :=
  ∀ i, i < keys.size → st.alive.getD i false = true →
    st.vals.getD i 0 = (denv ⟨keys.getD i 0⟩).val

/-- What the scan must deliver: it started, and either nothing survives or the mask agrees. -/
def DbScanGood (denv : VarId → ZMod p) (keys : Array ℕ) (st : DbScanSt) : Prop :=
  st.started = true ∧ (st.live = 0 ∨ DbMaskAgree denv keys st)

theorem dbAbsorbGo_spec (regs keys vals : Array ℕ) :
    ∀ (m i live : ℕ) (alive : Array Bool), keys.size - i ≤ m →
      (dbAbsorbGo regs keys i vals alive live).1 = vals ∧
      (∀ j, (dbAbsorbGo regs keys i vals alive live).2.1.getD j false = true →
        alive.getD j false = true) ∧
      (∀ j, i ≤ j → j < keys.size →
        (dbAbsorbGo regs keys i vals alive live).2.1.getD j false = true →
        regs.getD (keys.getD j 0) 0 = vals.getD j 0) := by
  intro m
  induction m with
  | zero =>
    intro i live alive hm
    rw [dbAbsorbGo, dif_neg (by omega)]
    exact ⟨rfl, fun _ h => h, fun j hj hjs _ => absurd hjs (by omega)⟩
  | succ m ih =>
    intro i live alive hm
    by_cases hlt : i < keys.size
    · rw [dbAbsorbGo, dif_pos hlt]
      have hkey : keys.getD i 0 = keys[i] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]; rfl
      have hdead : ∀ (al : Array Bool), (al.set! i false).getD i false = false := by
        intro al
        rw [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds_self]
        split <;> rfl
      have hne : ∀ (al : Array Bool) (j : ℕ), j ≠ i →
          (al.set! i false).getD j false = al.getD j false := by
        intro al j hji
        rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!,
          Array.getElem?_setIfInBounds_ne (Ne.symm hji)]
      by_cases hal : alive.getD i false
      · rw [if_pos hal]
        by_cases heq : regs.getD keys[i] 0 == vals.getD i 0
        · rw [if_pos heq]
          obtain ⟨h1, h2, h3⟩ := ih (i + 1) live alive (by omega)
          refine ⟨h1, h2, fun j hj hjs hjl => ?_⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact h3 j (by omega) hjs hjl
          · have : j = i := by omega
            subst this; rw [hkey]; simpa using heq
        · rw [if_neg heq]
          obtain ⟨h1, h2, h3⟩ := ih (i + 1) (live - 1) (alive.set! i false) (by omega)
          refine ⟨h1, fun j hjl => ?_, fun j hj hjs hjl => ?_⟩
          · have hj2 := h2 j hjl
            rcases Nat.decEq j i with hji | hji
            · rwa [hne alive j hji] at hj2
            · subst hji; rw [hdead alive] at hj2; exact absurd hj2 (by simp)
          · rcases Nat.lt_or_ge i j with hij | hij
            · exact h3 j (by omega) hjs hjl
            · have hji : j = i := by omega
              subst hji
              have hj2 := h2 j hjl
              rw [hdead alive] at hj2; exact absurd hj2 (by simp)
      · rw [if_neg hal]
        obtain ⟨h1, h2, h3⟩ := ih (i + 1) live alive (by omega)
        refine ⟨h1, h2, fun j hj hjs hjl => ?_⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact h3 j (by omega) hjs hjl
        · have : j = i := by omega
          subst this
          exact absurd (h2 j hjl) (by simpa using hal)
    · rw [dbAbsorbGo, dif_neg hlt]
      exact ⟨rfl, fun _ h => h, fun j hj hjs _ => absurd hjs (by omega)⟩

theorem dbAbsorbArgs_true (keys regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) :
    dbAbsorbArgs keys regs vals alive live true =
      ((dbAbsorbGo regs keys 0 vals alive live).1, (dbAbsorbGo regs keys 0 vals alive live).2.1,
        (dbAbsorbGo regs keys 0 vals alive live).2.2, true) := by
  rw [dbAbsorbArgs]; simp

theorem dbAbsorbArgs_false (keys regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) :
    dbAbsorbArgs keys regs vals alive live false =
      (keys.map (fun k => regs.getD k 0), Array.replicate keys.size true, keys.size, true) := by
  rw [dbAbsorbArgs]; simp

theorem dbMap_getD (keys : Array ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < keys.size) :
    (keys.map f).getD j 0 = f (keys.getD j 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hj), Array.getElem?_eq_getElem hj,
    Array.getElem_map]
  rfl

/-- Absorbing the assignment's own point leaves the mask agreeing with it, whatever it held. -/
theorem dbAbsorbArgs_agree (denv : VarId → ZMod p) (keys regs vals : Array ℕ)
    (alive : Array Bool) (live : ℕ) (started : Bool) (hregs : DbRegsAt denv keys regs) :
    ∀ j, j < keys.size →
      (dbAbsorbArgs keys regs vals alive live started).2.1.getD j false = true →
      (dbAbsorbArgs keys regs vals alive live started).1.getD j 0
        = (denv ⟨keys.getD j 0⟩).val := by
  intro j hj hal
  cases started with
  | true =>
    rw [dbAbsorbArgs_true] at hal ⊢
    obtain ⟨h1, _, h3⟩ := dbAbsorbGo_spec regs keys vals keys.size 0 live alive (by omega)
    simp only at hal ⊢
    rw [h1, ← h3 j (Nat.zero_le j) hj hal]
    exact hregs j hj
  | false =>
    rw [dbAbsorbArgs_false] at hal ⊢
    simp only at hal ⊢
    rw [dbMap_getD keys _ j hj]
    exact hregs j hj

/-- Absorbing any point can only kill keys, so agreement survives. -/
theorem dbAbsorbArgs_preserve (denv : VarId → ZMod p) (keys regs vals : Array ℕ)
    (alive : Array Bool) (live : ℕ)
    (hag : ∀ j, j < keys.size → alive.getD j false = true →
      vals.getD j 0 = (denv ⟨keys.getD j 0⟩).val) :
    ∀ j, j < keys.size →
      (dbAbsorbArgs keys regs vals alive live true).2.1.getD j false = true →
      (dbAbsorbArgs keys regs vals alive live true).1.getD j 0
        = (denv ⟨keys.getD j 0⟩).val := by
  intro j hj hal
  rw [dbAbsorbArgs_true] at hal ⊢
  obtain ⟨h1, h2, _⟩ := dbAbsorbGo_spec regs keys vals keys.size 0 live alive (by omega)
  simp only at hal ⊢
  rw [h1]
  exact hag j hj (h2 j hal)

/-- Once the mask is good, the rest of the sweep keeps it good. -/
theorem dbScanLoop_preserve {bs : BusSemantics p} (facts : BusFacts p bs)
    (items : Array (DbItem p)) (ilev : Array ℕ) (keys : Array ℕ) (doms : Array DbDom)
    (denv : VarId → ZMod p) :
    ∀ (d key : ℕ) (dom : DbDom) (i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
      (started : Bool),
      DbScanGood denv keys ⟨regs, vals, alive, live, started⟩ →
      DbScanGood denv keys
        (dbScanLoop facts items ilev keys doms d key dom i n regs vals alive live started) := by
  intro d key dom i n regs vals alive live started
  induction d, key, dom, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items ilev keys doms with
  | case1 d key dom i n regs vals alive live started hge =>
    intro hg; rw [dbScanLoop, if_pos hge]; exact hg
  | case2 d key dom i n regs vals alive live started hlt hdead =>
    intro hg; rw [dbScanLoop, if_neg hlt, if_pos hdead]; exact hg
  | case3 d key dom i n regs vals alive live started hlt halive regs1 hok hinner vals1 alive1
      live1 started1 habs ih =>
    intro hg
    obtain ⟨hst, hlive⟩ := hg
    have hst' : started = true := hst
    subst hst'
    have hne : ¬ live = 0 := fun h0 => halive (by simp [h0])
    have hagree : DbMaskAgree denv keys ⟨regs, vals, alive, live, true⟩ := hlive.resolve_left hne
    have habs' : dbAbsorbArgs keys (regs.set! key (DbDom.at p dom i))
        vals alive live true = (vals1, alive1, live1, started1) := habs
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_pos hinner, habs']
    refine ih ⟨?_, Or.inr ?_⟩
    · have hst4 : (dbAbsorbArgs keys (regs.set! key (DbDom.at p dom i))
          vals alive live true).2.2.2 = started1 := congrArg (fun r => r.2.2.2) habs'
      rw [dbAbsorbArgs_true] at hst4
      exact hst4.symm
    · intro j hj hj2
      rw [show vals1 = (dbAbsorbArgs keys regs1 vals alive live true).1 from
        (congrArg (fun r => r.1) habs).symm]
      refine dbAbsorbArgs_preserve denv keys regs1 vals alive live hagree j hj ?_
      rw [show (dbAbsorbArgs keys regs1 vals alive live true).2.1 = alive1 from
        congrArg (fun r => r.2.1) habs]
      exact hj2
  | case4 d key dom i n regs vals alive live started hlt halive regs1 hok hinner dom' regs2 vals1
      alive1 live1 started1 hrec ihinner ih =>
    intro hg
    have hrec' : dbScanLoop facts items ilev keys doms (d + 1) (keys.getD (d + 1) 0)
        (doms.getD (d + 1) (DbDom.range 0)) 0 (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! key (DbDom.at p dom i)) vals alive live started
        = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_neg hinner]
    simp only
    rw [hrec']
    refine ih ?_
    have := ihinner hg
    rw [hrec'] at this
    exact this
  | case5 d key dom i n regs vals alive live started hlt halive regs1 hok ih =>
    intro hg
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_neg hok]
    exact ih hg

theorem dbSetD_self (regs : Array ℕ) (k v : ℕ) (hk : k < regs.size) :
    (regs.set! k v).getD k 0 = v := by
  rw [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds_self, if_pos hk]
  rfl

theorem dbSet_size (regs : Array ℕ) (k v : ℕ) : (regs.set! k v).size = regs.size := by
  rw [Array.set!]; simp

theorem dbSetD_ne {α : Type} (a : Array α) (k k' : ℕ) (v dflt : α) (h : k' ≠ k) :
    (a.set! k v).getD k' dflt = a.getD k' dflt := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!,
    Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-- The sweep at dimension `d` writes only the keys from `d` on. -/
theorem dbScanLoop_regs {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem p))
    (ilev : Array ℕ) (keys : Array ℕ) (doms : Array DbDom) (k : ℕ) :
    ∀ (d key : ℕ) (dom : DbDom) (i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
      (started : Bool),
      key = keys.getD d 0 → d < keys.size →
      (∀ d', d ≤ d' → d' < keys.size → keys.getD d' 0 ≠ k) →
      (dbScanLoop facts items ilev keys doms d key dom i n regs vals alive live
        started).regs.getD k 0 = regs.getD k 0 := by
  intro d key dom i n regs vals alive live started
  induction d, key, dom, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items ilev keys doms with
  | case1 d key dom i n regs vals alive live started hge =>
    intro _ _ _; rw [dbScanLoop, if_pos hge]
  | case2 d key dom i n regs vals alive live started hlt hdead =>
    intro _ _ _; rw [dbScanLoop, if_neg hlt, if_pos hdead]
  | case3 d key dom i n regs vals alive live started hlt halive regs1 hok hinner vals1 alive1
      live1 started1 habs ih =>
    intro hkey hd hfp
    subst hkey
    have habs' : dbAbsorbArgs keys (regs.set! (keys.getD d 0) (DbDom.at p dom i))
        vals alive live started = (vals1, alive1, live1, started1) := habs
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_pos hinner, habs', ih rfl hd hfp]
    exact dbSetD_ne regs _ k _ 0 (fun he => hfp d (le_refl d) hd he.symm)
  | case4 d key dom i n regs vals alive live started hlt halive regs1 hok hinner dom' regs2 vals1
      alive1 live1 started1 hrec ihinner ih =>
    intro hkey hd hfp
    subst hkey
    have hrec' : dbScanLoop facts items ilev keys doms (d + 1) (keys.getD (d + 1) 0)
        (doms.getD (d + 1) (DbDom.range 0)) 0 (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p dom i)) vals alive live started
        = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_neg hinner]
    simp only
    rw [hrec', ih rfl hd hfp]
    have hin := ihinner rfl (by omega) (fun d' hd' hlt' => hfp d' (by omega) hlt')
    rw [hrec'] at hin
    rw [hin]
    exact dbSetD_ne regs _ k _ 0 (fun he => hfp d (le_refl d) hd he.symm)
  | case5 d key dom i n regs vals alive live started hlt halive regs1 hok ih =>
    intro hkey hd hfp
    subst hkey
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_neg hok, ih rfl hd hfp]
    exact dbSetD_ne regs _ k _ 0 (fun he => hfp d (le_refl d) hd he.symm)

theorem dbScanLoop_size {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem p))
    (ilev : Array ℕ) (keys : Array ℕ) (doms : Array DbDom) :
    ∀ (d key : ℕ) (dom : DbDom) (i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
      (started : Bool),
      (dbScanLoop facts items ilev keys doms d key dom i n regs vals alive live started).regs.size
        = regs.size := by
  intro d key dom i n regs vals alive live started
  induction d, key, dom, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items ilev keys doms with
  | case1 d key dom i n regs vals alive live started hge => rw [dbScanLoop, if_pos hge]
  | case2 d key dom i n regs vals alive live started hlt hdead =>
    rw [dbScanLoop, if_neg hlt, if_pos hdead]
  | case3 d key dom i n regs vals alive live started hlt halive regs1 hok hinner vals1 alive1
      live1 started1 habs ih =>
    have habs' : dbAbsorbArgs keys (regs.set! key (DbDom.at p dom i))
        vals alive live started = (vals1, alive1, live1, started1) := habs
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_pos hinner, habs', ih, dbSet_size]
  | case4 d key dom i n regs vals alive live started hlt halive regs1 hok hinner dom' regs2 vals1
      alive1 live1 started1 hrec ihinner ih =>
    have hrec' : dbScanLoop facts items ilev keys doms (d + 1) (keys.getD (d + 1) 0)
        (doms.getD (d + 1) (DbDom.range 0)) 0 (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! key (DbDom.at p dom i)) vals alive live started
        = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_neg hinner]
    simp only
    rw [hrec', ih]
    have hin := ihinner
    rw [hrec'] at hin
    rw [hin, dbSet_size]
  | case5 d key dom i n regs vals alive live started hlt halive regs1 hok ih =>
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_neg hok, ih, dbSet_size]

/-- The sweep reaches the assignment's own point, so the mask ends up agreeing with it. `hitems`
    is level-aware: an item is tested at the depth of its innermost key, where the registers
    already carry the assignment's values for every key up to that depth. -/
theorem dbScanLoop_reach {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem p))
    (ilev : Array ℕ) (keys : Array ℕ) (doms : Array DbDom) (denv : VarId → ZMod p) (idx : ℕ → ℕ)
    (hdist : ∀ a b, a < keys.size → b < keys.size → keys.getD a 0 = keys.getD b 0 → a = b)
    (hidx : ∀ d, d < keys.size → idx d < (doms.getD d (.range 0)).size ∧
      DbDom.at p (doms.getD d (.range 0)) (idx d) = (denv ⟨keys.getD d 0⟩).val)
    (hitems : ∀ (dd : ℕ) (regs' : Array ℕ), dd < keys.size →
      (∀ d', d' ≤ dd → regs'.getD (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val) →
      dbAllOkLev facts items ilev dd regs' 0 = true) :
    ∀ (d key : ℕ) (dom : DbDom) (i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
      (started : Bool),
      key = keys.getD d 0 → dom = doms.getD d (.range 0) →
      d < keys.size → n = (doms.getD d (.range 0)).size → i ≤ idx d →
      (∀ d', d' < keys.size → keys.getD d' 0 < regs.size) →
      (∀ d', d' < d → regs.getD (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val) →
      DbScanGood denv keys
        (dbScanLoop facts items ilev keys doms d key dom i n regs vals alive live started) := by
  intro d key dom i n regs vals alive live started
  induction d, key, dom, i, n, regs, vals, alive, live, started using
    dbScanLoop.induct facts items ilev keys doms with
  | case1 d key dom i n regs vals alive live started hge =>
    intro _ hdom hd hn hi _ _
    subst hdom
    exact absurd hge (by rw [hn]; have := (hidx d hd).1; omega)
  | case2 d key dom i n regs vals alive live started hlt hdead =>
    intro _ _ _ _ _ _ _
    rw [dbScanLoop, if_neg hlt, if_pos hdead]
    simp only [Bool.and_eq_true, beq_iff_eq] at hdead
    exact ⟨hdead.1, Or.inl hdead.2⟩
  | case3 d key dom i n regs vals alive live started hlt halive regs1 hok hinner vals1 alive1
      live1 started1 habs ih =>
    intro hkey hdom hd hn hi hcov houter
    subst hkey; subst hdom
    have habs' : dbAbsorbArgs keys
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = (vals1, alive1, live1, started1) := habs
    have hset : ∀ d', d' < d →
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD
          (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val := by
      intro d' hd'
      rw [dbSetD_ne regs _ _ _ 0 (fun he => by
        have := hdist d' d (by omega) hd he; omega)]
      exact houter d' hd'
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_pos hinner, habs']
    rcases Nat.lt_or_ge i (idx d) with hlti | hgei
    · exact ih rfl rfl hd hn (by omega) (fun d' hd' => by rw [dbSet_size]; exact hcov d' hd')
        (fun d' hd' => hset d' hd')
    · have hieq : i = idx d := by omega
      have hregsAt : DbRegsAt denv keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)) := by
        intro d0 hd0
        rcases Nat.lt_trichotomy d0 d with h | h | h
        · exact hset d0 h
        · subst h
          rw [dbSetD_self regs _ _ (hcov d0 hd0), hieq]
          exact (hidx d0 hd0).2
        · omega
      refine dbScanLoop_preserve facts items ilev keys doms denv _ _ _ _ _ _ _ _ _ _ ⟨?_, Or.inr ?_⟩
      · have hst4 : (dbAbsorbArgs keys
            (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
            vals alive live started).2.2.2 = started1 := congrArg (fun r => r.2.2.2) habs'
        cases started with
        | true => rw [dbAbsorbArgs_true] at hst4; exact hst4.symm
        | false => rw [dbAbsorbArgs_false] at hst4; exact hst4.symm
      · intro j hj hj2
        rw [show vals1 = (dbAbsorbArgs keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live started).1 from (congrArg (fun r => r.1) habs').symm]
        refine dbAbsorbArgs_agree denv keys _ vals alive live started hregsAt j hj ?_
        rw [show (dbAbsorbArgs keys
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live started).2.1 = alive1 from congrArg (fun r => r.2.1) habs']
        exact hj2
  | case4 d key dom i n regs vals alive live started hlt halive regs1 hok hinner dom' regs2 vals1
      alive1 live1 started1 hrec ihinner ih =>
    intro hkey hdom hd hn hi hcov houter
    subst hkey; subst hdom
    have hrec' : dbScanLoop facts items ilev keys doms (d + 1) (keys.getD (d + 1) 0)
        (doms.getD (d + 1) (DbDom.range 0)) 0 (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started = ⟨regs2, vals1, alive1, live1, started1⟩ := hrec
    have hd1 : d + 1 < keys.size := by omega
    have hset : ∀ d', d' < d →
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD
          (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val := by
      intro d' hd'
      rw [dbSetD_ne regs _ _ _ 0 (fun he => by
        have := hdist d' d (by omega) hd he; omega)]
      exact houter d' hd'
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_pos hok, if_neg hinner]
    simp only
    rw [hrec']
    rcases Nat.lt_or_ge i (idx d) with hlti | hgei
    · refine ih rfl rfl hd hn (by omega) (fun d' hd' => by
        have hsz := dbScanLoop_size facts items ilev keys doms (d + 1) (keys.getD (d + 1) 0)
          (doms.getD (d + 1) (DbDom.range 0)) 0 (doms.getD (d + 1) (DbDom.range 0)).size
          (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
          vals alive live started
        rw [hrec'] at hsz
        rw [show regs2.size = regs.size from by rw [hsz, dbSet_size]]
        exact hcov d' hd') (fun d' hd' => ?_)
      have hfoot := dbScanLoop_regs facts items ilev keys doms (keys.getD d' 0) (d + 1)
        (keys.getD (d + 1) 0) (doms.getD (d + 1) (DbDom.range 0)) 0
        (doms.getD (d + 1) (DbDom.range 0)).size
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i))
        vals alive live started rfl hd1
        (fun e he hes hkey' => by have := hdist d' e (by omega) hes hkey'.symm; omega)
      rw [hrec'] at hfoot
      rw [hfoot]
      exact hset d' hd'
    · have hieq : i = idx d := by omega
      refine dbScanLoop_preserve facts items ilev keys doms denv _ _ _ _ _ _ _ _ _ _ ?_
      have := ihinner rfl rfl hd1 rfl (Nat.zero_le _)
        (fun d' hd' => by rw [dbSet_size]; exact hcov d' hd') (fun d' hd' => by
        rcases Nat.lt_trichotomy d' d with h | h | h
        · exact hset d' h
        · subst h
          rw [dbSetD_self regs _ _ (hcov d' hd), hieq]
          exact (hidx d' hd).2
        · omega)
      rw [hrec'] at this
      exact this
  | case5 d key dom i n regs vals alive live started hlt halive regs1 hok ih =>
    intro hkey hdom hd hn hi hcov houter
    subst hkey; subst hdom
    have hset : ∀ d', d' < d →
        (regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD
          (keys.getD d' 0) 0 = (denv ⟨keys.getD d' 0⟩).val := by
      intro d' hd'
      rw [dbSetD_ne regs _ _ _ 0 (fun he => by
        have := hdist d' d (by omega) hd he; omega)]
      exact houter d' hd'
    rw [dbScanLoop, if_neg hlt, if_neg halive, if_neg hok]
    rcases Nat.lt_or_ge i (idx d) with hlti | hgei
    · exact ih rfl rfl hd hn (by omega) (fun d' hd' => by rw [dbSet_size]; exact hcov d' hd')
        (fun d' hd' => hset d' hd')
    · -- the assignment's own point cannot fail the level-`d` items
      exfalso
      refine hok (hitems d _ hd ?_)
      intro d0 hd0
      rcases Nat.lt_or_ge d0 d with h | h
      · exact hset d0 h
      · have hd0d : d0 = d := by omega
        subst hd0d
        rw [dbSetD_self regs _ _ (hcov d0 hd), show i = idx d0 from by omega]
        exact (hidx d0 hd).2

/-! ## 5. Assembling the invocation

The scan is sound point-wise (layer 4); what remains is that the pass only ever scans boxes it is
entitled to: the domain table is sound (layer 2), the gathered items hold at the assignment (layer
3), and the two "no answer" exits — a failing variable-free obligation and an empty box — happen
only when nothing satisfies the system. -/

/-- Agreement on an array of variables, as the context's per-item variable lists carry them. -/
def DbRegsAgreeA (denv : VarId → ZMod p) (regs : Array ℕ) (vs : Array VarId) : Prop :=
  ∀ i ∈ vs, regs.getD i.index 0 = (denv i).val

/-- A target's keys are pairwise distinct, so the sweep's dimensions write disjoint registers. -/
def DbNodupIdx (vs : Array VarId) : Prop :=
  ∀ a b, a < vs.size → b < vs.size → (vs.getD a ⟨0⟩).index = (vs.getD b ⟨0⟩).index → a = b

private theorem dbListFoldlInv {α : Type u} {β : Type v} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α), (∀ b a, a ∈ l → P b → P (f b a)) → ∀ b0, P b0 → P (l.foldl f b0) := by
  intro l
  induction l with
  | nil => intro _ b0 h0; exact h0
  | cons a rest ih =>
    intro hstep b0 h0
    rw [List.foldl_cons]
    exact ih (fun b a' ha' hb => hstep b a' (List.mem_cons_of_mem _ ha') hb) _
      (hstep b0 a (List.mem_cons_self ..) h0)

/-- Any invariant preserved by one step of an array fold survives the fold. -/
theorem dbFoldlInv {α : Type u} {β : Type v} (P : β → Prop) (f : β → α → β) (as : Array α)
    (hstep : ∀ b a, a ∈ as → P b → P (f b a)) (b0 : β) (h0 : P b0) : P (as.foldl f b0) := by
  rw [← Array.foldl_toList]
  exact dbListFoldlInv P f as.toList (fun b a ha hb => hstep b a (by simpa using ha) hb) b0 h0

/-- A position of `as.zipIdx` names its own element. -/
theorem dbMem_zipIdx {α : Type u} (as : Array α) (x : α × ℕ) (h : x ∈ as.zipIdx) :
    ∃ hlt : x.2 < as.size, as[x.2] = x.1 := by
  have h' : as[x.2]? = some x.1 := Array.mem_zipIdx_iff_getElem?.mp h
  have hlt : x.2 < as.size := by
    rcases Nat.lt_or_ge x.2 as.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at h'; exact absurd h' (by simp)
  rw [Array.getElem?_eq_getElem hlt] at h'
  exact ⟨hlt, Option.some.inj h'⟩

/-! ### Constant domains

`DbDom.at` reduces a `Nat` index into the field, so a one-element domain pins its variable's value
whatever representative the index arithmetic produced. -/

theorem dbAddN_modEq (p a b : ℕ) : dbAddN p a b % p = (a + b) % p := by
  unfold dbAddN
  by_cases h : a + b < p
  · rw [if_pos h]
  · rw [if_neg h]
    exact (Nat.mod_eq_sub_mod (Nat.le_of_not_lt h)).symm

theorem dbMulN_addN (p a b c : ℕ) : dbMulN p (dbAddN p a b) c = (a + b) * c % p := by
  rw [dbMulN, Nat.mul_mod, dbAddN_modEq, ← Nat.mul_mod]

/-- A domain admitting a single value pins any of its members to that value. -/
theorem dbDom_const?_sound [NeZero p] (dm : DbDom) (v c : ℕ) (hmem : DbDomMem p dm v)
    (hc : DbDom.const? p dm = some c) : v = c := by
  obtain ⟨k, hk, hat⟩ := hmem
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  cases dm with
  | explicit vs =>
    simp only [DbDom.size] at hk
    simp only [DbDom.const?] at hc
    rcases h0 : vs[0]? with _ | v0
    · rw [h0] at hc; exact absurd hc (by simp)
    · rw [h0] at hc
      dsimp only at hc
      by_cases hall : vs.all (fun w => w == v0)
      · rw [if_pos hall] at hc
        have hcv : v0 = c := by simpa using hc
        have hall' : ∀ (i : ℕ) (h : i < vs.size), vs[i] = v0 := by simpa using hall
        rw [← hcv, ← hat]
        simp only [DbDom.at]
        rw [dbGetD_lt vs k 0 hk]
        exact hall' k hk
      · rw [if_neg hall] at hc; exact absurd hc (by simp)
  | range b =>
    simp only [DbDom.size] at hk
    simp only [DbDom.const?] at hc
    by_cases hb : b == 1
    · rw [if_pos hb] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      have hk0 : k = 0 := by simp only [beq_iff_eq] at hb; omega
      subst hk0
      rw [← hat]
      simp [DbDom.at]
    · rw [if_neg hb] at hc; exact absurd hc (by simp)
  | coset b negB aInv =>
    simp only [DbDom.size] at hk
    simp only [DbDom.const?] at hc
    by_cases hb : b == 1
    · rw [if_pos hb] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      have hk0 : k = 0 := by simp only [beq_iff_eq] at hb; omega
      subst hk0
      rw [← hat]
      simp only [DbDom.at]
      rw [if_pos hp, dbMulN_addN, Nat.zero_add, dbMulN]
    · rw [if_neg hb] at hc; exact absurd hc (by simp)

private theorem dbConstantDomains_go [NeZero p] (denv : VarId → ZMod p) (doms : Array DbDom) :
    ∀ (l : List (VarId × ℕ)),
      (∀ ki ∈ l, DbDomMem p (doms.getD ki.2 (.range 0)) (denv ki.1).val) →
      ∀ f ∈ (l.foldr (init := ([] : List (VarId × ZMod p))) fun ki acc =>
          match DbDom.const? p (doms.getD ki.2 (.range 0)) with
          | some c => (ki.1, zmodOfNatP p c) :: acc
          | none => acc), denv f.1 = f.2 := by
  intro l
  induction l with
  | nil => intro _ f hf; simp at hf
  | cons ki rest ih =>
    intro hmem f hf
    rw [List.foldr_cons] at hf
    rcases hc : DbDom.const? p (doms.getD ki.2 (.range 0)) with _ | c
    · rw [hc] at hf
      exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) f hf
    · rw [hc] at hf
      dsimp only at hf
      rcases List.mem_cons.mp hf with rfl | hf'
      · show denv ki.1 = zmodOfNatP p c
        rw [← dbDom_const?_sound (doms.getD ki.2 (.range 0)) (denv ki.1).val c
          (hmem ki (List.mem_cons_self ..)) hc, zmodOfNatP_val]
      · exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) f hf'

/-- The answers a target needs no scan for: every one-element domain forces its key. -/
theorem dbConstantDomains_sound [NeZero p] (denv : VarId → ZMod p) (keys : Array VarId)
    (doms : Array DbDom)
    (hdom : ∀ k, ∀ hk : k < keys.size, DbDomMem p (doms.getD k (.range 0)) (denv keys[k]).val) :
    ∀ f ∈ dbConstantDomains p keys doms, denv f.1 = f.2 := by
  rw [dbConstantDomains, ← Array.foldr_toList]
  refine dbConstantDomains_go denv doms keys.zipIdx.toList (fun ki hki => ?_)
  obtain ⟨hlt, heq⟩ := dbMem_zipIdx keys ki (Array.mem_toList_iff.mp hki)
  rw [← heq]
  exact hdom ki.2 hlt

/-! ### The target's domains

`dbDomsOf` answers only when every key is domained, and then key `k`'s domain sits at position `k`. -/

private theorem dbDomsGo_none (T : DbTab p) : ∀ (l : List VarId),
    l.foldl (fun acc v => match acc with
      | none => none
      | some ds => match T.get v.index with
        | none => none
        | some dm => some (ds.push dm)) (none : Option (Array DbDom)) = none := by
  intro l
  induction l with
  | nil => rfl
  | cons v rest ih => simpa using ih

private theorem dbGetD_push_lt (acc : Array DbDom) (dm : DbDom) (k : ℕ) (h : k < acc.size) :
    (acc.push dm).getD k (.range 0) = acc.getD k (.range 0) := by
  rw [dbGetD_lt _ _ _ (by rw [Array.size_push]; omega), dbGetD_lt _ _ _ h,
    Array.getElem_push_lt h]

private theorem dbGetD_push_eq (acc : Array DbDom) (dm : DbDom) :
    (acc.push dm).getD acc.size (.range 0) = dm := by
  rw [dbGetD_lt _ _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

private theorem dbDomsGo (T : DbTab p) : ∀ (l : List VarId) (acc doms : Array DbDom),
    l.foldl (fun acc v => match acc with
      | none => none
      | some ds => match T.get v.index with
        | none => none
        | some dm => some (ds.push dm)) (some acc) = some doms →
      (∀ k, k < acc.size → doms.getD k (.range 0) = acc.getD k (.range 0)) ∧
      (∀ k v, l[k]? = some v → T.get v.index = some (doms.getD (acc.size + k) (.range 0))) := by
  intro l
  induction l with
  | nil =>
    intro acc doms h
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => rfl, fun k v hv => by simp at hv⟩
  | cons v rest ih =>
    intro acc doms h
    simp only [List.foldl_cons] at h
    rcases hg : T.get v.index with _ | dm
    · rw [hg] at h
      simp only at h
      rw [dbDomsGo_none] at h
      exact absurd h (by simp)
    · rw [hg] at h
      simp only at h
      obtain ⟨h1, h2⟩ := ih (acc.push dm) doms h
      refine ⟨fun k hk => by rw [h1 k (by rw [Array.size_push]; omega), dbGetD_push_lt acc dm k hk],
        fun k w hw => ?_⟩
      rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
        subst hw
        rw [hg, Nat.add_zero, h1 acc.size (by rw [Array.size_push]; omega), dbGetD_push_eq]
      · rw [List.getElem?_cons_succ] at hw
        have := h2 k w hw
        rwa [Array.size_push, show acc.size + 1 + k = acc.size + (k + 1) from by omega] at this

/-- Key `k` of a preflighted target carries the domain the table holds for it. -/
theorem dbDomsOf_get (T : DbTab p) (vs : Array VarId) (doms : Array DbDom)
    (h : dbDomsOf T vs = some doms) :
    ∀ k, ∀ hk : k < vs.size, T.get vs[k].index = some (doms.getD k (.range 0)) := by
  rw [dbDomsOf, ← Array.foldl_toList] at h
  obtain ⟨_, h2⟩ := dbDomsGo T vs.toList #[] doms h
  intro k hk
  have := h2 k vs[k] (by rw [List.getElem?_eq_getElem (by simpa using hk)]; simp)
  simpa using this

/-! ### The mask's answer -/

theorem dbForcedOfMask_sound [NeZero p] (denv : VarId → ZMod p) (keys : Array VarId)
    (vals : Array ℕ) (alive : Array Bool)
    (hag : ∀ j, ∀ hj : j < keys.size, alive.getD j false = true →
      vals.getD j 0 = (denv keys[j]).val) :
    ∀ (i : ℕ), ∀ f ∈ dbForcedOfMask p keys vals alive i, denv f.1 = f.2 := by
  intro i
  induction hn : keys.size - i generalizing i with
  | zero =>
    intro f hf
    rw [dbForcedOfMask, dif_neg (by omega)] at hf
    simp at hf
  | succ n ih =>
    intro f hf
    have hlt : i < keys.size := by omega
    rw [dbForcedOfMask, dif_pos hlt] at hf
    dsimp only at hf
    by_cases hal : alive.getD i false
    · rw [if_pos hal] at hf
      rcases List.mem_cons.mp hf with rfl | hf'
      · show denv keys[i] = zmodOfNatP p (vals.getD i 0)
        rw [hag i hlt hal, zmodOfNatP_val]
      · exact ih (i + 1) (by omega) f hf'
    · rw [if_neg hal] at hf
      exact ih (i + 1) (by omega) f hf

/-! ### The per-item variable lists

`dbVarsOf` collects a superset of `DenseExpr.vars` without duplicates: the first gives agreement on
every expression the item mentions, the second that the sweep's dimensions are independent. -/

private theorem dbPushVar_mem (acc : Array VarId) (i : VarId) : ∀ x ∈ acc, x ∈ dbPushVar acc i := by
  intro x hx
  rw [dbPushVar]
  split
  · exact hx
  · exact Array.mem_push_of_mem _ hx

private theorem dbPushVar_self (acc : Array VarId) (i : VarId) : i ∈ dbPushVar acc i := by
  rw [dbPushVar]
  split
  · next h => exact Array.contains_iff_mem.mp h
  · exact Array.mem_push_self

private theorem dbVarsOf_mem : ∀ (e : DenseExpr p) (acc : Array VarId),
    (∀ x ∈ acc, x ∈ dbVarsOf e acc) ∧ (∀ i ∈ e.vars, i ∈ dbVarsOf e acc) := by
  intro e
  induction e with
  | const c => intro acc; exact ⟨fun x hx => hx, fun i hi => by simp [DenseExpr.vars] at hi⟩
  | var j =>
    intro acc
    refine ⟨dbPushVar_mem acc j, fun i hi => ?_⟩
    have hij : i = j := by simpa [DenseExpr.vars] using hi
    subst hij
    exact dbPushVar_self acc i
  | add a b iha ihb =>
    intro acc
    refine ⟨fun x hx => (ihb (dbVarsOf a acc)).1 x ((iha acc).1 x hx), fun i hi => ?_⟩
    rcases List.mem_append.mp (by simpa only [DenseExpr.vars] using hi) with h | h
    · exact (ihb (dbVarsOf a acc)).1 i ((iha acc).2 i h)
    · exact (ihb (dbVarsOf a acc)).2 i h
  | mul a b iha ihb =>
    intro acc
    refine ⟨fun x hx => (ihb (dbVarsOf a acc)).1 x ((iha acc).1 x hx), fun i hi => ?_⟩
    rcases List.mem_append.mp (by simpa only [DenseExpr.vars] using hi) with h | h
    · exact (ihb (dbVarsOf a acc)).1 i ((iha acc).2 i h)
    · exact (ihb (dbVarsOf a acc)).2 i h

private theorem dbVarsOfList_mem : ∀ (es : List (DenseExpr p)) (acc : Array VarId),
    (∀ x ∈ acc, x ∈ dbVarsOfList es acc) ∧
      (∀ e ∈ es, ∀ i ∈ e.vars, i ∈ dbVarsOfList es acc) := by
  intro es
  induction es with
  | nil => intro acc; exact ⟨fun x hx => hx, fun e he => by simp at he⟩
  | cons e rest ih =>
    intro acc
    refine ⟨fun x hx => (ih (dbVarsOf e acc)).1 x ((dbVarsOf_mem e acc).1 x hx),
      fun e' he' i hi => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he''
    · exact (ih (dbVarsOf e' acc)).1 i ((dbVarsOf_mem e' acc).2 i hi)
    · exact (ih (dbVarsOf e acc)).2 e' he'' i hi

theorem dbVarsOf_agree (denv : VarId → ZMod p) (regs : Array ℕ) (e : DenseExpr p)
    (h : DbRegsAgreeA denv regs (dbVarsOf e #[])) : DbRegsAgree denv regs e.vars :=
  fun i hi => h i ((dbVarsOf_mem e #[]).2 i hi)

theorem dbBiVars_agree (denv : VarId → ZMod p) (regs : Array ℕ)
    (bi : BusInteraction (DenseExpr p)) (h : DbRegsAgreeA denv regs (dbBiVars bi)) :
    DbRegsAgree denv regs (denseBIVars bi) := by
  intro i hi
  refine h i ?_
  rw [dbBiVars]
  rcases List.mem_append.mp (by simpa only [denseBIVars] using hi) with hm | hm
  · exact (dbVarsOfList_mem bi.payload (dbVarsOf bi.multiplicity #[])).1 i
      ((dbVarsOf_mem bi.multiplicity #[]).2 i hm)
  · obtain ⟨e, he, hie⟩ := List.mem_flatMap.mp hm
    exact (dbVarsOfList_mem bi.payload (dbVarsOf bi.multiplicity #[])).2 e he i hie

/-- Positional distinctness, in the `getElem` form the collectors preserve. -/
private def DbNodupA (vs : Array VarId) : Prop :=
  ∀ a b (ha : a < vs.size) (hb : b < vs.size), vs[a] = vs[b] → a = b

private theorem dbVarId_eq (x y : VarId) (h : x.index = y.index) : x = y := by
  cases x; cases y; simpa using h

private theorem dbNodupIdx_of (vs : Array VarId) (h : DbNodupA vs) : DbNodupIdx vs := by
  intro a b ha hb hidx
  rw [dbGetD_lt vs a ⟨0⟩ ha, dbGetD_lt vs b ⟨0⟩ hb] at hidx
  exact h a b ha hb (dbVarId_eq _ _ hidx)

private theorem dbPushVar_nodup (acc : Array VarId) (i : VarId) (h : DbNodupA acc) :
    DbNodupA (dbPushVar acc i) := by
  rw [dbPushVar]
  split
  · exact h
  · next hc =>
    have hni : ∀ k, ∀ hk : k < acc.size, acc[k] ≠ i := by
      intro k hk hki
      exact hc (Array.contains_iff_mem.mpr (by rw [← hki]; exact Array.getElem_mem hk))
    intro a b ha hb hab
    rw [Array.size_push] at ha hb
    rcases Nat.lt_or_ge a acc.size with h1 | h1 <;> rcases Nat.lt_or_ge b acc.size with h2 | h2
    · rw [Array.getElem_push_lt h1, Array.getElem_push_lt h2] at hab
      exact h a b h1 h2 hab
    · have hb' : b = acc.size := by omega
      subst hb'
      rw [Array.getElem_push_lt h1, Array.getElem_push_eq] at hab
      exact absurd hab (hni a h1)
    · have ha' : a = acc.size := by omega
      subst ha'
      rw [Array.getElem_push_lt h2, Array.getElem_push_eq] at hab
      exact absurd hab.symm (hni b h2)
    · omega

private theorem dbVarsOf_nodup : ∀ (e : DenseExpr p) (acc : Array VarId), DbNodupA acc →
    DbNodupA (dbVarsOf e acc) := by
  intro e
  induction e with
  | const c => intro acc h; exact h
  | var j => intro acc h; exact dbPushVar_nodup acc j h
  | add a b iha ihb => intro acc h; exact ihb _ (iha acc h)
  | mul a b iha ihb => intro acc h; exact ihb _ (iha acc h)

private theorem dbVarsOfList_nodup : ∀ (es : List (DenseExpr p)) (acc : Array VarId),
    DbNodupA acc → DbNodupA (dbVarsOfList es acc) := by
  intro es
  induction es with
  | nil => intro acc h; exact h
  | cons e rest ih => intro acc h; exact ih _ (dbVarsOf_nodup e acc h)

private theorem dbNodupA_empty : DbNodupA (#[] : Array VarId) := by
  intro a b ha; simp at ha

theorem dbVarsOf_nodupIdx (e : DenseExpr p) : DbNodupIdx (dbVarsOf e #[]) :=
  dbNodupIdx_of _ (dbVarsOf_nodup e #[] dbNodupA_empty)

theorem dbBiVars_nodupIdx (bi : BusInteraction (DenseExpr p)) : DbNodupIdx (dbBiVars bi) :=
  dbNodupIdx_of _ (dbVarsOfList_nodup bi.payload _ (dbVarsOf_nodup bi.multiplicity #[]
    dbNodupA_empty))

/-! ### The register file's width -/

private theorem dbFoldMaxL_ge : ∀ (l : List VarId) (m : ℕ),
    m ≤ l.foldl (fun b v => max b (v.index + 1)) m := by
  intro l
  induction l with
  | nil => intro m; exact Nat.le_refl m
  | cons v rest ih =>
    intro m
    rw [List.foldl_cons]
    exact le_trans (le_max_left m (v.index + 1)) (ih _)

private theorem dbFoldMaxL_mem : ∀ (l : List VarId) (m : ℕ), ∀ i ∈ l,
    i.index < l.foldl (fun b v => max b (v.index + 1)) m := by
  intro l
  induction l with
  | nil => intro m i hi; simp at hi
  | cons v rest ih =>
    intro m i hi
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact lt_of_lt_of_le (lt_of_lt_of_le (by omega) (le_max_right m (i.index + 1)))
        (dbFoldMaxL_ge rest _)
    · exact ih _ i hi'

/-! ### The context

Everything the target loop reads is built once. `DbCtxGood` is what a satisfying assignment makes
true of it; `DbCtxShape` what holds unconditionally. -/

theorem dbGetD_map {α : Type u} {β : Type v} (as : Array α) (f : α → β) (pos : ℕ) (dflt : β) :
    (as.map f).getD pos dflt = if h : pos < as.size then f as[pos] else dflt := by
  rcases Nat.lt_or_ge pos as.size with h | h
  · rw [dif_pos h, dbGetD_lt _ _ _ (by simpa using h), Array.getElem_map]
  · rw [dif_neg (by omega), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using h)]
    rfl

/-- The cache resolves each fact about the interaction it was built from. -/
theorem dbPreOne_preOf {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (bi : BusInteraction (DenseExpr p)) (hbc : DbBusCacheOk facts bc bi.busId)
    (vars : Array VarId) :
    DbBiPreOf facts bi (dbPreOne facts bc bi vars) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [dbPreOne, hbc.byteSpec] at hb
    split at hb
    · rcases hspec : facts.byteXorSpec bi.busId with _ | spec
      · rw [hspec] at hb; simp at hb
      · rw [hspec] at hb
        simp only [Option.bind_some] at hb
        rcases hdec : spec.decode bi.payload with _ | t
        · rw [hdec] at hb; simp at hb
        · rw [hdec] at hb
          simp only [Option.map_some, Option.some.injEq] at hb
          subst hb
          exact ⟨hspec, t.1, hdec, rfl⟩
    · simp at hb
  · intro h
    simp only [dbPreOne, hbc.varRange, Bool.and_eq_true] at h
    exact h.2
  · intro t ht
    simp only [dbPreOne, hbc.tuple] at ht
    split_ifs at ht
    exact ht
  · intro t ht
    simp only [dbPreOne] at ht
    split_ifs at ht <;> exact ht

/-- The `k`-th entry of a phase that pushes one element per step. -/
theorem dbPushGetD {α : Type u} (out : Array α) (x : α) (k : ℕ) (dflt : α) (h : k < out.size) :
    (out.push x).getD k dflt = out.getD k dflt := by
  rw [dbGetD_lt _ _ _ (by rw [Array.size_push]; omega), dbGetD_lt _ _ _ h,
    Array.getElem_push_lt h]

theorem dbPushGetD_at {α : Type u} (out : Array α) (x : α) (k : ℕ) (dflt : α) (hk : k = out.size) :
    (out.push x).getD k dflt = x := by
  subst hk
  rw [dbGetD_lt _ _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

/-- Every operand's variables are among the item's recorded variables, so the compiled engine can
    resolve each operand against the plan's keys. -/
def DbItemVars (it : DbItem p) (vs : Array VarId) : Prop :=
  match it with
  | .always => True
  | .zero e => ∀ v ∈ e.vars, v ∈ vs
  | .varRange m x w =>
    (∀ v ∈ m.vars, v ∈ vs) ∧ (∀ v ∈ x.vars, v ∈ vs) ∧ (∀ v ∈ w.vars, v ∈ vs)
  | .varRangeConst m x _ => (∀ v ∈ m.vars, v ∈ vs) ∧ (∀ v ∈ x.vars, v ∈ vs)
  | .tupleRange m x y _ _ =>
    (∀ v ∈ m.vars, v ∈ vs) ∧ (∀ v ∈ x.vars, v ∈ vs) ∧ (∀ v ∈ y.vars, v ∈ vs)
  | .fixedRange m v _ => (∀ z ∈ m.vars, z ∈ vs) ∧ (∀ z ∈ v.vars, z ∈ vs)
  | .byte m o1 o2 r _ _ =>
    (∀ v ∈ m.vars, v ∈ vs) ∧ (∀ v ∈ o1.vars, v ∈ vs) ∧ (∀ v ∈ o2.vars, v ∈ vs) ∧
      (∀ v ∈ r.vars, v ∈ vs)
  | .fallback _ m payload =>
    (∀ v ∈ m.vars, v ∈ vs) ∧ ∀ e ∈ payload, ∀ v ∈ e.vars, v ∈ vs

/-- An item with no variables at all satisfies `DbItemVars` against any record. -/
theorem dbItemVars_of_empty (it : DbItem p) (vs : Array VarId) (h : DbItemVars it #[]) :
    DbItemVars it vs := by
  cases it <;> simp only [DbItemVars] at h ⊢
  · exact fun v hv => absurd (h v hv) (by simp)
  · exact ⟨fun v hv => absurd (h.1 v hv) (by simp),
      fun v hv => absurd (h.2.1 v hv) (by simp), fun v hv => absurd (h.2.2 v hv) (by simp)⟩
  · exact ⟨fun v hv => absurd (h.1 v hv) (by simp), fun v hv => absurd (h.2 v hv) (by simp)⟩
  · exact ⟨fun v hv => absurd (h.1 v hv) (by simp),
      fun v hv => absurd (h.2.1 v hv) (by simp), fun v hv => absurd (h.2.2 v hv) (by simp)⟩
  · exact ⟨fun v hv => absurd (h.1 v hv) (by simp), fun v hv => absurd (h.2 v hv) (by simp)⟩
  · exact ⟨fun v hv => absurd (h.1 v hv) (by simp),
      fun v hv => absurd (h.2.1 v hv) (by simp), fun v hv => absurd (h.2.2.1 v hv) (by simp),
      fun v hv => absurd (h.2.2.2 v hv) (by simp)⟩
  · exact ⟨fun v hv => absurd (h.1 v hv) (by simp),
      fun e he v hv => absurd (h.2 e he v hv) (by simp)⟩

/-- What a satisfying assignment makes true of the once-built context. -/
structure DbCtxGood {p : ℕ} {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) : Prop where
  /-- Every domain contains the value the assignment gives its variable. -/
  tab : DbTabSound p denv ctx.T
  /-- The variable-free obligations hold, so the pass does not take the vacuous exit. -/
  constOk : ctx.constOk = true
  csItem : ∀ (pos : ℕ) (regs : Array ℕ), DbRegsAgreeA denv regs (ctx.csVars.getD pos #[]) →
    dbItemOk facts regs (ctx.csItems.getD pos DbItem.always) = true
  csVarless : ∀ item ∈ ctx.csVarlessItems, ∀ regs : Array ℕ, dbItemOk facts regs item = true
  biItem : ∀ (pos : ℕ) (regs : Array ℕ), DbRegsAgreeA denv regs (ctx.biVars.getD pos #[]) →
    dbItemOk facts regs (ctx.biItems.getD pos DbItem.always) = true
  csItemVars : ∀ pos, DbItemVars (ctx.csItems.getD pos DbItem.always) (ctx.csVars.getD pos #[])
  csVarlessItemVars : ∀ item ∈ ctx.csVarlessItems, DbItemVars item #[]
  biItemVars : ∀ pos, DbItemVars (ctx.biItems.getD pos DbItem.always) (ctx.biVars.getD pos #[])

/-- What holds of the context whether or not anything satisfies the system. -/
structure DbCtxShape {p : ℕ} (ctx : DbCtx p) : Prop where
  csNodup : ∀ pos, DbNodupIdx (ctx.csVars.getD pos #[])
  csNv : ∀ pos, ∀ i ∈ ctx.csVars.getD pos #[], i.index < ctx.nv
  biNodup : ∀ pos, DbNodupIdx (ctx.biVars.getD pos #[])
  biNv : ∀ pos, ∀ i ∈ ctx.biVars.getD pos #[], i.index < ctx.nv

private theorem dbNodupIdx_empty : DbNodupIdx (#[] : Array VarId) := by
  intro a b ha; simp at ha

/-! ### Gathering

The gather records each item's variables alongside it, so the scan can place the item at the depth
of its innermost key. -/

/-- Each gathered item holds whenever the registers carry the assignment on the variables recorded
    for it. -/
structure DbGatherOk {p : ℕ} {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (g : DbGather p) : Prop where
  size : g.ivars.size = g.items.size
  ok : ∀ i, i < g.items.size → ∀ regs : Array ℕ,
    DbRegsAgreeA denv regs (g.ivars.getD i #[]) →
    dbItemOk facts regs (g.items.getD i DbItem.always) = true
  vars : ∀ i, i < g.items.size →
    DbItemVars (g.items.getD i DbItem.always) (g.ivars.getD i #[])

private theorem dbGatherCsAt_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) (hgood : DbCtxGood facts denv ctx)
    (mark : Array ℕ) (gen : ℕ) (g : DbGather p) (pos : ℕ) (hg : DbGatherOk facts denv g) :
    DbGatherOk facts denv (dbGatherCsAt ctx mark gen g pos) := by
  obtain ⟨hsz, hok, hvars⟩ := hg
  rw [dbGatherCsAt]
  split
  · split
    · refine ⟨by simp [hsz], fun i hi regs hagree => ?_, fun i hi => ?_⟩
      · simp only [Array.size_push] at hi
        rcases Nat.lt_or_ge i g.items.size with hlt | hge
        · rw [dbPushGetD _ _ _ _ (show i < g.ivars.size by omega)] at hagree
          rw [dbPushGetD _ _ _ _ (show i < g.items.size by omega)]
          exact hok i hlt regs hagree
        · rw [dbPushGetD_at _ _ i _ (show i = g.ivars.size by omega)] at hagree
          rw [dbPushGetD_at _ _ i _ (show i = g.items.size by omega)]
          exact hgood.csItem pos regs hagree
      · simp only [Array.size_push] at hi
        rcases Nat.lt_or_ge i g.items.size with hlt | hge
        · rw [dbPushGetD _ _ _ _ (show i < g.ivars.size by omega),
            dbPushGetD _ _ _ _ (show i < g.items.size by omega)]
          exact hvars i hlt
        · rw [dbPushGetD_at _ _ i _ (show i = g.ivars.size by omega),
            dbPushGetD_at _ _ i _ (show i = g.items.size by omega)]
          exact hgood.csItemVars pos
    · exact ⟨hsz, hok, hvars⟩
  · exact ⟨hsz, hok, hvars⟩

private theorem dbGatherBiAt_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) (hgood : DbCtxGood facts denv ctx)
    (mark : Array ℕ) (gen : ℕ) (g : DbGather p) (pos : ℕ) (hg : DbGatherOk facts denv g) :
    DbGatherOk facts denv (dbGatherBiAt ctx mark gen g pos) := by
  obtain ⟨hsz, hok, hvars⟩ := hg
  rw [dbGatherBiAt]
  split
  · refine ⟨by simp [hsz], fun i hi regs hagree => ?_, fun i hi => ?_⟩
    · simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i g.items.size with hlt | hge
      · rw [dbPushGetD _ _ _ _ (show i < g.ivars.size by omega)] at hagree
        rw [dbPushGetD _ _ _ _ (show i < g.items.size by omega)]
        exact hok i hlt regs hagree
      · rw [dbPushGetD_at _ _ i _ (show i = g.ivars.size by omega)] at hagree
        rw [dbPushGetD_at _ _ i _ (show i = g.items.size by omega)]
        exact hgood.biItem pos regs hagree
    · simp only [Array.size_push] at hi
      rcases Nat.lt_or_ge i g.items.size with hlt | hge
      · rw [dbPushGetD _ _ _ _ (show i < g.ivars.size by omega),
          dbPushGetD _ _ _ _ (show i < g.items.size by omega)]
        exact hvars i hlt
      · rw [dbPushGetD_at _ _ i _ (show i = g.ivars.size by omega),
          dbPushGetD_at _ _ i _ (show i = g.items.size by omega)]
        exact hgood.biItemVars pos
  · exact ⟨hsz, hok, hvars⟩

theorem dbGather_ok [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ctx : DbCtx p) (hgood : DbCtxGood facts denv ctx)
    (hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size)
    (mark : Array ℕ) (gen : ℕ) (xs : Array VarId) :
    DbGatherOk facts denv (dbGather ctx mark gen xs) := by
  rw [dbGather]
  refine dbFoldlInv (fun g : DbGather p => DbGatherOk facts denv g)
    _ _ (fun g v _ hg => ?_) _ ⟨hvl, fun i hi regs _ => ?_, fun i hi => ?_⟩
  · dsimp only
    refine dbFoldlInv (fun g : DbGather p => DbGatherOk facts denv g)
      _ _ (fun g' pos _ hg' => dbGatherBiAt_ok facts denv ctx hgood mark gen g' pos hg') _ ?_
    exact dbFoldlInv (fun g : DbGather p => DbGatherOk facts denv g)
      _ _ (fun g' pos _ hg' => dbGatherCsAt_ok facts denv ctx hgood mark gen g' pos hg') _ hg
  · exact hgood.csVarless _ (by rw [dbGetD_lt _ _ DbItem.always hi]; exact Array.getElem_mem hi)
      regs
  · exact dbItemVars_of_empty _ _ (hgood.csVarlessItemVars _
      (by rw [dbGetD_lt _ _ DbItem.always hi]; exact Array.getElem_mem hi))

/-! ### Item levels -/

theorem dbKeyPos?_spec (keys : Array VarId) (v : VarId) :
    ∀ (k j : ℕ), dbKeyPos? keys v k = some j → ∃ h : j < keys.size, keys[j] = v := by
  intro k
  induction hn : keys.size - k generalizing k with
  | zero => intro j h; rw [dbKeyPos?, dif_neg (by omega)] at h; simp at h
  | succ n ih =>
    intro j h
    have hk : k < keys.size := by omega
    rw [dbKeyPos?, dif_pos hk] at h
    split at h
    · next heq =>
      have hjk : j = k := (Option.some.inj h).symm
      subst hjk
      exact ⟨hk, eq_of_beq heq⟩
    · exact ih (k + 1) (by omega) j h

/-- Every variable of an item with a level is a key no deeper than that level. -/
theorem dbItemLevel?_spec (keys : Array VarId) (vs : Array VarId) (l : ℕ)
    (h : dbItemLevel? keys vs = some l) :
    ∀ v ∈ vs, ∃ j, j ≤ l ∧ ∃ hj : j < keys.size, keys[j] = v := by
  rw [dbItemLevel?] at h
  have key : ∀ (li : List VarId) (acc : Option ℕ) (l' : ℕ),
      li.foldl (fun m v => match m, dbKeyPos? keys v 0 with
        | some a, some b => some (max a b) | _, _ => none) acc = some l' →
      (∃ a, acc = some a ∧ a ≤ l') ∧
        ∀ v ∈ li, ∃ j, j ≤ l' ∧ ∃ hj : j < keys.size, keys[j] = v := by
    intro li
    induction li with
    | nil => intro acc l' hf; exact ⟨⟨l', hf, le_refl _⟩, fun v hv => by simp at hv⟩
    | cons x rest ih =>
      intro acc l' hf
      simp only [List.foldl_cons] at hf
      rcases hacc : acc with _ | a
      · rw [hacc] at hf
        have : ∀ (li' : List VarId) (l'' : ℕ),
            li'.foldl (fun m v => match m, dbKeyPos? keys v 0 with
              | some a, some b => some (max a b) | _, _ => none) none ≠ some l'' := by
          intro li'
          induction li' with
          | nil => intro l'' h''; simp at h''
          | cons y r ihy => intro l'' h''; exact ihy l'' (by simpa using h'')
        exact absurd hf (this _ _)
      · rw [hacc] at hf
        rcases hkx : dbKeyPos? keys x 0 with _ | b
        · rw [hkx] at hf
          have : ∀ (li' : List VarId) (l'' : ℕ),
              li'.foldl (fun m v => match m, dbKeyPos? keys v 0 with
                | some a, some b => some (max a b) | _, _ => none) none ≠ some l'' := by
            intro li'
            induction li' with
            | nil => intro l'' h''; simp at h''
            | cons y r ihy => intro l'' h''; exact ihy l'' (by simpa using h'')
          exact absurd hf (this _ _)
        · rw [hkx] at hf
          obtain ⟨⟨a', ha', hle⟩, hrest⟩ := ih (some (max a b)) l' hf
          refine ⟨⟨a, rfl, le_trans (le_trans (le_max_left a b)
            (le_of_eq (Option.some.inj ha'))) hle⟩, fun v hv => ?_⟩
          rcases List.mem_cons.mp hv with rfl | hv'
          · obtain ⟨hj, hkj⟩ := dbKeyPos?_spec keys v 0 b hkx
            exact ⟨b, le_trans (le_trans (le_max_right a b)
              (le_of_eq (Option.some.inj ha'))) hle, hj, hkj⟩
          · exact hrest v hv'
  intro v hv
  rw [← Array.foldl_toList] at h
  exact (key vs.toList (some 0) l h).2 v (by simpa using hv)

/-- The level pass keeps each item's obligation and pins it to a depth where its variables are
    already bound. -/
theorem dbLevelItems_spec (keys : Array VarId) (items : Array (DbItem p))
    (ivars : Array (Array VarId)) :
    ∀ (k : ℕ) (out : Array (DbItem p)) (lev : Array ℕ), out.size = k → lev.size = k →
      k ≤ items.size →
      (∀ i, i < k → out.getD i DbItem.always = DbItem.always ∨
        (out.getD i DbItem.always = items.getD i DbItem.always ∧
          dbItemLevel? keys (ivars.getD i #[]) = some (lev.getD i 0))) →
      (dbLevelItems keys items ivars k out lev).1.size = items.size ∧
      (dbLevelItems keys items ivars k out lev).2.size = items.size ∧
      ∀ i, i < items.size →
        (dbLevelItems keys items ivars k out lev).1.getD i DbItem.always = DbItem.always ∨
        ((dbLevelItems keys items ivars k out lev).1.getD i DbItem.always
            = items.getD i DbItem.always ∧
          dbItemLevel? keys (ivars.getD i #[])
            = some ((dbLevelItems keys items ivars k out lev).2.getD i 0)) := by
  intro k
  induction hn : items.size - k generalizing k with
  | zero =>
    intro out lev ho hl hk hinv
    rw [dbLevelItems, dif_neg (by omega)]
    exact ⟨by simp only []; omega, by simp only []; omega, fun i hi => hinv i (by omega)⟩
  | succ n ih =>
    intro out lev ho hl hk hinv
    have hlt : k < items.size := by omega
    rw [dbLevelItems, dif_pos hlt]
    have hstep : ∀ (x : DbItem p) (y : ℕ),
        (x = items.getD k DbItem.always ∧ dbItemLevel? keys (ivars.getD k #[]) = some y) ∨
          x = DbItem.always →
        ∀ i, i < k + 1 → (out.push x).getD i DbItem.always = DbItem.always ∨
          ((out.push x).getD i DbItem.always = items.getD i DbItem.always ∧
            dbItemLevel? keys (ivars.getD i #[]) = some ((lev.push y).getD i 0)) := by
      intro x y hx i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · rw [dbPushGetD _ _ _ _ (by omega), dbPushGetD _ _ _ _ (by omega)]
        exact hinv i hik
      · have hik' : i = k := by omega
        subst hik'
        rw [dbPushGetD_at out _ i _ (by omega), dbPushGetD_at lev _ i _ (by omega)]
        rcases hx with ⟨h1, h2⟩ | h1
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl h1
    split
    · next l hlv =>
      refine ih (k + 1) (by omega) _ _ (by simp [ho]) (by simp [hl]) (by omega)
        (hstep _ l (Or.inl ⟨by rw [dbGetD_lt _ _ _ hlt], hlv⟩))
    · exact ih (k + 1) (by omega) _ _ (by simp [ho]) (by simp [hl]) (by omega)
        (hstep _ 0 (Or.inr rfl))

/-! ### Plans

`dbRunPlan` threads a register file through the run, so a plan's answer is a function of whatever
file it inherits; `DbPlanSound` quantifies over that. -/

/-- The forced list one plan contributes, as a function of the register file it starts from. -/
def dbRunPlanNew {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ) (regs0 : Array ℕ)
    (plan : DbPlan p) : List (VarId × ZMod p) :=
  match plan with
  | .done forced => forced
  | .scan keys doms items ilev constOk =>
    let regs0 := if regs0.size == nv then regs0 else Array.replicate nv 0
    if !constOk then dbZeroAll keys
    else
      let res := dbScanBox facts items ilev (keys.map (fun v => v.index)) doms regs0
      if !res.started then dbZeroAll keys
      else if res.live == 0 then []
      else dbForcedOfMask p keys res.vals res.alive 0

theorem dbRunPlan_snd {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (st : Array ℕ × List (List (VarId × ZMod p))) (plan : DbPlan p) :
    (dbRunPlan facts nv st plan).2 = dbRunPlanNew facts nv st.1 plan :: st.2 := by
  cases plan with
  | done forced => rfl
  | scan keys doms items ilev constOk =>
    simp only [dbRunPlan, dbRunPlanNew]
    split_ifs <;> rfl

/-- The forced list one plan contributes on the compiled engine. -/
def dbRunPlanYNew {bs : BusSemantics p} (facts : BusFacts p bs) (plan : DbPlan p) :
    List (VarId × ZMod p) :=
  match plan with
  | .done forced => forced
  | .scan keys doms items ilev constOk =>
    if !constOk then dbZeroAll keys
    else if keys.isEmpty then []
    else
      let kks := keys.size
      let C := dbCompilePlan (keys.map (fun v => v.index)) kks items ilev
      let r := dbScanDepth facts C.items C.ops C.lstart doms kks 0
        (Array.replicate kks (0 : ℕ)) #[] #[] 0 false
      if !r.started then dbZeroAll keys
      else if r.live == 0 then []
      else dbForcedOfMask p keys r.vals r.alive 0

theorem dbRunPlanY_head {bs : BusSemantics p} (facts : BusFacts p bs)
    (out : List (List (VarId × ZMod p))) (plan : DbPlan p) :
    dbRunPlanY facts out plan = dbRunPlanYNew facts plan :: out := by
  cases plan with
  | done forced => rfl
  | scan keys doms items ilev constOk =>
    simp only [dbRunPlanY, dbRunPlanYNew]
    split_ifs <;> rfl

theorem dbRunPlanH_snd {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (st : Array ℕ × List (List (VarId × ZMod p))) (plan : DbPlan p) :
    (dbRunPlanH facts nv st plan).2 = dbRunPlanNew facts nv st.1 plan :: st.2 ∨
    (dbRunPlanH facts nv st plan).2 = dbRunPlanYNew facts plan :: st.2 := by
  cases plan with
  | done forced => exact Or.inl rfl
  | scan keys doms items ilev constOk =>
    rw [dbRunPlanH]
    split
    · exact Or.inl (by rw [dbRunPlan_snd])
    · exact Or.inr (by rw [dbRunPlanY_head])

/-- A plan answers soundly on either engine: every constant it forces holds in every satisfying
    assignment (the boxed engine's answer additionally quantifies over the register file it
    inherits). -/
def DbPlanSound {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (d : DenseConstraintSystem p) (plan : DbPlan p) : Prop :=
  (∀ (regs0 : Array ℕ), ∀ f ∈ dbRunPlanNew facts nv regs0 plan,
    ∀ denv, d.satisfies bs denv → denv f.1 = f.2) ∧
  (∀ f ∈ dbRunPlanYNew facts plan, ∀ denv, d.satisfies bs denv → denv f.1 = f.2)

private theorem dbKeys_getD (xs : Array VarId) (j : ℕ) (hj : j < xs.size) :
    (xs.map (fun v => v.index)).getD j 0 = xs[j].index := by
  rw [dbGetD_map, dif_pos hj]

/-- The sweep of a preflighted box ends with a good mask. -/
theorem dbScanBox_good [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (items : Array (DbItem p)) (ilev : Array ℕ) (xs : Array VarId)
    (doms : Array DbDom) (regs : Array ℕ) (hnodup : DbNodupIdx xs)
    (hcov : ∀ i ∈ xs, i.index < regs.size)
    (hmem : ∀ k, ∀ hk : k < xs.size, DbDomMem p (doms.getD k (.range 0)) (denv xs[k]).val)
    (hitems : ∀ (dd : ℕ) (regs' : Array ℕ), dd < xs.size →
      (∀ d', d' ≤ dd → ∀ h : d' < xs.size, regs'.getD xs[d'].index 0 = (denv xs[d']).val) →
      dbAllOkLev facts items ilev dd regs' 0 = true)
    (hempty : xs.isEmpty = true → dbAllOkLev facts items ilev 0 regs 0 = true) :
    DbScanGood denv (xs.map (fun v => v.index))
      (dbScanBox facts items ilev (xs.map (fun v => v.index)) doms regs) := by
  have hcov' : ∀ d', d' < (xs.map (fun v => v.index)).size →
      (xs.map (fun v => v.index)).getD d' 0 < regs.size := by
    intro d' hd'
    rw [Array.size_map] at hd'
    rw [dbKeys_getD xs d' hd']
    exact hcov xs[d'] (Array.getElem_mem hd')
  rw [dbScanBox]
  split
  · next hemp =>
    have hxs : xs.isEmpty = true := by
      have hz : (xs.map (fun v => v.index)).size = 0 := by simpa [Array.isEmpty] using hemp
      rw [Array.size_map] at hz
      simp [Array.isEmpty, hz]
    rw [if_pos (hempty hxs)]
    exact ⟨rfl, Or.inl rfl⟩
  · next hemp =>
    have hsz : 0 < (xs.map (fun v => v.index)).size := by
      rcases Nat.eq_zero_or_pos (xs.map (fun v => v.index)).size with h | h
      · exact absurd (by simp [Array.isEmpty, h]) hemp
      · exact h
    have hmem' : ∀ dd, dd < (xs.map (fun v => v.index)).size →
        DbDomMem p (doms.getD dd (.range 0))
          (denv ⟨(xs.map (fun v => v.index)).getD dd 0⟩).val := by
      intro dd hdd
      rw [Array.size_map] at hdd
      rw [dbKeys_getD xs dd hdd]
      exact hmem dd hdd
    have hdist : ∀ a b, a < (xs.map (fun v => v.index)).size →
        b < (xs.map (fun v => v.index)).size →
        (xs.map (fun v => v.index)).getD a 0 = (xs.map (fun v => v.index)).getD b 0 → a = b := by
      intro a b ha hb hab
      rw [Array.size_map] at ha hb
      rw [dbKeys_getD xs a ha, dbKeys_getD xs b hb] at hab
      exact hnodup a b ha hb (by
        rw [dbGetD_lt xs a ⟨0⟩ ha, dbGetD_lt xs b ⟨0⟩ hb]; exact hab)
    have hitems' : ∀ (dd : ℕ) (regs' : Array ℕ), dd < (xs.map (fun v => v.index)).size →
        (∀ d', d' ≤ dd → regs'.getD ((xs.map (fun v => v.index)).getD d' 0) 0
          = (denv ⟨(xs.map (fun v => v.index)).getD d' 0⟩).val) →
        dbAllOkLev facts items ilev dd regs' 0 = true := by
      intro dd regs' hdd hreg
      rw [Array.size_map] at hdd
      refine hitems dd regs' hdd (fun d' hd' h => ?_)
      have := hreg d' hd'
      rw [dbKeys_getD xs d' h] at this
      exact this
    refine dbScanLoop_reach facts items ilev _ doms denv
      (fun dd => if h : dd < (xs.map (fun v => v.index)).size then (hmem' dd h).choose else 0)
      hdist (fun dd hdd => ?_) hitems' 0 _ _ 0 _ regs #[] #[] 0 false rfl rfl hsz rfl
      (Nat.zero_le _) hcov' (fun d' hd' => absurd hd' (by omega))
    dsimp only
    rw [dif_pos hdd]
    exact (hmem' dd hdd).choose_spec

/-- What the scan's answer forces, given a good mask. -/
theorem dbScanAnswer_sound [NeZero p] (denv : VarId → ZMod p) (xs : Array VarId) (st : DbScanSt)
    (hgoodst : DbScanGood denv (xs.map (fun v => v.index)) st) :
    ∀ f ∈ (if !st.started then dbZeroAll xs
      else if st.live == 0 then [] else dbForcedOfMask p xs st.vals st.alive 0),
      denv f.1 = f.2 := by
  obtain ⟨hstarted, hlive⟩ := hgoodst
  rw [hstarted]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hl : st.live == 0
  · rw [if_pos hl]; intro f hf; simp at hf
  · rw [if_neg hl]
    rcases hlive with h0 | hag
    · exact absurd (by simpa using h0) hl
    · refine dbForcedOfMask_sound denv xs st.vals st.alive (fun j hj hal => ?_) 0
      have hj' := hag j (by rwa [Array.size_map]) hal
      rwa [dbKeys_getD xs j hj] at hj'

/-! ### The reordered keys

The sort is untrusted: the plan keeps its output only when it is still a distinct sub-collection of
the target's keys, and re-reads the domains from the table. -/

theorem dbMemVar_spec (b : Array VarId) (v : VarId) :
    ∀ k, dbMemVar b v k = true → v ∈ b := by
  intro k
  induction hn : b.size - k generalizing k with
  | zero => intro h; rw [dbMemVar, dif_neg (by omega)] at h; simp at h
  | succ n ih =>
    intro h
    have hk : k < b.size := by omega
    rw [dbMemVar, dif_pos hk, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [← eq_of_beq h]; exact Array.getElem_mem hk
    · exact ih (k + 1) (by omega) h

theorem dbSubsetVars_spec (a b : Array VarId) :
    ∀ k, dbSubsetVars a b k = true → ∀ j, k ≤ j → ∀ hj : j < a.size, a[j] ∈ b := by
  intro k
  induction hn : a.size - k generalizing k with
  | zero => intro _ j hkj hj; omega
  | succ n ih =>
    intro h j hkj hj
    have hk : k < a.size := by omega
    rw [dbSubsetVars, dif_pos hk, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · exact dbMemVar_spec b a[k] 0 h.1
    · exact ih (k + 1) (by omega) h.2 j (by omega) hj

theorem dbNodupVars_spec (a : Array VarId) :
    ∀ k, dbNodupVars a k = true → ∀ i j, k ≤ i → i < j → ∀ hj : j < a.size,
      ∀ hi : i < a.size, a[i] ≠ a[j] := by
  intro k
  induction hn : a.size - k generalizing k with
  | zero => intro _ i j hki hij hj hi; omega
  | succ n ih =>
    intro h i j hki hij hj hi
    have hk : k < a.size := by omega
    rw [dbNodupVars, dif_pos hk, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases Nat.eq_or_lt_of_le hki with rfl | hlt
    · intro heq
      refine absurd ?_ (by simp [h.1] : ¬ (dbMemVar a a[k] (k + 1) = true))
      have hmem : ∀ (m : ℕ), m ≤ j → a[k] = a[j] → dbMemVar a a[k] m = true := by
        intro m
        induction hnm : j - m generalizing m with
        | zero =>
          intro hmj heq'
          have hmj' : m = j := by omega
          subst hmj'
          rw [dbMemVar, dif_pos hj, Bool.or_eq_true]
          exact Or.inl (beq_iff_eq.mpr heq'.symm)
        | succ n' ihm =>
          intro hmj heq'
          have hms : m < a.size := by omega
          rw [dbMemVar, dif_pos hms, Bool.or_eq_true]
          by_cases hb : a[m] == a[k]
          · exact Or.inl hb
          · refine Or.inr (ihm (m + 1) (by omega) ?_ heq')
            rcases Nat.eq_or_lt_of_le hmj with rfl | hmlt
            · exact absurd (beq_iff_eq.mpr heq'.symm) hb
            · omega
      exact hmem (k + 1) (by omega) heq
    · exact ih (k + 1) (by omega) h.2 i j (by omega) hij hj hi

/-- What the ordered keys give the scan: they are distinct, they are keys of the target, and their
    domains are the table's. -/
theorem dbOrderKeys_spec (T : DbTab p) (xs : Array VarId) (doms : Array DbDom) :
    ∀ (ks : Array VarId) (ds : Array DbDom), dbOrderKeys T xs doms = (ks, ds) →
      dbDomsOf T xs = some doms → DbNodupIdx xs →
      DbNodupIdx ks ∧ (∀ v ∈ ks, v ∈ xs) ∧ ks.size = xs.size ∧
        ∀ k, ∀ hk : k < ks.size, T.get ks[k].index = some (ds.getD k (.range 0)) := by
  intro ks ds hord hdoms hnodup
  have hid : ∀ (ks' : Array VarId) (ds' : Array DbDom), (ks', ds') = (xs, doms) →
      DbNodupIdx ks' ∧ (∀ v ∈ ks', v ∈ xs) ∧ ks'.size = xs.size ∧
        ∀ k, ∀ hk : k < ks'.size, T.get ks'[k].index = some (ds'.getD k (.range 0)) := by
    intro ks' ds' h
    have h1 : ks' = xs := congrArg Prod.fst h
    have h2 : ds' = doms := congrArg Prod.snd h
    subst h1; subst h2
    exact ⟨hnodup, fun v hv => hv, rfl, fun k hk => dbDomsOf_get T ks' ds' hdoms k hk⟩
  simp only [dbOrderKeys] at hord
  split at hord
  · exact hid ks ds hord.symm
  · split at hord
    · next hchk =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨hsz, hsub⟩, _⟩, hnd⟩ := hchk
      split at hord
      · next ds0 hds0 =>
        have h1 : ks = _ := congrArg Prod.fst hord.symm
        have h2 : ds = ds0 := congrArg Prod.snd hord.symm
        subst h1; subst h2
        refine ⟨fun a b ha hb hab => ?_, fun v hv => ?_, hsz, fun k hk =>
          dbDomsOf_get T _ _ hds0 k hk⟩
        · by_contra hne
          rcases Nat.lt_or_ge a b with h | h
          · exact dbNodupVars_spec _ 0 hnd a b (Nat.zero_le _) h hb ha
              (by rw [← dbGetD_lt _ _ (⟨0⟩ : VarId) ha, ← dbGetD_lt _ _ (⟨0⟩ : VarId) hb]
                  exact dbVarId_eq _ _ hab)
          · have hlt : b < a := by omega
            exact dbNodupVars_spec _ 0 hnd b a (Nat.zero_le _) hlt ha hb
              (by rw [← dbGetD_lt _ _ (⟨0⟩ : VarId) hb, ← dbGetD_lt _ _ (⟨0⟩ : VarId) ha]
                  exact dbVarId_eq _ _ hab.symm)
        · obtain ⟨j, hj, hvj⟩ := Array.getElem_of_mem hv
          rw [← hvj]
          exact dbSubsetVars_spec _ xs 0 hsub j (Nat.zero_le _) hj
      · exact hid ks ds hord.symm
    · exact hid ks ds hord.symm

/-! ### The compiled engine

Soundness only: whatever `dbRunPlanY` forces must hold in every satisfying assignment. The mask
is an intersection over survivors, so it suffices that (i) the assignment's own point is never
skipped — the pivot lemmas say a satisfying point always lands on the pivot's root — and (ii) at
that point every compiled item test passes, which reduces to the source item's `dbItemOk` through
the operand-evaluation bridge. Junk survivors and dropped filters only weaken the mask. -/

/-- Slot registers agree with the assignment on the ordered keys up to depth `dd`. -/
def DbSRegs (denv : VarId → ZMod p) (ks : Array VarId) (sregs : Array ℕ) (dd : ℕ) : Prop :=
  ∀ j, j ≤ dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val

/-- The variable's slot, resolved through the mapped key indices. -/
theorem dbSlotIdx_at (ks : Array VarId) (hknd : DbNodupIdx ks) (j : ℕ) (hj : j < ks.size) :
    dbSlotIdx (ks.map (fun v => v.index)) ks[j].index 0 = j := by
  have hmapv : ∀ (k : ℕ), ∀ hk : k < ks.size,
      (ks.map (fun v => v.index))[k]'(by simpa using hk) = ks[k].index := by
    intro k hk
    rw [Array.getElem_map]
  have key : ∀ (m k : ℕ), j - k ≤ m → k ≤ j →
      dbSlotIdx (ks.map (fun v => v.index)) ks[j].index k = j := by
    intro m
    induction m with
    | zero =>
      intro k hm hk
      have hkj : k = j := by omega
      subst hkj
      rw [dbSlotIdx, dif_pos (by simpa using hj)]
      rw [if_pos (by rw [hmapv k hj]; exact beq_self_eq_true _)]
    | succ m ih =>
      intro k hm hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hkj
      · rw [dbSlotIdx, dif_pos (by simpa using hj)]
        rw [if_pos (by rw [hmapv k hj]; exact beq_self_eq_true _)]
      · have hks : k < ks.size := by omega
        rw [dbSlotIdx, dif_pos (by simpa using hks)]
        rw [if_neg ?_, ih (k + 1) (by omega) (by omega)]
        rw [hmapv k hks]
        intro hbeq
        have hidx : (ks.getD k ⟨0⟩).index = (ks.getD j ⟨0⟩).index := by
          rw [dbGetD_lt _ _ _ hks, dbGetD_lt _ _ _ hj]
          exact eq_of_beq hbeq
        exact absurd (hknd k j hks hj hidx) (by omega)
  exact key j 0 (by omega) (Nat.zero_le _)

/-- The denotation of one monomial: its coefficient times its slots' key variables. -/
def dbTermDenote (denv : VarId → ZMod p) (ks : Array VarId) (t : DbTerm) : ZMod p :=
  (t.coef : ZMod p) * (t.slotsArr.toList.map (fun s => denv (ks.getD s ⟨0⟩))).prod

def dbTermsDenote (denv : VarId → ZMod p) (ks : Array VarId) (ts : Array DbTerm) : ZMod p :=
  (ts.toList.map (dbTermDenote denv ks)).sum

/-- Well-formed terms: coefficients below `p`, slots bounded by the depth and the key count. -/
def DbTermsWF (pp : ℕ) (ks : Array VarId) (dd : ℕ) (ts : Array DbTerm) : Prop :=
  ∀ t ∈ ts, t.coef < pp ∧ ∀ s ∈ t.slotsArr, s ≤ dd ∧ s < ks.size

private theorem dbTermCoef_of (c : ℕ) (ss : Array ℕ) : (DbTerm.of c ss).coef = c := by
  rw [DbTerm.of]
  split_ifs <;> rfl

private theorem dbTermSlots_of (c : ℕ) (ss : Array ℕ) : (DbTerm.of c ss).slotsArr = ss := by
  rw [DbTerm.of]
  split_ifs with h1 h2
  · rw [show (DbTerm.cst c).slotsArr = #[] from rfl]
    exact (Array.eq_empty_of_size_eq_zero (by simpa using h1)).symm
  · rw [show (DbTerm.lin c (ss.getD 0 0)).slotsArr = #[ss.getD 0 0] from rfl]
    have hsz : ss.size = 1 := by simpa using h2
    refine Array.ext (by simpa using hsz.symm) ?_
    intro k hk hk'
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    rw [Array.getElem_singleton, dbGetD_lt ss 0 0 (by omega)]
  · rfl

private theorem dbProdFold (denv : VarId → ZMod p) (ks : Array VarId) :
    ∀ (sl : List ℕ) (w : ZMod p),
      sl.foldl (fun w s => w * denv (ks.getD s ⟨0⟩)) w
        = w * (sl.map (fun s => denv (ks.getD s ⟨0⟩))).prod := by
  intro sl
  induction sl with
  | nil => intro w; simp
  | cons s rest ih =>
    intro w
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- One term's evaluation is its denotation's value. -/
private theorem dbTermEval_val [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (ks : Array VarId) (sregs : Array ℕ) (dd : ℕ) (hag : DbSRegs denv ks sregs dd)
    (t : DbTerm) (hco : t.coef < p) (hsl : ∀ s ∈ t.slotsArr, s ≤ dd ∧ s < ks.size) :
    (match t with
      | .cst c => c
      | .lin c s => dbMulN p c (sregs.getD s 0)
      | .mono c ss => ss.foldl (fun m s => dbMulN p m (sregs.getD s 0)) c)
      = (dbTermDenote denv ks t).val := by
  have hslv : ∀ s, s ≤ dd → ∀ hs : s < ks.size,
      sregs.getD s 0 = (denv (ks.getD s ⟨0⟩)).val := by
    intro s hsd hs
    rw [dbGetD_lt _ _ _ hs]
    exact hag s hsd hs
  cases t with
  | cst c =>
    rw [dbTermDenote]
    simp only [DbTerm.coef, DbTerm.slotsArr]
    rw [show ((#[] : Array ℕ).toList.map (fun s => denv (ks.getD s ⟨0⟩))).prod = 1 from by simp,
      mul_one, ZMod.val_natCast_of_lt (by simpa [DbTerm.coef] using hco)]
  | lin c s =>
    obtain ⟨hsd, hs⟩ := hsl s (by simp [DbTerm.slotsArr])
    rw [dbTermDenote]
    simp only [DbTerm.coef, DbTerm.slotsArr]
    rw [show (#[s].toList.map (fun s => denv (ks.getD s ⟨0⟩))).prod
        = denv (ks.getD s ⟨0⟩) from by simp]
    have hmul := dbMulN_val ((c : ZMod p)) (denv (ks.getD s ⟨0⟩))
    rw [ZMod.val_natCast_of_lt (by simpa [DbTerm.coef] using hco)] at hmul
    rw [hslv s hsd hs, hmul]
  | mono c ss =>
    rw [dbTermDenote]
    simp only [DbTerm.coef, DbTerm.slotsArr]
    rw [← Array.foldl_toList]
    have key : ∀ (sl : List ℕ) (w : ZMod p), (∀ s ∈ sl, s ≤ dd ∧ s < ks.size) →
        sl.foldl (fun m s => dbMulN p m (sregs.getD s 0)) w.val
          = (w * (sl.map (fun s => denv (ks.getD s ⟨0⟩))).prod).val := by
      intro sl
      induction sl with
      | nil => intro w _; simp
      | cons s rest ih =>
        intro w hmem
        obtain ⟨hsd, hs⟩ := hmem s List.mem_cons_self
        rw [List.foldl_cons, hslv s hsd hs, dbMulN_val,
          ih _ (fun u hu => hmem u (List.mem_cons_of_mem _ hu)), List.map_cons,
          List.prod_cons, ← mul_assoc]
    have hc : c = ((c : ZMod p)).val :=
      (ZMod.val_natCast_of_lt (by simpa [DbTerm.coef] using hco)).symm
    rw [hc, key ss.toList _ (fun s hs => hsl s (by simpa [DbTerm.slotsArr] using hs))]
    rw [ZMod.val_natCast_of_lt (by simpa [DbTerm.coef] using hco)]

/-- Evaluating well-formed terms over agreeing slot registers computes the denotation's value. -/
theorem dbEvalTerms_denote [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (sregs : Array ℕ) (dd : ℕ) (hag : DbSRegs denv ks sregs dd) (ts : Array DbTerm)
    (hwf : DbTermsWF p ks dd ts) :
    dbEvalTerms p sregs ts = (dbTermsDenote denv ks ts).val := by
  rw [dbEvalTerms, dbTermsDenote, ← Array.foldl_toList]
  have key : ∀ (tl : List DbTerm) (acc : ℕ) (z : ZMod p), acc = z.val →
      (∀ t ∈ tl, t.coef < p ∧ ∀ s ∈ t.slotsArr, s ≤ dd ∧ s < ks.size) →
      tl.foldl (fun acc t =>
        match t with
        | .cst c => dbAddN p acc c
        | .lin c s => dbAddN p acc (dbMulN p c (sregs.getD s 0))
        | .mono c ss =>
          dbAddN p acc (ss.foldl (fun m s => dbMulN p m (sregs.getD s 0)) c)) acc
        = (z + (tl.map (dbTermDenote denv ks)).sum).val := by
    intro tl
    induction tl with
    | nil =>
      intro acc z hacc _
      rw [List.foldl_nil, hacc, List.map_nil, List.sum_nil, add_zero]
    | cons t rest ih =>
      intro acc z hacc hmem
      obtain ⟨hco, hsl⟩ := hmem t List.mem_cons_self
      have hval := dbTermEval_val denv ks sregs dd hag t hco hsl
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
      refine ih _ (z + dbTermDenote denv ks t)
        ?_ (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
      cases t with
      | cst c =>
        show dbAddN p acc c = _
        rw [hacc, ← dbAddN_val, ← hval]
      | lin c sl =>
        show dbAddN p acc (dbMulN p c (sregs.getD sl 0)) = _
        rw [hacc, ← dbAddN_val, ← hval]
      | mono c ss =>
        show dbAddN p acc (ss.foldl (fun m s => dbMulN p m (sregs.getD s 0)) c) = _
        rw [hacc, ← dbAddN_val, ← hval]
  have hfin := key ts.toList 0 0 (by simp) (fun t ht => hwf t (by simpa using ht))
  rw [zero_add] at hfin
  exact hfin

/-- The expansion's terms denote the expression, and are well formed at any depth bounding every
    variable's key position. -/
private theorem dbTermDenote_mul (denv : VarId → ZMod p) (ks : Array VarId) [NeZero p]
    (s t : DbTerm) :
    dbTermDenote denv ks (dbMulTerm p s t)
      = dbTermDenote denv ks s * dbTermDenote denv ks t := by
  rw [dbMulTerm, dbTermDenote, dbTermCoef_of, dbTermSlots_of, dbTermDenote, dbTermDenote,
    dbMulN_cast, Array.toList_append, List.map_append, List.prod_append]
  ring

private theorem dbCrossTerms_toList [NeZero p] (x y : Array DbTerm) :
    (dbCrossTerms p x y).toList
      = x.toList.flatMap (fun s => y.toList.map (dbMulTerm p s)) := by
  have inner : ∀ (s : DbTerm) (acc : Array DbTerm),
      (y.foldl (fun acc t => acc.push (dbMulTerm p s t)) acc).toList
        = acc.toList ++ y.toList.map (dbMulTerm p s) := by
    intro s acc
    rw [← Array.foldl_toList]
    generalize y.toList = yl
    induction yl generalizing acc with
    | nil => simp
    | cons t rest ih =>
      rw [List.foldl_cons, ih, Array.toList_push, List.map_cons, List.append_assoc,
        List.singleton_append]
  have outer : ∀ (xl : List DbTerm) (acc : Array DbTerm),
      (xl.foldl (fun a s => y.foldl (fun a t => a.push (dbMulTerm p s t)) a) acc).toList
        = acc.toList ++ xl.flatMap (fun s => y.toList.map (dbMulTerm p s)) := by
    intro xl
    induction xl with
    | nil => intro acc; simp
    | cons s rest ih =>
      intro acc
      rw [List.foldl_cons, ih, inner s acc, List.flatMap_cons, List.append_assoc]
  rw [dbCrossTerms, ← Array.foldl_toList, outer]
  simp

private theorem dbCrossSum [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (y : Array DbTerm) :
    ∀ (xl : List DbTerm),
      ((xl.flatMap (fun s => y.toList.map (dbMulTerm p s))).map (dbTermDenote denv ks)).sum
        = (xl.map (dbTermDenote denv ks)).sum
          * (y.toList.map (dbTermDenote denv ks)).sum := by
  intro xl
  induction xl with
  | nil => simp
  | cons s rest ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons, add_mul]
    congr 1
    rw [List.map_map, show (dbTermDenote denv ks ∘ dbMulTerm p s)
      = (fun t => dbTermDenote denv ks s * dbTermDenote denv ks t) from
        funext (fun t => dbTermDenote_mul denv ks s t)]
    exact List.sum_map_mul_left _ _ _

theorem dbTermsOf_denote [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (hknd : DbNodupIdx ks) (dd : ℕ) (e : DenseExpr p)
    (hvars : ∀ v ∈ e.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v)
    (ts : Array DbTerm) (h : dbTermsOf (ks.map (fun v => v.index)) e = some ts) :
    dbTermsDenote denv ks ts = e.eval denv ∧ DbTermsWF p ks dd ts := by
  induction e generalizing ts with
  | const c =>
    rw [dbTermsOf] at h
    rw [← Option.some.inj h, dbTermsDenote]
    constructor
    · rw [show (#[DbTerm.cst c.val].toList.map (dbTermDenote denv ks))
        = [dbTermDenote denv ks (DbTerm.cst c.val)] from rfl, List.sum_singleton,
        dbTermDenote]
      simp only [DbTerm.coef, DbTerm.slotsArr]
      rw [show ((#[] : Array ℕ).toList.map (fun s => denv (ks.getD s ⟨0⟩))).prod = 1
        from by simp, mul_one, ← zmodOfNatP_eq, zmodOfNatP_val]
      rfl
    · intro t ht
      rw [show t = DbTerm.cst c.val from by simpa using ht]
      exact ⟨ZMod.val_lt _, fun sl hsl => by simp [DbTerm.slotsArr] at hsl⟩
  | var i =>
    obtain ⟨j, hjd, hj, hkj⟩ := hvars i (by simp [DenseExpr.vars])
    have hslot : dbSlotIdx (ks.map (fun v => v.index)) i.index 0 = j := by
      rw [show i.index = ks[j].index from by rw [hkj]]
      exact dbSlotIdx_at ks hknd j hj
    rw [dbTermsOf] at h
    rw [← Option.some.inj h, dbTermsDenote]
    constructor
    · rw [show (#[DbTerm.lin 1 (dbSlotIdx (ks.map (fun v => v.index)) i.index 0)].toList.map
          (dbTermDenote denv ks))
        = [dbTermDenote denv ks
            (DbTerm.lin 1 (dbSlotIdx (ks.map (fun v => v.index)) i.index 0))] from rfl,
        List.sum_singleton, dbTermDenote]
      simp only [DbTerm.coef, DbTerm.slotsArr]
      rw [hslot, show ((#[j] : Array ℕ).toList.map (fun s => denv (ks.getD s ⟨0⟩))).prod
        = denv (ks.getD j ⟨0⟩) from by simp, dbGetD_lt _ _ _ hj, hkj]
      rw [Nat.cast_one, one_mul]
      rfl
    · intro t ht
      rw [show t = DbTerm.lin 1 (dbSlotIdx (ks.map (fun v => v.index)) i.index 0) from by
        simpa using ht]
      refine ⟨by simpa [DbTerm.coef] using (Fact.out : p.Prime).one_lt, fun sl hsl => ?_⟩
      rw [show sl = dbSlotIdx (ks.map (fun v => v.index)) i.index 0 from by
        simpa [DbTerm.slotsArr] using hsl, hslot]
      exact ⟨hjd, hj⟩
  | add a b iha ihb =>
    have ha : ∀ v ∈ a.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    have hb : ∀ v ∈ b.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    rw [dbTermsOf] at h
    rcases hx : dbTermsOf (ks.map (fun v => v.index)) a with _ | x
    · rw [hx] at h; simp at h
    rcases hy : dbTermsOf (ks.map (fun v => v.index)) b with _ | y
    · rw [hx, hy] at h; simp at h
    simp only [hx, hy] at h
    split_ifs at h with hcap
    · obtain ⟨hda, hwa⟩ := iha ha x hx
      obtain ⟨hdb, hwb⟩ := ihb hb y hy
      rw [← Option.some.inj h]
      constructor
      · rw [dbTermsDenote, Array.toList_append, List.map_append, List.sum_append,
          show (DenseExpr.add a b).eval denv = a.eval denv + b.eval denv from rfl,
          ← hda, ← hdb]
        rfl
      · intro t ht
        rcases (by simpa using Array.mem_append.mp ht) with hta | htb
        · exact hwa t hta
        · exact hwb t htb
  | mul a b iha ihb =>
    have ha : ∀ v ∈ a.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    have hb : ∀ v ∈ b.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    rw [dbTermsOf] at h
    rcases hx : dbTermsOf (ks.map (fun v => v.index)) a with _ | x
    · rw [hx] at h; simp at h
    rcases hy : dbTermsOf (ks.map (fun v => v.index)) b with _ | y
    · rw [hx, hy] at h; simp at h
    simp only [hx, hy] at h
    split_ifs at h with hcap
    · obtain ⟨hda, hwa⟩ := iha ha x hx
      obtain ⟨hdb, hwb⟩ := ihb hb y hy
      rw [← Option.some.inj h]
      constructor
      · rw [dbTermsDenote, dbCrossTerms_toList, dbCrossSum denv ks y x.toList,
          show (DenseExpr.mul a b).eval denv = a.eval denv * b.eval denv from rfl,
          ← hda, ← hdb]
        rfl
      · intro t ht
        have htl : t ∈ (dbCrossTerms p x y).toList := by simpa using ht
        rw [dbCrossTerms_toList] at htl
        obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp htl
        obtain ⟨w, hw, hvw⟩ := List.mem_map.mp hv
        rw [← hvw, dbMulTerm]
        constructor
        · rw [dbTermCoef_of]
          exact dbMulN_lt p _ _
        · intro sl hsl
          rw [dbTermSlots_of] at hsl
          rcases (by simpa using Array.mem_append.mp hsl) with h1 | h2
          · exact (hwa u (by simpa using hu)).2 sl h1
          · exact (hwb w (by simpa using hw)).2 sl h2

/-- The slot tree evaluates to the expression's value over agreeing registers. -/
theorem dbTrOf_eval [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (hknd : DbNodupIdx ks) (sregs : Array ℕ) (dd : ℕ) (hag : DbSRegs denv ks sregs dd)
    (e : DenseExpr p)
    (hvars : ∀ v ∈ e.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v) :
    dbEvalTr p sregs (dbTrOf (ks.map (fun v => v.index)) e) = (e.eval denv).val := by
  induction e with
  | const c => rfl
  | var i =>
    obtain ⟨j, hjd, hj, hkj⟩ := hvars i (by simp [DenseExpr.vars])
    rw [dbTrOf, dbEvalTr, show i.index = ks[j].index from by rw [hkj],
      dbSlotIdx_at ks hknd j hj, hag j hjd hj, hkj]
    rfl
  | add a b iha ihb =>
    have ha : ∀ v ∈ a.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    have hb : ∀ v ∈ b.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    rw [dbTrOf, dbEvalTr, iha ha, ihb hb, show (DenseExpr.add a b).eval denv
      = a.eval denv + b.eval denv from rfl]
    exact dbAddN_val _ _
  | mul a b iha ihb =>
    have ha : ∀ v ∈ a.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    have hb : ∀ v ∈ b.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v := fun v hv =>
      hvars v (by simp [DenseExpr.vars, hv])
    rw [dbTrOf, dbEvalTr, iha ha, ihb hb, show (DenseExpr.mul a b).eval denv
      = a.eval denv * b.eval denv from rfl]
    exact dbMulN_val _ _

/-- A compiled operand evaluates to its source expression's value over agreeing registers. -/
theorem dbOpVal_eval [Fact p.Prime] [NeZero p]
    (denv : VarId → ZMod p) (ks : Array VarId) (hknd : DbNodupIdx ks) (sregs : Array ℕ)
    (dd : ℕ) (hag : DbSRegs denv ks sregs dd) (e : DenseExpr p)
    (hvars : ∀ v ∈ e.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v)
    (ops : Array DbCOp) (o : ℕ)
    (hop : ops.getD o default = dbCOpOf (ks.map (fun v => v.index)) e) :
    dbOpVal p ops sregs o = (e.eval denv).val := by
  rw [dbOpVal, hop, dbCOpOf]
  by_cases hsz : dbExprSize e ≤ 1
  · rw [if_pos hsz]
    exact dbTrOf_eval denv ks hknd sregs dd hag e hvars
  · rw [if_neg hsz]
    rcases hts : dbTermsOf (ks.map (fun v => v.index)) e with _ | ts
    · rw [hts]
      exact dbTrOf_eval denv ks hknd sregs dd hag e hvars
    · rw [hts]
      obtain ⟨hden, hwf⟩ := dbTermsOf_denote denv ks hknd dd e hvars ts hts
      show dbEvalTerms p sregs ts = (e.eval denv).val
      rw [dbEvalTerms_denote denv ks sregs dd hag ts hwf, hden]

/-- The affine view of well-formed terms at depth `dd`: over registers agreeing below `dd`, the
    denotation is `b + l · x` with `x` the key-`dd` variable. -/
theorem dbTermsAffine?_spec [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (sregs : Array ℕ) (dd : ℕ) (hdd : dd < ks.size)
    (hag : ∀ j, j < dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val)
    (ts : Array DbTerm) (hwf : DbTermsWF p ks dd ts) (b l : ℕ)
    (h : dbTermsAffine? p sregs dd ts = some (b, l)) :
    b < p ∧ l < p ∧ dbTermsDenote denv ks ts = (b : ZMod p) + (l : ZMod p) * denv ks[dd] := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hcv : ∀ z : ZMod p, ((z.val : ℕ) : ZMod p) = z := fun z => by
    rw [← zmodOfNatP_eq, zmodOfNatP_val]
  have hslv : ∀ s, s ≤ dd → s ≠ dd → ∀ hs : s < ks.size,
      sregs.getD s 0 = (denv (ks.getD s ⟨0⟩)).val := by
    intro s hsd hne hs
    rw [dbGetD_lt _ _ _ hs]
    exact hag s (by omega) hs
  have hnone : ∀ (tl : List DbTerm),
      tl.foldl (fun acc t =>
        match acc with
        | none => none
        | some (b, l) =>
          match t with
          | .cst c => some (dbAddN p b c, l)
          | .lin c s =>
            if s == dd then some (b, dbAddN p l c)
            else some (dbAddN p b (dbMulN p c (sregs.getD s 0)), l)
          | .mono c ss =>
            match ss.foldl (init := ((c : ℕ), (0 : ℕ))) fun st s =>
              if s == dd then (st.1, st.2 + 1)
              else (dbMulN p st.1 (sregs.getD s 0), st.2) with
            | (v, 0) => some (dbAddN p b v, l)
            | (v, 1) => some (b, dbAddN p l v)
            | _ => none) none = none := by
    intro tl
    induction tl with
    | nil => rfl
    | cons t rest ih => rw [List.foldl_cons]; exact ih
  have hmono : ∀ (sl : List ℕ) (v cnt : ℕ), v < p → (∀ s ∈ sl, s ≤ dd ∧ s < ks.size) →
      (sl.foldl (fun st s =>
        if s == dd then (st.1, st.2 + 1)
        else (dbMulN p st.1 (sregs.getD s 0), st.2)) (v, cnt)).1 < p ∧
      ((sl.foldl (fun st s =>
        if s == dd then (st.1, st.2 + 1)
        else (dbMulN p st.1 (sregs.getD s 0), st.2)) (v, cnt)).1 : ZMod p)
        * (denv ks[dd]) ^ (sl.foldl (fun st s =>
            if s == dd then (st.1, st.2 + 1)
            else (dbMulN p st.1 (sregs.getD s 0), st.2)) (v, cnt)).2
        = (v : ZMod p) * (denv ks[dd]) ^ cnt
          * (sl.map (fun s => denv (ks.getD s ⟨0⟩))).prod := by
    intro sl
    induction sl with
    | nil => intro v cnt hv _; exact ⟨hv, by simp⟩
    | cons s rest ih =>
      intro v cnt hv hmem
      obtain ⟨hsd, hs⟩ := hmem s List.mem_cons_self
      rw [List.foldl_cons, List.map_cons, List.prod_cons]
      by_cases hseq : (s == dd) = true
      · rw [if_pos hseq]
        have hseq' : s = dd := by simpa using hseq
        subst hseq'
        obtain ⟨h1, h2⟩ := ih v (cnt + 1) hv
          (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
        refine ⟨h1, ?_⟩
        rw [h2, dbGetD_lt _ _ _ hs, pow_succ]
        ring
      · rw [if_neg hseq]
        obtain ⟨h1, h2⟩ := ih (dbMulN p v (sregs.getD s 0)) cnt (dbMulN_lt p _ _)
          (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
        refine ⟨h1, ?_⟩
        rw [h2, dbMulN_cast, hslv s hsd (by simpa using hseq) hs, hcv]
        ring
  have key : ∀ (tl : List DbTerm) (b0 l0 : ℕ), b0 < p → l0 < p →
      (∀ t ∈ tl, t.coef < p ∧ ∀ s ∈ t.slotsArr, s ≤ dd ∧ s < ks.size) →
      ∀ (b' l' : ℕ),
      tl.foldl (fun acc t =>
        match acc with
        | none => none
        | some (b, l) =>
          match t with
          | .cst c => some (dbAddN p b c, l)
          | .lin c s =>
            if s == dd then some (b, dbAddN p l c)
            else some (dbAddN p b (dbMulN p c (sregs.getD s 0)), l)
          | .mono c ss =>
            match ss.foldl (init := ((c : ℕ), (0 : ℕ))) fun st s =>
              if s == dd then (st.1, st.2 + 1)
              else (dbMulN p st.1 (sregs.getD s 0), st.2) with
            | (v, 0) => some (dbAddN p b v, l)
            | (v, 1) => some (b, dbAddN p l v)
            | _ => none) (some (b0, l0)) = some (b', l') →
      b' < p ∧ l' < p ∧
        (b' : ZMod p) + (l' : ZMod p) * denv ks[dd]
          = ((b0 : ZMod p) + (l0 : ZMod p) * denv ks[dd])
            + (tl.map (dbTermDenote denv ks)).sum := by
    intro tl
    induction tl with
    | nil =>
      intro b0 l0 hb0 hl0 _ b' l' hf
      obtain ⟨hb, hl⟩ : b0 = b' ∧ l0 = l' := by
        have := Option.some.inj hf
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      subst hb; subst hl
      exact ⟨hb0, hl0, by simp⟩
    | cons t rest ih =>
      intro b0 l0 hb0 hl0 hmem b' l' hf
      obtain ⟨hco, hsl⟩ := hmem t List.mem_cons_self
      rw [List.foldl_cons] at hf
      rw [List.map_cons, List.sum_cons]
      cases t with
      | cst c =>
        obtain ⟨h1, h2, h3⟩ := ih (dbAddN p b0 c) l0 (dbAddN_lt p _ _ hb0
            (by simpa [DbTerm.coef] using hco)) hl0
          (fun u hu => hmem u (List.mem_cons_of_mem _ hu)) b' l' hf
        refine ⟨h1, h2, ?_⟩
        rw [h3, dbAddN_cast _ _ hb0 (by simpa [DbTerm.coef] using hco),
          show (dbTermDenote denv ks (DbTerm.cst c)) = (c : ZMod p) from by
            rw [dbTermDenote]; simp [DbTerm.coef, DbTerm.slotsArr]]
        ring
      | lin c sl =>
        obtain ⟨hsd, hs⟩ := hsl sl (by simp [DbTerm.slotsArr])
        have hden : dbTermDenote denv ks (DbTerm.lin c sl)
            = (c : ZMod p) * denv (ks.getD sl ⟨0⟩) := by
          rw [dbTermDenote]; simp [DbTerm.coef, DbTerm.slotsArr]
        by_cases hseq : (sl == dd) = true
        · simp only [hseq, if_true] at hf
          obtain ⟨h1, h2, h3⟩ := ih b0 (dbAddN p l0 c) hb0 (dbAddN_lt p _ _ hl0
              (by simpa [DbTerm.coef] using hco))
            (fun u hu => hmem u (List.mem_cons_of_mem _ hu)) b' l' hf
          refine ⟨h1, h2, ?_⟩
          have hseq' : sl = dd := by simpa using hseq
          subst hseq'
          rw [h3, dbAddN_cast _ _ hl0 (by simpa [DbTerm.coef] using hco), hden,
            dbGetD_lt _ _ _ hs]
          ring
        · have hseqf : (sl == dd) = false := by simpa using hseq
          simp only [hseqf, Bool.false_eq_true, if_false] at hf
          obtain ⟨h1, h2, h3⟩ := ih (dbAddN p b0 (dbMulN p c (sregs.getD sl 0))) l0
            (dbAddN_lt p _ _ hb0 (dbMulN_lt p _ _)) hl0
            (fun u hu => hmem u (List.mem_cons_of_mem _ hu)) b' l' hf
          refine ⟨h1, h2, ?_⟩
          rw [h3, dbAddN_cast _ _ hb0 (dbMulN_lt p _ _), dbMulN_cast, hden,
            hslv sl hsd (by simpa using hseq) hs, hcv]
          ring
      | mono c ss =>
        have hden : dbTermDenote denv ks (DbTerm.mono c ss)
            = (c : ZMod p) * (ss.toList.map (fun s => denv (ks.getD s ⟨0⟩))).prod := rfl
        rcases hin : ss.foldl (fun st s =>
            if s == dd then (st.1, st.2 + 1)
            else (dbMulN p st.1 (sregs.getD s 0), st.2)) ((c : ℕ), (0 : ℕ)) with ⟨v, cnt⟩
        have hinL : ss.toList.foldl (fun st s =>
            if s == dd then (st.1, st.2 + 1)
            else (dbMulN p st.1 (sregs.getD s 0), st.2)) ((c : ℕ), (0 : ℕ)) = (v, cnt) := by
          rw [Array.foldl_toList]; exact hin
        obtain ⟨hv1, hv2⟩ := hmono ss.toList c 0 (by simpa [DbTerm.coef] using hco)
          (fun u hu => hsl u (by simpa [DbTerm.slotsArr] using hu))
        rw [hinL] at hv1 hv2
        simp only [pow_zero, mul_one] at hv2
        simp only [hin] at hf
        match cnt, hf, hv2 with
        | 0, hf, hv2 =>
          obtain ⟨h1, h2, h3⟩ := ih (dbAddN p b0 v) l0 (dbAddN_lt p _ _ hb0 hv1) hl0
            (fun u hu => hmem u (List.mem_cons_of_mem _ hu)) b' l' hf
          refine ⟨h1, h2, ?_⟩
          rw [h3, dbAddN_cast _ _ hb0 hv1, hden, ← hv2, pow_zero, mul_one]
          ring
        | 1, hf, hv2 =>
          obtain ⟨h1, h2, h3⟩ := ih b0 (dbAddN p l0 v) hb0 (dbAddN_lt p _ _ hl0 hv1)
            (fun u hu => hmem u (List.mem_cons_of_mem _ hu)) b' l' hf
          refine ⟨h1, h2, ?_⟩
          rw [h3, dbAddN_cast _ _ hl0 hv1, hden, ← hv2, pow_one]
          ring
        | (n + 2), hf, hv2 =>
          exact absurd (hf.symm.trans
            (show _ = (none : Option (ℕ × ℕ)) from hnone rest)) (by simp)
  rw [dbTermsAffine?, ← Array.foldl_toList] at h
  obtain ⟨h1, h2, h3⟩ := key ts.toList 0 0 hp0 hp0
    (fun t ht => hwf t (by simpa using ht)) b l h
  refine ⟨h1, h2, ?_⟩
  rw [dbTermsDenote, h3]
  simp

/-- The affine view of a compiled operand. -/
theorem dbOpAffine?_spec [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (hknd : DbNodupIdx ks) (sregs : Array ℕ) (dd : ℕ) (hdd : dd < ks.size)
    (hag : ∀ j, j < dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val)
    (e : DenseExpr p)
    (hvars : ∀ v ∈ e.vars, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v)
    (ops : Array DbCOp) (o : ℕ)
    (hop : ops.getD o default = dbCOpOf (ks.map (fun v => v.index)) e) (b l : ℕ)
    (h : dbOpAffine? p ops sregs dd o = some (b, l)) :
    b < p ∧ l < p ∧ e.eval denv = (b : ZMod p) + (l : ZMod p) * denv ks[dd] := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hcv : ∀ z : ZMod p, ((z.val : ℕ) : ZMod p) = z := fun z => by
    rw [← zmodOfNatP_eq, zmodOfNatP_val]
  have hpos : ∀ (e' : DenseExpr p), 1 ≤ dbExprSize e' := by
    intro e'
    cases e' <;> rw [dbExprSize] <;> omega
  rw [dbOpAffine?, hop] at h
  cases e with
  | const c =>
    rw [dbCOpOf, if_pos (show dbExprSize (DenseExpr.const c) ≤ 1 from le_refl 1)] at h
    simp only [dbTrOf] at h
    obtain ⟨hb, hl⟩ : c.val = b ∧ 0 = l := by
      have := Option.some.inj h
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    subst hb; subst hl
    refine ⟨ZMod.val_lt _, hp0, ?_⟩
    rw [hcv, Nat.cast_zero, zero_mul, add_zero]
    rfl
  | var i =>
    obtain ⟨j, hjd, hj, hkj⟩ := hvars i (by simp [DenseExpr.vars])
    have hslot : dbSlotIdx (ks.map (fun v => v.index)) i.index 0 = j := by
      rw [show i.index = ks[j].index from by rw [hkj]]
      exact dbSlotIdx_at ks hknd j hj
    rw [dbCOpOf, if_pos (show dbExprSize (DenseExpr.var i) ≤ 1 from le_refl 1)] at h
    simp only [dbTrOf, hslot] at h
    by_cases hseq : (j == dd) = true
    · have hseq' : j = dd := by simpa using hseq
      subst hseq'
      simp only [beq_self_eq_true, if_true] at h
      obtain ⟨hb, hl⟩ : 0 = b ∧ 1 = l := by
        have := Option.some.inj h
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      subst hb; subst hl
      refine ⟨hp0, (Fact.out : p.Prime).one_lt, ?_⟩
      rw [Nat.cast_zero, Nat.cast_one, zero_add, one_mul,
        show (DenseExpr.var i).eval denv = denv i from rfl, ← hkj]
    · have hne : j ≠ dd := by simpa using hseq
      have hseqf : (j == dd) = false := by simpa using hseq
      simp only [hseqf, Bool.false_eq_true, if_false] at h
      obtain ⟨hb, hl⟩ : sregs.getD j 0 = b ∧ 0 = l := by
        have := Option.some.inj h
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      subst hb; subst hl
      have hagj : sregs.getD j 0 = (denv ks[j]).val := hag j (by omega) hj
      refine ⟨by rw [hagj]; exact ZMod.val_lt _, hp0, ?_⟩
      rw [hagj, hcv, Nat.cast_zero, zero_mul, add_zero,
        show (DenseExpr.var i).eval denv = denv i from rfl, ← hkj]
  | add a b' =>
    rw [dbCOpOf, if_neg (show ¬(dbExprSize (DenseExpr.add a b') ≤ 1) from by
      have := hpos a; have := hpos b'; simp only [dbExprSize]; omega)] at h
    rcases hts : dbTermsOf (ks.map (fun v => v.index)) (DenseExpr.add a b') with _ | ts
    · rw [hts] at h
      simp only [dbTrOf] at h
      simp at h
    · rw [hts] at h
      simp only [] at h
      obtain ⟨hden, hwf⟩ := dbTermsOf_denote denv ks hknd dd (DenseExpr.add a b') hvars ts hts
      obtain ⟨h1, h2, h3⟩ := dbTermsAffine?_spec denv ks sregs dd hdd hag ts hwf b l h
      exact ⟨h1, h2, by rw [← hden, h3]⟩
  | mul a b' =>
    rw [dbCOpOf, if_neg (show ¬(dbExprSize (DenseExpr.mul a b') ≤ 1) from by
      have := hpos a; have := hpos b'; simp only [dbExprSize]; omega)] at h
    rcases hts : dbTermsOf (ks.map (fun v => v.index)) (DenseExpr.mul a b') with _ | ts
    · rw [hts] at h
      simp only [dbTrOf] at h
      simp at h
    · rw [hts] at h
      simp only [] at h
      obtain ⟨hden, hwf⟩ := dbTermsOf_denote denv ks hknd dd (DenseExpr.mul a b') hvars ts hts
      obtain ⟨h1, h2, h3⟩ := dbTermsAffine?_spec denv ks sregs dd hdd hag ts hwf b l h
      exact ⟨h1, h2, by rw [← hden, h3]⟩

/-- The pivot root is the unique solution of `b + l·x = target` read back as a value. -/
theorem dbPivotRoot_eq [Fact p.Prime] [NeZero p] (b l target x : ℕ) (hl : l < p)
    (hl0 : l ≠ 0) (hx : x < p)
    (heq : (target : ZMod p) = (b : ZMod p) + (l : ZMod p) * (x : ZMod p)) :
    dbPivotRoot p b l target = x := by
  have hlz : (l : ZMod p) ≠ 0 := dbCast_ne_zero l hl (by omega)
  have hsolve : ((target : ZMod p) - (b : ZMod p)) * (l : ZMod p)⁻¹ = (x : ZMod p) := by
    rw [heq]
    have hcancel : (b : ZMod p) + (l : ZMod p) * (x : ZMod p) - (b : ZMod p)
        = (l : ZMod p) * (x : ZMod p) := by ring
    rw [hcancel, mul_comm ((l : ZMod p)) ((x : ZMod p)), mul_assoc,
      mul_inv_cancel₀ hlz, mul_one]
  rw [dbPivotRoot, zmodOfNatP_eq, zmodOfNatP_eq, zmodOfNatP_eq]
  by_cases hl1 : l == 1
  · rw [if_pos hl1]
    have hl1' : l = 1 := by simpa using hl1
    rw [show zmodAddP ((target : ZMod p)) (zmodNegP ((b : ZMod p)))
        = (target : ZMod p) - (b : ZMod p) from by
      rw [zmodAddP_eq, zmodNegP_eq, sub_eq_add_neg]]
    have : (target : ZMod p) - (b : ZMod p) = (x : ZMod p) := by
      rw [← hsolve, hl1']
      simp
    rw [this, ZMod.val_natCast_of_lt hx]
  · rw [if_neg hl1]
    rw [show zmodMulP (zmodAddP ((target : ZMod p)) (zmodNegP ((b : ZMod p))))
        ((l : ZMod p))⁻¹ = ((target : ZMod p) - (b : ZMod p)) * (l : ZMod p)⁻¹ from by
      rw [zmodMulP_eq, zmodAddP_eq, zmodNegP_eq, sub_eq_add_neg]]
    rw [hsolve, ZMod.val_natCast_of_lt hx]

/-- One compiled operand's provenance: in bounds (so later pushes preserve it) and equal to the
    source expression's compilation. -/
def DbOpFrom (kidx : Array ℕ) (ops : Array DbCOp) (o : ℕ) (e : DenseExpr p) : Prop :=
  o < ops.size ∧ ops.getD o default = dbCOpOf kidx e

/-- The compiled item's operands are compilations of the source item's expressions, scalars
    preserved. `.always` needs nothing (it is also the sort array's initializer). -/
def DbXItFrom (kidx : Array ℕ) (ops : Array DbCOp) : DbXIt → DbItem p → Prop
  | .always, _ => True
  | .zero o, .zero e => DbOpFrom kidx ops o e
  | .varRange om ox ow, .varRange m x w =>
    DbOpFrom kidx ops om m ∧ DbOpFrom kidx ops ox x ∧ DbOpFrom kidx ops ow w
  | .varRangeConst om ox b', .varRangeConst m x b =>
    DbOpFrom kidx ops om m ∧ DbOpFrom kidx ops ox x ∧ b' = b
  | .tupleRange om ox oy bx' bY', .tupleRange m x y bx bY =>
    DbOpFrom kidx ops om m ∧ DbOpFrom kidx ops ox x ∧ DbOpFrom kidx ops oy y ∧
      bx' = bx ∧ bY' = bY
  | .fixedRange om ov b', .fixedRange m v b =>
    DbOpFrom kidx ops om m ∧ DbOpFrom kidx ops ov v ∧ b' = b
  | .byte om oo1 oo2 orr b' kind', .byte m o1 o2 r b kind =>
    DbOpFrom kidx ops om m ∧ DbOpFrom kidx ops oo1 o1 ∧ DbOpFrom kidx ops oo2 o2 ∧
      DbOpFrom kidx ops orr r ∧ b' = b ∧ kind' = kind
  | .fallback bid' om os, .fallback bid m payload =>
    DbOpFrom kidx ops om m ∧ bid' = bid ∧ List.Forall₂ (DbOpFrom kidx ops) os payload
  | _, _ => False

/-- The operand array only grows, and only by appending: an in-bounds `DbOpFrom` survives. -/
private def DbOpsExt (ops ops' : Array DbCOp) : Prop :=
  ops.size ≤ ops'.size ∧ ∀ o, o < ops.size → ops'.getD o default = ops.getD o default

private theorem dbOpsExt_refl (ops : Array DbCOp) : DbOpsExt ops ops :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem dbOpsExt_trans {a b c : Array DbCOp} (h1 : DbOpsExt a b) (h2 : DbOpsExt b c) :
    DbOpsExt a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun o ho => by rw [h2.2 o (Nat.lt_of_lt_of_le ho h1.1), h1.2 o ho]⟩

private theorem dbOpsExt_push (ops : Array DbCOp) (x : DbCOp) : DbOpsExt ops (ops.push x) :=
  ⟨by simp, fun o ho => dbPushGetD ops x o _ ho⟩

private theorem dbOpFrom_mono {kidx : Array ℕ} {ops ops' : Array DbCOp} (hext : DbOpsExt ops ops')
    (o : ℕ) (e : DenseExpr p) (h : DbOpFrom kidx ops o e) : DbOpFrom kidx ops' o e :=
  ⟨Nat.lt_of_lt_of_le h.1 hext.1, by rw [hext.2 o h.1, h.2]⟩

private theorem dbOpFrom_push {kidx : Array ℕ} (ops : Array DbCOp) (e : DenseExpr p) (o : ℕ)
    (ho : o = ops.size) : DbOpFrom kidx (ops.push (dbCOpOf kidx e)) o e :=
  ⟨by simp [ho], dbPushGetD_at ops _ o default ho⟩

private theorem dbOpFrom_pushed {kidx : Array ℕ} (ops ops' : Array DbCOp) (e : DenseExpr p) (o : ℕ)
    (ho : o = ops.size) (hext : DbOpsExt (ops.push (dbCOpOf kidx e)) ops') :
    DbOpFrom kidx ops' o e :=
  dbOpFrom_mono hext o e (dbOpFrom_push ops e o ho)

private theorem dbXItFrom_mono {kidx : Array ℕ} {ops ops' : Array DbCOp} (hext : DbOpsExt ops ops')
    (xit : DbXIt) (it : DbItem p) (h : DbXItFrom kidx ops xit it) : DbXItFrom kidx ops' xit it := by
  have hm : ∀ (o : ℕ) (e : DenseExpr p), DbOpFrom kidx ops o e → DbOpFrom kidx ops' o e :=
    fun o e hb => dbOpFrom_mono hext o e hb
  cases xit <;> cases it <;> simp only [DbXItFrom] at h ⊢ <;>
    first
      | trivial
      | exact h.elim
      | exact hm _ _ h
      | exact ⟨hm _ _ h.1, hm _ _ h.2.1, hm _ _ h.2.2⟩
      | exact ⟨hm _ _ h.1, hm _ _ h.2.1, h.2.2⟩
      | exact ⟨hm _ _ h.1, h.2.1, h.2.2.imp (fun _ _ hb => hm _ _ hb)⟩
      | exact ⟨hm _ _ h.1, hm _ _ h.2.1, hm _ _ h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
      | exact ⟨hm _ _ h.1, hm _ _ h.2.1, hm _ _ h.2.2.1, hm _ _ h.2.2.2.1,
          h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem dbCompileOps_spec (kidx : Array ℕ) : ∀ (es : List (DenseExpr p))
    (ops : Array DbCOp), DbOpsExt ops (dbCompileOps kidx ops es).1 ∧
      List.Forall₂ (DbOpFrom kidx (dbCompileOps kidx ops es).1) (dbCompileOps kidx ops es).2 es := by
  intro es
  induction es with
  | nil => intro ops; exact ⟨dbOpsExt_refl ops, List.Forall₂.nil⟩
  | cons e rest ih =>
    intro ops
    obtain ⟨hext, hall⟩ := ih (ops.push (dbCOpOf kidx e))
    refine ⟨dbOpsExt_trans (dbOpsExt_push ops _) hext, ?_⟩
    exact List.Forall₂.cons (dbOpFrom_pushed ops _ e ops.size rfl hext) hall

private theorem dbCompileItem_ext (kidx : Array ℕ) (ops : Array DbCOp) (it : DbItem p) :
    DbOpsExt ops (dbCompileItem kidx ops it).1 := by
  cases it with
  | always => exact dbOpsExt_refl ops
  | zero e => exact dbOpsExt_push ops _
  | varRange m x w =>
    exact dbOpsExt_trans (dbOpsExt_push ops _)
      (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _))
  | varRangeConst m x b => exact dbOpsExt_trans (dbOpsExt_push ops _) (dbOpsExt_push _ _)
  | tupleRange m x y bx bY =>
    exact dbOpsExt_trans (dbOpsExt_push ops _)
      (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _))
  | fixedRange m v b => exact dbOpsExt_trans (dbOpsExt_push ops _) (dbOpsExt_push _ _)
  | byte m o1 o2 r b kind =>
    exact dbOpsExt_trans (dbOpsExt_push ops _) (dbOpsExt_trans (dbOpsExt_push _ _)
      (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _)))
  | fallback bid m payload =>
    exact dbOpsExt_trans (dbOpsExt_push ops _)
      (dbCompileOps_spec kidx payload (ops.push (dbCOpOf kidx m))).1

private theorem dbCompileItem_from (kidx : Array ℕ) (ops : Array DbCOp) (it : DbItem p)
    (xit : DbXIt) (h : (dbCompileItem kidx ops it).2 = some xit) :
    DbXItFrom kidx (dbCompileItem kidx ops it).1 xit it := by
  cases it with
  | always => exact absurd h (by simp [dbCompileItem])
  | zero e =>
    rw [show xit = DbXIt.zero ops.size from (Option.some.inj h).symm]
    exact dbOpFrom_push ops e ops.size rfl
  | varRange m x w =>
    rw [show xit = DbXIt.varRange ops.size (ops.size + 1) (ops.size + 2) from (Option.some.inj h).symm]
    exact ⟨dbOpFrom_pushed ops _ m _ rfl
        (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _)),
      dbOpFrom_pushed _ _ x _ (by simp) (dbOpsExt_push _ _),
      dbOpFrom_push _ w _ (by simp)⟩
  | varRangeConst m x b =>
    rw [show xit = DbXIt.varRangeConst ops.size (ops.size + 1) b from (Option.some.inj h).symm]
    exact ⟨dbOpFrom_pushed ops _ m _ rfl (dbOpsExt_push _ _), dbOpFrom_push _ x _ (by simp), rfl⟩
  | tupleRange m x y bx bY =>
    rw [show xit = DbXIt.tupleRange ops.size (ops.size + 1) (ops.size + 2) bx bY
      from (Option.some.inj h).symm]
    exact ⟨dbOpFrom_pushed ops _ m _ rfl
        (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _)),
      dbOpFrom_pushed _ _ x _ (by simp) (dbOpsExt_push _ _),
      dbOpFrom_push _ y _ (by simp), rfl, rfl⟩
  | fixedRange m v b =>
    rw [show xit = DbXIt.fixedRange ops.size (ops.size + 1) b from (Option.some.inj h).symm]
    exact ⟨dbOpFrom_pushed ops _ m _ rfl (dbOpsExt_push _ _), dbOpFrom_push _ v _ (by simp), rfl⟩
  | byte m o1 o2 r b kind =>
    rw [show xit = DbXIt.byte ops.size (ops.size + 1) (ops.size + 2) (ops.size + 3) b kind
      from (Option.some.inj h).symm]
    exact ⟨dbOpFrom_pushed ops _ m _ rfl (dbOpsExt_trans (dbOpsExt_push _ _)
        (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _))),
      dbOpFrom_pushed _ _ o1 _ (by simp)
        (dbOpsExt_trans (dbOpsExt_push _ _) (dbOpsExt_push _ _)),
      dbOpFrom_pushed _ _ o2 _ (by simp) (dbOpsExt_push _ _),
      dbOpFrom_push _ r _ (by simp), rfl, rfl⟩
  | fallback bid m payload =>
    obtain ⟨hext, hall⟩ := dbCompileOps_spec kidx payload (ops.push (dbCOpOf kidx m))
    rw [show xit = DbXIt.fallback bid ops.size
        (dbCompileOps kidx (ops.push (dbCOpOf kidx m)) payload).2 from (Option.some.inj h).symm]
    exact ⟨dbOpFrom_pushed ops _ m _ rfl hext, rfl, hall⟩

/-- The compile loop's invariant: every slot of `out` is either untouched or the compilation of a
    source item, placed inside its own level's `lstart` range. -/
private def DbCompileInv (kidx : Array ℕ) (items : Array (DbItem p)) (ilev lstart : Array ℕ)
    (out : Array DbXIt) (ops : Array DbCOp) : Prop :=
  ∀ pos, out.getD pos .always = .always ∨
    ∃ k, k < items.size ∧ lstart.getD (ilev.getD k 0) 0 ≤ pos ∧
      pos < lstart.getD (ilev.getD k 0 + 1) 0 ∧
      DbXItFrom kidx ops (out.getD pos .always) (items.getD k DbItem.always)

private theorem dbCompileGo_inv (kidx : Array ℕ) (items : Array (DbItem p)) (ilev lstart : Array ℕ) :
    ∀ (n k : ℕ), items.size - k ≤ n → ∀ (cur : Array ℕ) (out : Array DbXIt) (ops : Array DbCOp),
      DbCompileInv kidx items ilev lstart out ops →
      DbCompileInv kidx items ilev lstart (dbCompileGo kidx items ilev lstart k cur out ops).1
        (dbCompileGo kidx items ilev lstart k cur out ops).2 := by
  intro n
  induction n with
  | zero =>
    intro k hn cur out ops hinv
    rw [dbCompileGo, dif_neg (by omega)]
    exact hinv
  | succ n ih =>
    intro k hn cur out ops hinv
    rw [dbCompileGo]
    by_cases hk : k < items.size
    · rw [dif_pos hk]
      have hext := dbCompileItem_ext kidx ops items[k]
      have hinv' : DbCompileInv kidx items ilev lstart out (dbCompileItem kidx ops items[k]).1 :=
        fun pos => (hinv pos).imp id (fun ⟨j, hj, hlo, hhi, hfrom⟩ =>
          ⟨j, hj, hlo, hhi, dbXItFrom_mono hext _ _ hfrom⟩)
      rcases hxit : (dbCompileItem kidx ops items[k]).2 with _ | xit
      · simp only [hxit]
        exact ih (k + 1) (by omega) cur out _ hinv'
      · simp only [hxit]
        refine ih (k + 1) (by omega) _ _ _ (fun pos => ?_)
        by_cases hg : (lstart.getD (ilev.getD k 0) 0 ≤ cur.getD (ilev.getD k 0) 0 &&
            cur.getD (ilev.getD k 0) 0 < lstart.getD (ilev.getD k 0 + 1) 0) = true
        · rw [if_pos hg]
          by_cases hpos : pos = cur.getD (ilev.getD k 0) 0
          · subst hpos
            have hg' : lstart.getD (ilev.getD k 0) 0 ≤ cur.getD (ilev.getD k 0) 0 ∧
                cur.getD (ilev.getD k 0) 0 < lstart.getD (ilev.getD k 0 + 1) 0 := by
              simpa using hg
            rw [dbSetD_at]
            split
            · refine Or.inr ⟨k, hk, hg'.1, hg'.2, ?_⟩
              rw [dbGetD_lt items k _ hk]
              exact dbCompileItem_from kidx ops items[k] xit hxit
            · exact Or.inl rfl
          · rw [dbSetD_ne _ _ _ _ _ hpos]
            exact hinv' pos
        · rw [if_neg hg]
          exact hinv' pos
    · rw [dif_neg hk]
      exact hinv

/-- A nondecreasing `ℕ` array (the level offsets). -/
private def DbNondec (ls : Array ℕ) : Prop :=
  ∀ i j, i ≤ j → j < ls.size → ls.getD i 0 ≤ ls.getD j 0

private theorem dbGetD_ge {α : Type u} (vs : Array α) (k : ℕ) (dflt : α) (h : vs.size ≤ k) :
    vs.getD k dflt = dflt := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

private theorem dbLstartOf_nondec (counts : Array ℕ) :
    0 < (dbLstartOf counts).size ∧ DbNondec (dbLstartOf counts) := by
  have hzero : ∀ q, (#[0] : Array ℕ).getD q 0 = 0 := by
    intro q
    rcases Nat.lt_or_ge q 1 with h | h
    · rw [show q = 0 from by omega]; simp
    · exact dbGetD_ge _ _ _ (by simpa using h)
  have hstep : ∀ (ls : Array ℕ) (c : ℕ), 0 < ls.size ∧ DbNondec ls →
      0 < (ls.push (ls.getD (ls.size - 1) 0 + c)).size ∧
        DbNondec (ls.push (ls.getD (ls.size - 1) 0 + c)) := by
    intro ls c hls
    obtain ⟨hsz, hnd⟩ := hls
    refine ⟨by simp, fun i j hij hj => ?_⟩
    rw [Array.size_push] at hj
    by_cases hjs : j < ls.size
    · rw [dbPushGetD _ _ i _ (by omega), dbPushGetD _ _ j _ hjs]
      exact hnd i j hij hjs
    · rw [dbPushGetD_at _ _ j _ (by omega)]
      by_cases his : i < ls.size
      · rw [dbPushGetD _ _ i _ his]
        exact Nat.le_trans (hnd i (ls.size - 1) (by omega) (by omega)) (Nat.le_add_right _ _)
      · rw [dbPushGetD_at _ _ i _ (by omega)]
  rw [dbLstartOf]
  exact dbFoldlInv (fun ls => 0 < ls.size ∧ DbNondec ls) _ counts
    (fun ls c _ hls => hstep ls c hls) #[0]
    ⟨by simp, fun i j _ _ => by rw [hzero i, hzero j]⟩

private theorem dbLstart_unique (ls : Array ℕ) (hnd : DbNondec ls) (a b pos : ℕ)
    (ha : ls.getD a 0 ≤ pos) (ha' : pos < ls.getD (a + 1) 0)
    (hb : ls.getD b 0 ≤ pos) (hb' : pos < ls.getD (b + 1) 0) : a = b := by
  have key : ∀ x y : ℕ, x < y → pos < ls.getD (x + 1) 0 → ls.getD y 0 ≤ pos →
      pos < ls.getD (y + 1) 0 → False := by
    intro x y hxy hx' hy hy'
    have hy1 : y + 1 < ls.size := by
      by_contra hc
      rw [dbGetD_ge ls (y + 1) 0 (by omega)] at hy'
      omega
    have := hnd (x + 1) y (by omega) (by omega)
    omega
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd (key a b h ha' hb hb') not_false
  · exact h
  · exact absurd (key b a h hb' ha ha') not_false

/-- Every slot of the compiled plan's level-`dd` range holds `.always` or the compilation of a
    source item whose level is `dd`. -/
theorem dbCompilePlan_from (kidx : Array ℕ) (kks : ℕ) (items : Array (DbItem p))
    (ilev : Array ℕ) (dd pos : ℕ)
    (hlo : (dbCompilePlan kidx kks items ilev).lstart.getD dd 0 ≤ pos)
    (hhi : pos < (dbCompilePlan kidx kks items ilev).lstart.getD (dd + 1) 0) :
    (dbCompilePlan kidx kks items ilev).items.getD pos .always = .always ∨
      ∃ k, k < items.size ∧ ilev.getD k 0 = dd ∧
        DbXItFrom kidx (dbCompilePlan kidx kks items ilev).ops
          ((dbCompilePlan kidx kks items ilev).items.getD pos .always)
          (items.getD k DbItem.always) := by
  set counts := dbLevCount items ilev 0 (Array.replicate kks 0) with hcounts
  set lstart := dbLstartOf counts with hlstart
  have hlst : (dbCompilePlan kidx kks items ilev).lstart = lstart := rfl
  rw [hlst] at hlo hhi
  have hgo := dbCompileGo_inv kidx items ilev lstart items.size 0 (by omega)
    (lstart.extract 0 kks) (Array.replicate (lstart.getD kks 0) .always)
    (Array.emptyWithCapacity (2 * items.size))
    (fun q => Or.inl (by rw [dbGetD_replicate]; split <;> rfl))
  rcases hgo pos with hAlw | ⟨k, hk, hklo, hkhi, hfrom⟩
  · exact Or.inl hAlw
  · exact Or.inr ⟨k, hk,
      dbLstart_unique lstart (dbLstartOf_nondec counts).2 _ _ pos hklo hkhi hlo hhi, hfrom⟩

/-- The bridge: a compiled item's test passes wherever its source item's does — both sides
    evaluate every operand to its value at the assignment. -/
theorem dbXItOk_bridge [Fact p.Prime] [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ks : Array VarId) (hknd : DbNodupIdx ks) (sregs : Array ℕ)
    (dd : ℕ) (hag : DbSRegs denv ks sregs dd)
    (it : DbItem p) (vs : Array VarId) (hivars : DbItemVars it vs)
    (hpos : ∀ v ∈ vs, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v)
    (xit : DbXIt) (ops : Array DbCOp)
    (hfrom : DbXItFrom (ks.map (fun v => v.index)) ops xit it)
    (wregs : Array ℕ) (hwagree : DbRegsAgreeA denv wregs vs)
    (hok : dbItemOk facts wregs it = true) :
    dbXItOk facts ops sregs xit = true := by
  have heval : ∀ (o : ℕ) (e : DenseExpr p), DbOpFrom (ks.map (fun v => v.index)) ops o e →
      (∀ v ∈ e.vars, v ∈ vs) → dbOpVal p ops sregs o = (e.eval denv).val := by
    intro o e hfr hev
    exact dbOpVal_eval denv ks hknd sregs dd hag e
      (fun v hv => hpos v (hev v hv)) ops o hfr.2
  have hwval : ∀ (e : DenseExpr p), (∀ v ∈ e.vars, v ∈ vs) →
      dbEval p wregs e = (e.eval denv).val := by
    intro e hev
    exact dbEval_eval denv wregs e (fun i hi => hwagree i (hev i hi))
  cases xit with
  | always => rfl
  | zero o =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next e =>
    simp only [DbItemVars] at hivars
    show (dbOpVal p ops sregs o == 0) = true
    rw [heval o e hfrom hivars]
    rw [show dbItemOk facts wregs (DbItem.zero e) = (dbEval p wregs e == 0) from rfl,
      hwval e hivars] at hok
    exact hok
  | varRange om ox ow =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next m x w =>
    obtain ⟨hm, hx, hw⟩ := hivars
    obtain ⟨fm, fx, fw⟩ := hfrom
    simp only [dbXItOk, heval om m fm hm, heval ox x fx hx, heval ow w fw hw]
    simp only [dbItemOk, hwval m hm, hwval x hx, hwval w hw] at hok
    exact hok
  | varRangeConst om ox b' =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next m x b =>
    obtain ⟨hm, hx⟩ := hivars
    obtain ⟨fm, fx, hb⟩ := hfrom
    subst hb
    simp only [dbXItOk, heval om m fm hm, heval ox x fx hx]
    simp only [dbItemOk, hwval m hm, hwval x hx] at hok
    exact hok
  | tupleRange om ox oy bx' bY' =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next m x y bx bY =>
    obtain ⟨hm, hx, hy⟩ := hivars
    obtain ⟨fm, fx, fy, hbx, hbY⟩ := hfrom
    subst hbx; subst hbY
    simp only [dbXItOk, heval om m fm hm, heval ox x fx hx, heval oy y fy hy]
    simp only [dbItemOk, hwval m hm, hwval x hx, hwval y hy] at hok
    exact hok
  | fixedRange om ov b' =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next m v b =>
    obtain ⟨hm, hv⟩ := hivars
    obtain ⟨fm, fv, hb⟩ := hfrom
    subst hb
    simp only [dbXItOk, heval om m fm hm, heval ov v fv hv]
    simp only [dbItemOk, hwval m hm, hwval v hv] at hok
    exact hok
  | byte om oo1 oo2 orr b' kind' =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next m o1 o2 r b kind =>
    obtain ⟨hm, h1, h2, hr⟩ := hivars
    obtain ⟨fm, f1, f2, fr, hb, hkind⟩ := hfrom
    subst hb; subst hkind
    simp only [dbXItOk, heval om m fm hm, heval oo1 o1 f1 h1, heval oo2 o2 f2 h2,
      heval orr r fr hr]
    simp only [dbItemOk, hwval m hm, hwval o1 h1, hwval o2 h2, hwval r hr] at hok
    exact hok
  | fallback bid' om os =>
    cases it <;> simp only [DbXItFrom] at hfrom
    next bid m payload =>
    obtain ⟨hm, hpl⟩ := hivars
    obtain ⟨fm, hbid, hf2⟩ := hfrom
    subst hbid
    have hpay : ∀ (os' : List ℕ) (pl : List (DenseExpr p)),
        List.Forall₂ (DbOpFrom (ks.map (fun v => v.index)) ops) os' pl →
        (∀ e ∈ pl, ∀ v ∈ e.vars, v ∈ vs) →
        os'.map (fun o => zmodOfNatP p (dbOpVal p ops sregs o))
          = pl.map (fun ex => ex.eval denv) := by
      intro os' pl hf
      induction hf with
      | nil => intro _; rfl
      | cons hpair htail ih =>
        intro hev
        simp only [List.map_cons]
        rw [heval _ _ hpair (hev _ List.mem_cons_self), zmodOfNatP_val,
          ih (fun e he => hev e (List.mem_cons_of_mem _ he))]
    have hwpay : payload.map (fun t => zmodOfNatP p (dbEval p wregs t))
        = payload.map (fun ex => ex.eval denv) := by
      refine List.map_congr_left ?_
      intro x hx
      rw [hwval x (hpl x hx), zmodOfNatP_val]
    simp only [dbXItOk, heval om m fm hm]
    simp only [dbItemOk, hwval m hm] at hok
    by_cases hz : (m.eval denv).val == 0
    · rw [if_pos hz]
    · rw [if_neg hz]
      rw [if_neg hz] at hok
      rw [hpay os payload hf2 hpl]
      rw [hwpay] at hok
      exact hok

/-- All compiled items of a range pass when each one does. -/
theorem dbLevOkY_of {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array DbXIt)
    (ops : Array DbCOp) (sregs : Array ℕ) (lo hi : ℕ)
    (h : ∀ pos, lo ≤ pos → pos < hi → pos < items.size →
      dbXItOk facts ops sregs (items.getD pos .always) = true) :
    dbLevOkY facts items ops sregs lo hi = true := by
  have key : ∀ (m i : ℕ), hi - i ≤ m → lo ≤ i →
      dbLevOkY facts items ops sregs i hi = true := by
    intro m
    induction m with
    | zero =>
      intro i hm hlo
      rw [dbLevOkY, if_neg (by omega)]
    | succ m ih =>
      intro i hm hlo
      by_cases hih : i < hi
      · rw [dbLevOkY, if_pos hih]
        split
        · next hsz =>
          rw [if_pos (by
            have := h i hlo hih hsz
            rwa [dbGetD_lt _ _ _ hsz] at this)]
          exact ih (i + 1) (by omega) (by omega)
        · rfl
      · rw [dbLevOkY, if_neg hih]
  exact key hi lo (by omega) (le_refl _)

/-- The per-position source facts both pivot lemmas consume. -/
def DbPivotSrc {bs : BusSemantics p} (facts : BusFacts p bs) (denv : VarId → ZMod p)
    (ks : Array VarId) (dd : ℕ) (items : Array DbXIt) (ops : Array DbCOp) (lo hi : ℕ) : Prop :=
  ∀ pos, lo ≤ pos → pos < hi → pos < items.size →
    items.getD pos .always = .always ∨
    ∃ (it : DbItem p) (vs : Array VarId) (wregs : Array ℕ),
      DbItemVars it vs ∧
      (∀ v ∈ vs, ∃ j, j ≤ dd ∧ ∃ hj : j < ks.size, ks[j] = v) ∧
      DbXItFrom (ks.map (fun v => v.index)) ops (items.getD pos .always) it ∧
      DbRegsAgreeA denv wregs vs ∧ dbItemOk facts wregs it = true

/-- A pivot pins the assignment's own slot value to the computed root. -/
private theorem dbFindPivot_sound [Fact p.Prime] [NeZero p] {bs : BusSemantics p}
    (facts : BusFacts p bs) (denv : VarId → ZMod p) (ks : Array VarId) (hknd : DbNodupIdx ks)
    (sregs : Array ℕ) (dd : ℕ) (hdd : dd < ks.size)
    (hag : ∀ j, j < dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val)
    (items : Array DbXIt) (ops : Array DbCOp) (lo hi : ℕ)
    (hsrc : DbPivotSrc facts denv ks dd items ops lo hi) :
    ∀ (m i : ℕ), hi - i ≤ m → lo ≤ i → ∀ o target,
      dbFindPivot p items ops sregs dd i hi = some (DbPivot.val o target) →
      ∃ b l, dbOpAffine? p ops sregs dd o = some (b, l) ∧
        dbPivotRoot p b l target = (denv ks[dd]).val := by
  have hx : (denv ks[dd]).val < p := ZMod.val_lt _
  have hxcast : (((denv ks[dd]).val : ℕ) : ZMod p) = denv ks[dd] := by
    rw [← zmodOfNatP_eq, zmodOfNatP_val]
  intro m
  induction m with
  | zero =>
    intro i hm hlo o target h
    rw [dbFindPivot, if_neg (by omega)] at h
    simp at h
  | succ m ih =>
    intro i hm hlo o target h
    by_cases hih : i < hi
    · rw [dbFindPivot, if_pos hih] at h
      by_cases hsz : i < items.size
      · rw [dif_pos hsz] at h
        revert h
        split
        · next piv' hhead =>
          intro h
          have hpiv : piv' = DbPivot.val o target := Option.some.inj h
          subst hpiv
          have hxit : items.getD i .always = items[i] := dbGetD_lt _ _ _ hsz
          rcases hsrc i hlo hih hsz with hAlw | ⟨it, vs', w', hiv, hpos', hfrom', hagr, hok⟩
          · rw [hxit] at hAlw
            rw [hAlw] at hhead
            simp [dbItemPivot?] at hhead
          · rw [hxit] at hfrom'
            cases hitem : items[i] with
            | always => rw [hitem] at hhead; simp [dbItemPivot?] at hhead
            | varRange a b c => rw [hitem] at hhead; simp [dbItemPivot?] at hhead
            | varRangeConst a b c => rw [hitem] at hhead; simp [dbItemPivot?] at hhead
            | tupleRange a b c d' e' => rw [hitem] at hhead; simp [dbItemPivot?] at hhead
            | fixedRange a b c => rw [hitem] at hhead; simp [dbItemPivot?] at hhead
            | fallback a b c => rw [hitem] at hhead; simp [dbItemPivot?] at hhead
            | byte om oo1 oo2 orr b' kind' =>
              rw [hitem] at hfrom' hhead
              cases it <;> simp only [DbXItFrom] at hfrom'
              next mm o1 o2 r bound kind =>
              obtain ⟨hm', h1, h2, hr⟩ := hiv
              obtain ⟨fm, f1, f2, fr, hbb, hkk⟩ := hfrom'
              subst hbb; subst hkk
              simp only [dbItemPivot?, dbBytePivot] at hhead
              split at hhead
              all_goals try contradiction
              rename_i mv hcstm
              split_ifs at hhead with hmv0
              split at hhead
              all_goals try contradiction
              rename_i b1 l1 b2 l2 br lr haff1 haff2 haffr
              -- the semantic facts at the assignment
              obtain ⟨hmvp, _, hmden⟩ := dbOpAffine?_spec denv ks hknd sregs dd hdd hag
                mm (fun v hv => hpos' v (hm' v hv)) ops om fm.2 mv 0 hcstm
              have hcv : ∀ z : ZMod p, ((z.val : ℕ) : ZMod p) = z := fun z => by
                rw [← zmodOfNatP_eq, zmodOfNatP_val]
              have hconstv : ∀ (bc lc : ℕ) (ec : DenseExpr p), lc = 0 → bc < p →
                  ec.eval denv = (bc : ZMod p) + (lc : ZMod p) * denv ks[dd] →
                  (ec.eval denv).val = bc := by
                intro bc lc ec hlc hbc hden
                subst hlc
                rw [hden, Nat.cast_zero, zero_mul, add_zero, ZMod.val_natCast,
                  Nat.mod_eq_of_lt hbc]
              have hroot : ∀ (bc lc target' : ℕ) (ec : DenseExpr p), lc ≠ 0 → bc < p →
                  lc < p → target' = (ec.eval denv).val →
                  ec.eval denv = (bc : ZMod p) + (lc : ZMod p) * denv ks[dd] →
                  dbPivotRoot p bc lc target' = (denv ks[dd]).val := by
                intro bc lc target' ec hlc hbc hlcp htg hden
                refine dbPivotRoot_eq bc lc target' (denv ks[dd]).val hlcp hlc
                  (ZMod.val_lt _) ?_
                rw [hxcast, htg, hcv, hden]
              have hmne : (mm.eval denv).val ≠ 0 := by
                rw [hconstv mv 0 mm rfl hmvp hmden]
                simpa using hmv0
              have hokB := hok
              simp only [dbItemOk, dbEval_eval denv w' mm (fun z hz => hagr z (hm' z hz)),
                dbEval_eval denv w' o1 (fun z hz => hagr z (h1 z hz)),
                dbEval_eval denv w' o2 (fun z hz => hagr z (h2 z hz)),
                dbEval_eval denv w' r (fun z hz => hagr z (hr z hz))] at hokB
              rw [if_neg (by simpa using hmne)] at hokB
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hokB
              have hbrel : dbByteRel kind' (o1.eval denv).val (o2.eval denv).val
                  (r.eval denv).val = true := by tauto
              obtain ⟨hb1p, hl1p, hden1⟩ := dbOpAffine?_spec denv ks hknd sregs dd hdd
                hag o1 (fun v hv => hpos' v (h1 v hv)) ops oo1 f1.2 b1 l1 haff1
              obtain ⟨hb2p, hl2p, hden2⟩ := dbOpAffine?_spec denv ks hknd sregs dd hdd
                hag o2 (fun v hv => hpos' v (h2 v hv)) ops oo2 f2.2 b2 l2 haff2
              obtain ⟨hbrp, hlrp, hdenr⟩ := dbOpAffine?_spec denv ks hknd sregs dd hdd
                hag r (fun v hv => hpos' v (hr v hv)) ops orr fr.2 br lr haffr
              split_ifs at hhead with hc1 hc2 hc3
              · -- `o1` linear, `o2` and the result constant: only xor solves for `o1`
                simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc1
                obtain ⟨⟨hl1ne, hl2z⟩, hlrz⟩ := hc1
                have hb2v := hconstv b2 l2 o2 hl2z hb2p hden2
                have hbrv := hconstv br lr r hlrz hbrp hdenr
                cases kind' with
                | pair => simp at hhead
                | or => simp at hhead
                | and => simp at hhead
                | xor =>
                  have hrelv : (r.eval denv).val
                      = Nat.xor (o1.eval denv).val (o2.eval denv).val := of_decide_eq_true hbrel
                  have htg : Nat.xor br b2 = (o1.eval denv).val := by
                    rw [← hb2v, ← hbrv, hrelv]
                    simp [Nat.xor_assoc]
                  obtain ⟨ho', ht'⟩ : oo1 = o ∧ Nat.xor br b2 = target := by
                    have := Option.some.inj hhead
                    constructor <;> cases this <;> rfl
                  subst ho'; subst ht'
                  exact ⟨b1, l1, haff1, hroot b1 l1 _ o1 hl1ne hb1p hl1p htg hden1⟩
              · -- `o2` linear, `o1` and the result constant
                simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc2
                obtain ⟨⟨hl1z, hl2ne⟩, hlrz⟩ := hc2
                have hb1v := hconstv b1 l1 o1 hl1z hb1p hden1
                have hbrv := hconstv br lr r hlrz hbrp hdenr
                cases kind' with
                | pair => simp at hhead
                | or => simp at hhead
                | and => simp at hhead
                | xor =>
                  have hrelv : (r.eval denv).val
                      = Nat.xor (o1.eval denv).val (o2.eval denv).val := of_decide_eq_true hbrel
                  have htg : Nat.xor br b1 = (o2.eval denv).val := by
                    rw [← hb1v, ← hbrv, hrelv]
                    show ((o1.eval denv).val ^^^ (o2.eval denv).val) ^^^ (o1.eval denv).val = _
                    rw [Nat.xor_comm (o1.eval denv).val, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
                  obtain ⟨ho', ht'⟩ : oo2 = o ∧ Nat.xor br b1 = target := by
                    have := Option.some.inj hhead
                    constructor <;> cases this <;> rfl
                  subst ho'; subst ht'
                  exact ⟨b2, l2, haff2, hroot b2 l2 _ o2 hl2ne hb2p hl2p htg hden2⟩
              · -- the result linear, both operands constant: every kind solves for the result
                simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hc3
                obtain ⟨⟨hl1z, hl2z⟩, hlrne⟩ := hc3
                have hb1v := hconstv b1 l1 o1 hl1z hb1p hden1
                have hb2v := hconstv b2 l2 o2 hl2z hb2p hden2
                have key : ∀ (target' : ℕ), target' = (r.eval denv).val →
                    some (DbPivot.val orr target') = some (DbPivot.val o target) →
                    ∃ b l, dbOpAffine? p ops sregs dd o = some (b, l) ∧
                      dbPivotRoot p b l target = (denv ks[dd]).val := by
                  intro target' htg hh
                  obtain ⟨ho', ht'⟩ : orr = o ∧ target' = target := by
                    have := Option.some.inj hh
                    constructor <;> cases this <;> rfl
                  subst ho'; subst ht'
                  exact ⟨br, lr, haffr, hroot br lr _ r hlrne hbrp hlrp htg hdenr⟩
                cases kind' with
                | pair =>
                  refine key 0 ?_ hhead
                  simp only [dbByteRel, beq_iff_eq] at hbrel
                  exact hbrel.symm
                | xor =>
                  refine key _ ?_ hhead
                  rw [← hb1v, ← hb2v]
                  exact (of_decide_eq_true hbrel).symm
                | or =>
                  refine key _ ?_ hhead
                  rw [← hb1v, ← hb2v]
                  exact (of_decide_eq_true hbrel).symm
                | and =>
                  refine key _ ?_ hhead
                  rw [← hb1v, ← hb2v]
                  exact (of_decide_eq_true hbrel).symm
            | zero o' =>
              rw [hitem] at hfrom' hhead
              cases it <;> simp only [DbXItFrom] at hfrom'
              next e =>
              simp only [DbItemVars] at hiv
              simp only [dbItemPivot?] at hhead
              split at hhead
              all_goals try contradiction
              rename_i b l haff
              · split_ifs at hhead with hl
                have hl' : l ≠ 0 := by simpa using hl
                obtain ⟨ho', ht'⟩ : o' = o ∧ (0 : ℕ) = target := by
                  have := Option.some.inj hhead
                  constructor <;> cases this <;> rfl
                subst ho'; subst ht'
                obtain ⟨hb, hlp, hden⟩ := dbOpAffine?_spec denv ks hknd sregs dd hdd hag e
                  (fun v hv => hpos' v (hiv v hv)) ops o' hfrom'.2 b l haff
                have hz : e.eval denv = 0 := by
                  have hv0 : (e.eval denv).val = 0 := by
                    have := hok
                    rw [show dbItemOk facts w' (DbItem.zero e) = (dbEval p w' e == 0)
                      from rfl, dbEval_eval denv w' e
                        (fun z hz => hagr z (hiv z hz))] at this
                    simpa using this
                  exact (ZMod.val_eq_zero _).mp hv0
                refine ⟨b, l, haff, ?_⟩
                refine dbPivotRoot_eq b l 0 (denv ks[dd]).val hlp hl' hx ?_
                rw [hxcast, Nat.cast_zero, ← hden, hz]
        · next hhead =>
          intro h
          exact ih (i + 1) (by omega) (by omega) o target h
      · rw [dif_neg hsz] at h
        simp at h
    · rw [dbFindPivot, if_neg hih] at h
      simp at h

/-- A `.val` pivot pins the assignment's own slot value to the computed root. -/
theorem dbFindPivot_val [Fact p.Prime] [NeZero p] {bs : BusSemantics p}
    (facts : BusFacts p bs) (denv : VarId → ZMod p) (ks : Array VarId) (hknd : DbNodupIdx ks)
    (sregs : Array ℕ) (dd : ℕ) (hdd : dd < ks.size)
    (hag : ∀ j, j < dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val)
    (items : Array DbXIt) (ops : Array DbCOp) (lo hi : ℕ)
    (hsrc : DbPivotSrc facts denv ks dd items ops lo hi) (o target : ℕ)
    (h : dbFindPivot p items ops sregs dd lo hi = some (DbPivot.val o target)) :
    ∃ b l, dbOpAffine? p ops sregs dd o = some (b, l) ∧
      dbPivotRoot p b l target = (denv ks[dd]).val :=
  dbFindPivot_sound facts denv ks hknd sregs dd hdd hag items ops lo hi hsrc hi lo
    (by omega) (le_refl _) o target h

/-- On a directly-indexable domain, a member value is found at an index carrying it. -/
theorem dbDomFind_mem [NeZero p] (dom : DbDom) (x : ℕ) (hxp : x < p)
    (hdir : ∀ cb cn ca, dom ≠ DbDom.coset cb cn ca)
    (hmem : DbDomMem p dom x) :
    ∃ i0, dbDomFind dom x = some i0 ∧ i0 < dom.size ∧ DbDom.at p dom i0 = x := by
  obtain ⟨k, hk, hat⟩ := hmem
  cases dom with
  | range b =>
    rw [DbDom.size] at hk
    rw [DbDom.at] at hat
    have hxb : x < b := by
      split at hat
      · omega
      · next hkp =>
        have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
        have := Nat.mod_lt k hp0
        omega
    refine ⟨x, by rw [dbDomFind, if_pos hxb], by rw [DbDom.size]; exact hxb, ?_⟩
    rw [DbDom.at, if_pos hxp]
  | explicit vs =>
    rw [DbDom.size] at hk
    rw [DbDom.at] at hat
    have hmemv : x ∈ vs := by
      rw [← hat, dbGetD_lt _ _ _ hk]
      exact Array.getElem_mem hk
    have hfind : vs.findIdx? (fun v => v == x) = some (vs.findIdx (fun v => v == x)) :=
      Array.findIdx?_eq_some_of_exists ⟨x, hmemv, by simp⟩
    obtain ⟨hi0, hpred, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfind
    refine ⟨vs.findIdx (fun v => v == x), by rw [dbDomFind]; exact hfind,
      by rw [DbDom.size]; exact hi0, ?_⟩
    rw [DbDom.at, dbGetD_lt _ _ _ hi0]
    exact eq_of_beq hpred
  | coset b negB aInv => exact absurd rfl (hdir b negB aInv)

/-! ### The compiled box loop -/

/-- Every key the mask still calls forced carries the assignment's value (slot-indexed). -/
def DbMaskAgreeY (denv : VarId → ZMod p) (ks : Array VarId) (st : DbScanY) : Prop :=
  ∀ j, ∀ hj : j < ks.size, st.alive.getD j false = true →
    st.vals.getD j 0 = (denv ks[j]).val

def DbScanYGood (denv : VarId → ZMod p) (ks : Array VarId) (st : DbScanY) : Prop :=
  st.started = true ∧ st.vals.size = ks.size ∧ (st.live = 0 ∨ DbMaskAgreeY denv ks st)

private theorem dbAbsorbY_spec (regs vals : Array ℕ) :
    ∀ (m i live : ℕ) (alive : Array Bool), vals.size - i ≤ m →
      (dbAbsorbY regs i vals alive live).1 = vals ∧
      (∀ j, (dbAbsorbY regs i vals alive live).2.1.getD j false = true →
        alive.getD j false = true) ∧
      (∀ j, i ≤ j → j < vals.size →
        (dbAbsorbY regs i vals alive live).2.1.getD j false = true →
        regs.getD j 0 = vals.getD j 0) := by
  intro m
  induction m with
  | zero =>
    intro i live alive hm
    rw [dbAbsorbY, dif_neg (by omega)]
    exact ⟨rfl, fun _ h => h, fun j hj hjs _ => absurd hjs (by omega)⟩
  | succ m ih =>
    intro i live alive hm
    by_cases hlt : i < vals.size
    · rw [dbAbsorbY, dif_pos hlt]
      have hdead : ∀ (al : Array Bool), (al.set! i false).getD i false = false := by
        intro al
        rw [dbSetD_at]
        split <;> rfl
      have hne : ∀ (al : Array Bool) (j : ℕ), j ≠ i →
          (al.set! i false).getD j false = al.getD j false := fun al j hji =>
        dbSetD_ne al i j false false hji
      by_cases hal : alive.getD i false
      · rw [if_pos hal]
        by_cases heq : regs.getD i 0 == vals.getD i 0
        · rw [if_pos heq]
          obtain ⟨h1, h2, h3⟩ := ih (i + 1) live alive (by omega)
          refine ⟨h1, h2, fun j hj hjs hjl => ?_⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact h3 j (by omega) hjs hjl
          · have : j = i := by omega
            subst this
            simpa using heq
        · rw [if_neg heq]
          obtain ⟨h1, h2, h3⟩ := ih (i + 1) (live - 1) (alive.set! i false) (by omega)
          refine ⟨h1, fun j hjl => ?_, fun j hj hjs hjl => ?_⟩
          · have hj2 := h2 j hjl
            rcases Nat.decEq j i with hji | hji
            · rwa [hne alive j hji] at hj2
            · subst hji
              rw [hdead alive] at hj2
              exact absurd hj2 (by simp)
          · rcases Nat.lt_or_ge i j with hij | hij
            · exact h3 j (by omega) hjs hjl
            · have hji : j = i := by omega
              subst hji
              have hj2 := h2 j hjl
              rw [hdead alive] at hj2
              exact absurd hj2 (by simp)
      · rw [if_neg hal]
        obtain ⟨h1, h2, h3⟩ := ih (i + 1) live alive (by omega)
        refine ⟨h1, h2, fun j hj hjs hjl => ?_⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact h3 j (by omega) hjs hjl
        · have : j = i := by omega
          subst this
          exact absurd (h2 j hjl) (by simpa using hal)
    · rw [dbAbsorbY, dif_neg hlt]
      exact ⟨rfl, fun _ h => h, fun j hj hjs _ => absurd hjs (by omega)⟩

/-- Absorbing any register file: the result is started with a `ks.size` mask, and only kills. -/
private theorem dbAbsorbYArgs_shape (ks : Array VarId) (regs vals : Array ℕ)
    (alive : Array Bool) (live : ℕ) (started : Bool) (hsz : ks.size ≤ regs.size)
    (hvsz : started = true → vals.size = ks.size) :
    (dbAbsorbYArgs ks.size regs vals alive live started).2.2.2 = true ∧
    (dbAbsorbYArgs ks.size regs vals alive live started).1.size = ks.size ∧
    (started = true →
      (dbAbsorbYArgs ks.size regs vals alive live started).1 = vals ∧
      ∀ j, (dbAbsorbYArgs ks.size regs vals alive live started).2.1.getD j false = true →
        alive.getD j false = true) := by
  cases started with
  | false =>
    rw [dbAbsorbYArgs]
    simp only [Bool.not_false, if_true]
    refine ⟨by simp, by rw [Array.size_extract]; omega, fun h => by simp at h⟩
  | true =>
    rw [dbAbsorbYArgs]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨h1, h2, _⟩ := dbAbsorbY_spec regs vals vals.size 0 live alive (by omega)
    refine ⟨by simp, ?_, fun _ => ⟨h1, h2⟩⟩
    show (dbAbsorbY regs 0 vals alive live).1.size = ks.size
    rw [h1]
    exact hvsz rfl

/-- Absorbing the assignment's own register file makes every surviving key carry its value. -/
private theorem dbAbsorbYArgs_agree (denv : VarId → ZMod p) (ks : Array VarId)
    (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool)
    (hsz : ks.size ≤ regs.size) (hvsz : started = true → vals.size = ks.size)
    (hregs : ∀ j, ∀ hj : j < ks.size, regs.getD j 0 = (denv ks[j]).val) :
    ∀ j, ∀ hj : j < ks.size,
      (dbAbsorbYArgs ks.size regs vals alive live started).2.1.getD j false = true →
      (dbAbsorbYArgs ks.size regs vals alive live started).1.getD j 0 = (denv ks[j]).val := by
  cases started with
  | false =>
    rw [dbAbsorbYArgs]
    simp only [Bool.not_false, if_true]
    intro j hj _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by
      rw [Array.size_extract]; omega)]
    rw [show (regs.extract 0 ks.size)[j]'(by rw [Array.size_extract]; omega)
      = regs[0 + j]'(by omega) from Array.getElem_extract (by rw [Array.size_extract]; omega)]
    have := hregs j hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at this
    simpa using this
  | true =>
    rw [dbAbsorbYArgs]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨h1, _, h3⟩ := dbAbsorbY_spec regs vals vals.size 0 live alive (by omega)
    intro j hj hal
    show (dbAbsorbY regs 0 vals alive live).1.getD j 0 = _
    rw [h1, ← h3 j (Nat.zero_le _) (by rw [hvsz rfl]; omega) hal]
    exact hregs j hj

/-- Frame: the loops only write register slots at their own depth or deeper, and never resize. -/
private theorem dbScanY_frame {bs : BusSemantics p} (facts : BusFacts p bs)
    (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array ℕ) (doms : Array DbDom)
    (kks : ℕ) :
    ∀ (m d : ℕ), kks - d ≤ m →
      (∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
        (dbScanDepth facts items ops lstart doms kks d regs vals alive live
            started).regs.size = regs.size ∧
        ∀ j, j < d →
          (dbScanDepth facts items ops lstart doms kks d regs vals alive live
            started).regs.getD j 0 = regs.getD j 0) := by
  have hloop : ∀ (d : ℕ),
      (d + 1 < kks → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool),
        (dbScanDepth facts items ops lstart doms kks (d + 1) regs vals alive live
            started).regs.size = regs.size ∧
        ∀ j, j < d + 1 →
          (dbScanDepth facts items ops lstart doms kks (d + 1) regs vals alive live
            started).regs.getD j 0 = regs.getD j 0) →
      ∀ (dom : DbDom) (lo hi i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool)
        (live : ℕ) (started : Bool),
        (dbScanLoopY facts items ops lstart doms kks d dom lo hi i n regs vals alive live
            started).regs.size = regs.size ∧
        ∀ j, j < d →
          (dbScanLoopY facts items ops lstart doms kks d dom lo hi i n regs vals alive live
            started).regs.getD j 0 = regs.getD j 0 := by
    intro d hdepth dom lo hi i n
    have key : ∀ (m2 i : ℕ) (regs vals : Array ℕ) (alive : Array Bool)
        (live : ℕ) (started : Bool), n - i ≤ m2 →
        (dbScanLoopY facts items ops lstart doms kks d dom lo hi i n regs vals alive live
            started).regs.size = regs.size ∧
        ∀ j, j < d →
          (dbScanLoopY facts items ops lstart doms kks d dom lo hi i n regs vals alive live
            started).regs.getD j 0 = regs.getD j 0 := by
      intro m2
      induction m2 with
      | zero =>
        intro i regs vals alive live started hm2
        rw [dbScanLoopY, if_pos (by omega : i ≥ n)]
        exact ⟨rfl, fun j _ => rfl⟩
      | succ m2 ih =>
        intro i regs vals alive live started hm2
        by_cases hin : i ≥ n
        · rw [dbScanLoopY, if_pos hin]
          exact ⟨rfl, fun j _ => rfl⟩
        · rw [dbScanLoopY, if_neg hin]
          by_cases habort : started && live == 0
          · rw [if_pos habort]
            exact ⟨rfl, fun j _ => rfl⟩
          · rw [if_neg habort]
            by_cases hok : (decide (lo ≥ hi) || dbLevOkY facts items ops
                (regs.set! d (DbDom.at p dom i)) lo hi) = true
            · rw [if_pos hok]
              by_cases hleaf : d + 1 ≥ kks
              · rw [if_pos hleaf]
                obtain ⟨h1, h2⟩ := ih (i + 1) _ _ _ _ _ (by omega)
                refine ⟨by rw [h1, dbSet_size], fun j hj => ?_⟩
                rw [h2 j hj, dbSetD_ne _ _ _ _ _ (by omega : j ≠ d)]
              · rw [if_neg hleaf]
                obtain ⟨hd1, hd2⟩ := hdepth (by omega) (regs.set! d (DbDom.at p dom i))
                  vals alive live started
                obtain ⟨h1, h2⟩ := ih (i + 1) _ _ _ _ _ (by omega)
                refine ⟨by rw [h1, hd1, dbSet_size], fun j hj => ?_⟩
                rw [h2 j hj, hd2 j (by omega), dbSetD_ne _ _ _ _ _ (by omega : j ≠ d)]
            · rw [if_neg hok]
              obtain ⟨h1, h2⟩ := ih (i + 1) _ _ _ _ _ (by omega)
              refine ⟨by rw [h1, dbSet_size], fun j hj => ?_⟩
              rw [h2 j hj, dbSetD_ne _ _ _ _ _ (by omega : j ≠ d)]
    exact fun regs vals alive live started => key (n - i) i regs vals alive live started
      (le_refl _)
  intro m
  induction m with
  | zero =>
    intro d hm regs vals alive live started
    have hdepth : d + 1 < kks → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool),
        (dbScanDepth facts items ops lstart doms kks (d + 1) regs vals alive live
            started).regs.size = regs.size ∧
        ∀ j, j < d + 1 →
          (dbScanDepth facts items ops lstart doms kks (d + 1) regs vals alive live
            started).regs.getD j 0 = regs.getD j 0 := fun h => absurd h (by omega)
    simp only [dbScanDepth]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first
      | exact hloop d hdepth _ _ _ _ _ _ _ _ _ _
      | exact ⟨rfl, fun j _ => rfl⟩
  | succ m ihm =>
    intro d hm regs vals alive live started
    have hdepth : d + 1 < kks → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool),
        (dbScanDepth facts items ops lstart doms kks (d + 1) regs vals alive live
            started).regs.size = regs.size ∧
        ∀ j, j < d + 1 →
          (dbScanDepth facts items ops lstart doms kks (d + 1) regs vals alive live
            started).regs.getD j 0 = regs.getD j 0 := fun h regs' vals' alive' live'
        started' => ihm (d + 1) (by omega) regs' vals' alive' live' started'
    simp only [dbScanDepth]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first
      | exact hloop d hdepth _ _ _ _ _ _ _ _ _ _
      | exact ⟨rfl, fun j _ => rfl⟩

/-- Absorbing from a started state: the values stay, flags only die. -/
private theorem dbAbsorbYArgs_started (ks : Array VarId) (regs vals : Array ℕ)
    (alive : Array Bool) (live : ℕ) :
    (dbAbsorbYArgs ks.size regs vals alive live true).2.2.2 = true ∧
    (dbAbsorbYArgs ks.size regs vals alive live true).1 = vals ∧
    ∀ j, (dbAbsorbYArgs ks.size regs vals alive live true).2.1.getD j false = true →
      alive.getD j false = true := by
  rw [dbAbsorbYArgs]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  obtain ⟨h1, h2, _⟩ := dbAbsorbY_spec regs vals vals.size 0 live alive (by omega)
  exact ⟨by simp, h1, h2⟩

/-- Preserve: a good mask stays good — absorbing only kills keys. -/
private theorem dbScanY_preserve {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ks : Array VarId)
    (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array ℕ) (doms : Array DbDom) :
    ∀ (m d : ℕ), ks.size - d ≤ m →
      ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
        DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
        DbScanYGood denv ks (dbScanDepth facts items ops lstart doms ks.size d regs vals
          alive live started) := by
  have hstep : ∀ (regs' vals : Array ℕ) (alive : Array Bool) (live : ℕ),
      vals.size = ks.size →
      DbMaskAgreeY denv ks ⟨regs', vals, alive, live, true⟩ →
      DbScanYGood denv ks ⟨regs',
        (dbAbsorbYArgs ks.size regs' vals alive live true).1,
        (dbAbsorbYArgs ks.size regs' vals alive live true).2.1,
        (dbAbsorbYArgs ks.size regs' vals alive live true).2.2.1,
        (dbAbsorbYArgs ks.size regs' vals alive live true).2.2.2⟩ := by
    intro regs' vals alive live hvsz hagree
    obtain ⟨hs1, hs2, hs3⟩ := dbAbsorbYArgs_started ks regs' vals alive live
    refine ⟨hs1, by show (dbAbsorbYArgs ks.size regs' vals alive live true).1.size = _
                    rw [hs2]; exact hvsz, Or.inr ?_⟩
    intro j hj hal
    show (dbAbsorbYArgs ks.size regs' vals alive live true).1.getD j 0 = _
    rw [hs2]
    exact hagree j hj (hs3 j hal)
  have hloop : ∀ (d : ℕ),
      (d + 1 < ks.size → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool),
        DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
        DbScanYGood denv ks (dbScanDepth facts items ops lstart doms ks.size (d + 1) regs
          vals alive live started)) →
      ∀ (dom : DbDom) (lo hi i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool)
        (live : ℕ) (started : Bool),
        DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
        DbScanYGood denv ks (dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n
          regs vals alive live started) := by
    intro d hdepth dom lo hi i n
    have key : ∀ (m2 i : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool), n - i ≤ m2 →
        DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
        DbScanYGood denv ks (dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n
          regs vals alive live started) := by
      intro m2
      induction m2 with
      | zero =>
        intro i regs vals alive live started hm2 hgood
        rw [dbScanLoopY, if_pos (by omega : i ≥ n)]
        exact hgood
      | succ m2 ih =>
        intro i regs vals alive live started hm2 hgood
        by_cases hin : i ≥ n
        · rw [dbScanLoopY, if_pos hin]
          exact hgood
        · rw [dbScanLoopY, if_neg hin]
          by_cases habort : (started && live == 0) = true
          · rw [if_pos habort]
            exact hgood
          · rw [if_neg habort]
            obtain ⟨hst, hvsz, hlive⟩ := hgood
            have hagree : DbMaskAgreeY denv ks ⟨regs, vals, alive, live, started⟩ := by
              rcases hlive with h0 | h
              · exact absurd (by
                  rw [show started = true from hst, show live = 0 from h0]; rfl) habort
              · exact h
            by_cases hok : (decide (lo ≥ hi) || dbLevOkY facts items ops
                (regs.set! d (DbDom.at p dom i)) lo hi) = true
            · rw [if_pos hok]
              by_cases hleaf : d + 1 ≥ ks.size
              · rw [if_pos hleaf]
                subst hst
                have hnew := hstep (regs.set! d (DbDom.at p dom i)) vals alive live hvsz
                  (fun j hj hal => hagree j hj hal)
                exact ih (i + 1) _ _ _ _ _ (by omega) hnew
              · rw [if_neg hleaf]
                have hr := hdepth (by omega) (regs.set! d (DbDom.at p dom i)) vals alive
                  live started ⟨hst, hvsz, hlive⟩
                exact ih (i + 1) _ _ _ _ _ (by omega) hr
            · rw [if_neg hok]
              exact ih (i + 1) _ _ _ _ _ (by omega) ⟨hst, hvsz, hlive⟩
    exact fun regs vals alive live started => key (n - i) i regs vals alive live started
      (le_refl _)
  intro m
  induction m with
  | zero =>
    intro d hm regs vals alive live started hgood
    have hdepth : d + 1 < ks.size → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool),
        DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
        DbScanYGood denv ks (dbScanDepth facts items ops lstart doms ks.size (d + 1) regs
          vals alive live started) := fun h => absurd h (by omega)
    simp only [dbScanDepth]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first
      | exact hloop d hdepth _ _ _ _ _ _ _ _ _ _ hgood
      | exact hgood
  | succ m ihm =>
    intro d hm regs vals alive live started hgood
    have hdepth : d + 1 < ks.size → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool),
        DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
        DbScanYGood denv ks (dbScanDepth facts items ops lstart doms ks.size (d + 1) regs
          vals alive live started) := fun h regs' vals' alive' live' started' hg' =>
      ihm (d + 1) (by omega) regs' vals' alive' live' started' hg'
    simp only [dbScanDepth]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first
      | exact hloop d hdepth _ _ _ _ _ _ _ _ _ _ hgood
      | exact hgood

/-- Preserve, at the loop level. -/
private theorem dbScanY_preserveL {bs : BusSemantics p} (facts : BusFacts p bs)
    (denv : VarId → ZMod p) (ks : Array VarId)
    (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array ℕ) (doms : Array DbDom)
    (d : ℕ) :
    ∀ (dom : DbDom) (lo hi i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
      (started : Bool),
      DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
      DbScanYGood denv ks (dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n
        regs vals alive live started) := by
  intro dom lo hi i n
  have key : ∀ (m2 i : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
      (started : Bool), n - i ≤ m2 →
      DbScanYGood denv ks ⟨regs, vals, alive, live, started⟩ →
      DbScanYGood denv ks (dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n
        regs vals alive live started) := by
    intro m2
    induction m2 with
    | zero =>
      intro i regs vals alive live started hm2 hgood
      rw [dbScanLoopY, if_pos (by omega : i ≥ n)]
      exact hgood
    | succ m2 ih =>
      intro i regs vals alive live started hm2 hgood
      by_cases hin : i ≥ n
      · rw [dbScanLoopY, if_pos hin]
        exact hgood
      · rw [dbScanLoopY, if_neg hin]
        by_cases habort : (started && live == 0) = true
        · rw [if_pos habort]
          exact hgood
        · rw [if_neg habort]
          obtain ⟨hst, hvsz, hlive⟩ := hgood
          have hagree : DbMaskAgreeY denv ks ⟨regs, vals, alive, live, started⟩ := by
            rcases hlive with h0 | h
            · exact absurd (by
                rw [show started = true from hst, show live = 0 from h0]; rfl) habort
            · exact h
          by_cases hok : (decide (lo ≥ hi) || dbLevOkY facts items ops
              (regs.set! d (DbDom.at p dom i)) lo hi) = true
          · rw [if_pos hok]
            by_cases hleaf : d + 1 ≥ ks.size
            · rw [if_pos hleaf]
              subst hst
              obtain ⟨hs1, hs2, hs3⟩ := dbAbsorbYArgs_started ks
                (regs.set! d (DbDom.at p dom i)) vals alive live
              refine ih (i + 1) _ _ _ _ _ (by omega) ⟨hs1, ?_, Or.inr ?_⟩
              · show (dbAbsorbYArgs ks.size (regs.set! d (DbDom.at p dom i)) vals alive
                  live true).1.size = _
                rw [hs2]
                exact hvsz
              · intro j hj hal
                show (dbAbsorbYArgs ks.size (regs.set! d (DbDom.at p dom i)) vals alive
                  live true).1.getD j 0 = _
                rw [hs2]
                exact hagree j hj (hs3 j hal)
            · rw [if_neg hleaf]
              have hr := dbScanY_preserve facts denv ks items ops lstart doms
                (ks.size - (d + 1)) (d + 1) (le_refl _)
                (regs.set! d (DbDom.at p dom i)) vals alive live started
                ⟨hst, hvsz, hlive⟩
              exact ih (i + 1) _ _ _ _ _ (by omega) hr
          · rw [if_neg hok]
            exact ih (i + 1) _ _ _ _ _ (by omega) ⟨hst, hvsz, hlive⟩
  exact fun regs vals alive live started => key (n - i) i regs vals alive live started
    (le_refl _)

/-- The mask arrays keep `ks.size` entries from the first absorb on. -/
private theorem dbScanY_masksz {bs : BusSemantics p} (facts : BusFacts p bs)
    (ks : Array VarId) (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array ℕ)
    (doms : Array DbDom) :
    ∀ (m d : ℕ), ks.size - d ≤ m →
      ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
        regs.size = ks.size → (started = true → vals.size = ks.size) →
        ((dbScanDepth facts items ops lstart doms ks.size d regs vals alive live
            started).started = true →
          (dbScanDepth facts items ops lstart doms ks.size d regs vals alive live
            started).vals.size = ks.size) := by
  have hloop : ∀ (d : ℕ),
      (d + 1 < ks.size → ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool), regs.size = ks.size → (started = true → vals.size = ks.size) →
        ((dbScanDepth facts items ops lstart doms ks.size (d + 1) regs vals alive live
            started).started = true →
          (dbScanDepth facts items ops lstart doms ks.size (d + 1) regs vals alive live
            started).vals.size = ks.size)) →
      ∀ (dom : DbDom) (lo hi i n : ℕ) (regs vals : Array ℕ) (alive : Array Bool)
        (live : ℕ) (started : Bool), regs.size = ks.size →
        (started = true → vals.size = ks.size) →
        ((dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n regs vals alive
            live started).started = true →
          (dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n regs vals alive
            live started).vals.size = ks.size) := by
    intro d hdepth dom lo hi i n
    have key : ∀ (m2 i : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
        (started : Bool), n - i ≤ m2 → regs.size = ks.size →
        (started = true → vals.size = ks.size) →
        ((dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n regs vals alive
            live started).started = true →
          (dbScanLoopY facts items ops lstart doms ks.size d dom lo hi i n regs vals alive
            live started).vals.size = ks.size) := by
      intro m2
      induction m2 with
      | zero =>
        intro i regs vals alive live started hm2 hrs hmask
        rw [dbScanLoopY, if_pos (by omega : i ≥ n)]
        exact hmask
      | succ m2 ih =>
        intro i regs vals alive live started hm2 hrs hmask
        by_cases hin : i ≥ n
        · rw [dbScanLoopY, if_pos hin]
          exact hmask
        · rw [dbScanLoopY, if_neg hin]
          by_cases habort : (started && live == 0) = true
          · rw [if_pos habort]
            exact hmask
          · rw [if_neg habort]
            by_cases hok : (decide (lo ≥ hi) || dbLevOkY facts items ops
                (regs.set! d (DbDom.at p dom i)) lo hi) = true
            · rw [if_pos hok]
              by_cases hleaf : d + 1 ≥ ks.size
              · rw [if_pos hleaf]
                obtain ⟨_, hsz', _⟩ := dbAbsorbYArgs_shape ks
                  (regs.set! d (DbDom.at p dom i)) vals alive live started
                  (by rw [dbSet_size]; omega) hmask
                exact ih (i + 1) _ _ _ _ _ (by omega) (by rw [dbSet_size]; exact hrs)
                  (fun _ => hsz')
              · rw [if_neg hleaf]
                obtain ⟨hf1, _⟩ := dbScanY_frame facts items ops lstart doms ks.size
                  (ks.size - (d + 1)) (d + 1) (le_refl _)
                  (regs.set! d (DbDom.at p dom i)) vals alive live started
                have hr := hdepth (by omega) (regs.set! d (DbDom.at p dom i)) vals alive
                  live started (by rw [dbSet_size]; exact hrs) hmask
                exact ih (i + 1) _ _ _ _ _ (by omega)
                  (by rw [hf1, dbSet_size]; exact hrs) hr
            · rw [if_neg hok]
              exact ih (i + 1) _ _ _ _ _ (by omega) (by rw [dbSet_size]; exact hrs) hmask
    exact fun regs vals alive live started => key (n - i) i regs vals alive live started
      (le_refl _)
  intro m
  induction m with
  | zero =>
    intro d hm regs vals alive live started hrs hmask
    have hdepth : d + 1 < ks.size → ∀ (regs vals : Array ℕ) (alive : Array Bool)
        (live : ℕ) (started : Bool), regs.size = ks.size →
        (started = true → vals.size = ks.size) →
        ((dbScanDepth facts items ops lstart doms ks.size (d + 1) regs vals alive live
            started).started = true →
          (dbScanDepth facts items ops lstart doms ks.size (d + 1) regs vals alive live
            started).vals.size = ks.size) := fun h => absurd h (by omega)
    simp only [dbScanDepth]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first
      | exact hloop d hdepth _ _ _ _ _ _ _ _ _ _ hrs hmask
      | exact hmask
  | succ m ihm =>
    intro d hm regs vals alive live started hrs hmask
    have hdepth : d + 1 < ks.size → ∀ (regs vals : Array ℕ) (alive : Array Bool)
        (live : ℕ) (started : Bool), regs.size = ks.size →
        (started = true → vals.size = ks.size) →
        ((dbScanDepth facts items ops lstart doms ks.size (d + 1) regs vals alive live
            started).started = true →
          (dbScanDepth facts items ops lstart doms ks.size (d + 1) regs vals alive live
            started).vals.size = ks.size) := fun h regs' vals' alive' live' started' hrs'
        hm' => ihm (d + 1) (by omega) regs' vals' alive' live' started' hrs' hm'
    simp only [dbScanDepth]
    split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals try split
    all_goals first
      | exact hloop d hdepth _ _ _ _ _ _ _ _ _ _ hrs hmask
      | exact hmask

/-- Reach: the assignment's own point is visited and absorbed, so the final mask is good. -/
private theorem dbScanY_reach [Fact p.Prime] [NeZero p] {bs : BusSemantics p}
    (facts : BusFacts p bs) (denv : VarId → ZMod p) (ks : Array VarId)
    (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array ℕ) (doms : Array DbDom)
    (hmem : ∀ dd, ∀ hdd : dd < ks.size, DbDomMem p (doms.getD dd (.range 0))
      (denv ks[dd]).val)
    (hitems : ∀ (dd : ℕ) (sregs : Array ℕ), dd < ks.size → DbSRegs denv ks sregs dd →
      dbLevOkY facts items ops sregs (lstart.getD dd 0) (lstart.getD (dd + 1) 0) = true)
    (hval : ∀ (dd : ℕ) (sregs : Array ℕ) (o target : ℕ), ∀ hdd : dd < ks.size,
      (∀ j, j < dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val) →
      dbFindPivot p items ops sregs dd (lstart.getD dd 0) (lstart.getD (dd + 1) 0)
        = some (DbPivot.val o target) →
      ∃ b l, dbOpAffine? p ops sregs dd o = some (b, l) ∧
        dbPivotRoot p b l target = (denv ks[dd]).val) :
    ∀ (m d : ℕ), ks.size - d ≤ m → d < ks.size →
      ∀ (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ) (started : Bool),
        regs.size = ks.size → (started = true → vals.size = ks.size) →
        (∀ j, j < d → ∀ hj : j < ks.size, regs.getD j 0 = (denv ks[j]).val) →
        DbScanYGood denv ks (dbScanDepth facts items ops lstart doms ks.size d regs vals
          alive live started) := by
  intro m
  induction m with
  | zero => intro d hm hd; omega
  | succ m ihm =>
    intro d hm hd regs vals alive live started hrs hmask houter
    have hloopreach : ∀ (idx n : ℕ), idx < n →
        DbDom.at p (doms.getD d (DbDom.range 0)) idx = (denv ks[d]).val →
        ∀ (m2 i : ℕ) (regs vals : Array ℕ) (alive : Array Bool) (live : ℕ)
          (started : Bool), n - i ≤ m2 → i ≤ idx →
          regs.size = ks.size → (started = true → vals.size = ks.size) →
          (∀ j, j < d → ∀ hj : j < ks.size, regs.getD j 0 = (denv ks[j]).val) →
          DbScanYGood denv ks (dbScanLoopY facts items ops lstart doms ks.size d
            (doms.getD d (DbDom.range 0)) (lstart.getD d 0) (lstart.getD (d + 1) 0) i n
            regs vals alive live started) := by
      intro idx n hidxn hat m2
      induction m2 with
      | zero => intro i regs vals alive live started hm2 hiidx; omega
      | succ m2 ih =>
        intro i regs vals alive live started hm2 hiidx hrs' hmask' houter'
        rw [dbScanLoopY, if_neg (by omega : ¬ i ≥ n)]
        by_cases habort : (started && live == 0) = true
        · rw [if_pos habort]
          refine ⟨by simpa using (Bool.and_eq_true ..).mp habort |>.1,
            hmask' (by simpa using (Bool.and_eq_true ..).mp habort |>.1), Or.inl ?_⟩
          simpa using (Bool.and_eq_true ..).mp habort |>.2
        · rw [if_neg habort]
          have houter'' : ∀ j, j < d → ∀ hj : j < ks.size,
              (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD j 0
                = (denv ks[j]).val := by
            intro j hj hjk
            rw [dbSetD_ne _ _ _ _ _ (by omega : j ≠ d)]
            exact houter' j hj hjk
          have hrs'' : (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)).size
              = ks.size := by rw [dbSet_size]; exact hrs'
          rcases Nat.lt_or_ge i idx with hlti | hgei
          · -- before the assignment's point: keep walking, whatever happens
            by_cases hok : (decide (lstart.getD d 0 ≥ lstart.getD (d + 1) 0) ||
                dbLevOkY facts items ops
                  (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i))
                  (lstart.getD d 0) (lstart.getD (d + 1) 0)) = true
            · rw [if_pos hok]
              by_cases hleaf : d + 1 ≥ ks.size
              · rw [if_pos hleaf]
                obtain ⟨hs1, hs2, _⟩ := dbAbsorbYArgs_shape ks
                  (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)) vals alive
                  live started (by omega) hmask'
                exact ih (i + 1) _ _ _ _ _ (by omega) (by omega) hrs'' (fun _ => hs2)
                  houter''
              · rw [if_neg hleaf]
                have hf := dbScanY_frame facts items ops lstart doms ks.size
                  (ks.size - (d + 1)) (d + 1) (le_refl _)
                  (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)) vals alive
                  live started
                have hmsz := dbScanY_masksz facts ks items ops lstart doms
                  (ks.size - (d + 1)) (d + 1) (le_refl _)
                  (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)) vals alive
                  live started hrs'' hmask'
                refine ih (i + 1) _ _ _ _ _ (by omega) (by omega)
                  (by rw [hf.1]; exact hrs'') hmsz (fun j hj hjk => ?_)
                rw [hf.2 j (by omega)]
                exact houter'' j hj hjk
            · rw [if_neg hok]
              exact ih (i + 1) _ _ _ _ _ (by omega) (by omega) hrs'' hmask' houter''
          · -- the assignment's point: the level test passes and the mask becomes good
            have hieq : i = idx := by omega
            subst hieq
            have hagd : ∀ j, j ≤ d → ∀ hj : j < ks.size,
                (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD j 0
                  = (denv ks[j]).val := by
              intro j hj hjk
              rcases Nat.lt_or_ge j d with h | h
              · exact houter'' j h hjk
              · have : j = d := by omega
                subst this
                rw [dbSetD_at, if_pos (by omega), hat]
            have hok : (decide (lstart.getD d 0 ≥ lstart.getD (d + 1) 0) ||
                dbLevOkY facts items ops
                  (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i))
                  (lstart.getD d 0) (lstart.getD (d + 1) 0)) = true := by
              rw [hitems d _ hd (fun j hj hjk => hagd j hj hjk), Bool.or_true]
            rw [if_pos hok]
            by_cases hleaf : d + 1 ≥ ks.size
            · rw [if_pos hleaf]
              have hfull : ∀ j, ∀ hj : j < ks.size,
                  (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)).getD j 0
                    = (denv ks[j]).val := fun j hj => hagd j (by omega) hj
              obtain ⟨hs1, hs2, _⟩ := dbAbsorbYArgs_shape ks
                (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)) vals alive
                live started (by omega) hmask'
              have hagr := dbAbsorbYArgs_agree denv ks
                (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)) vals alive
                live started (by omega) hmask' hfull
              refine dbScanY_preserveL facts denv ks items ops lstart doms d _ _ _
                (i + 1) n _ _ _ _ _ ⟨hs1, hs2, Or.inr ?_⟩
              exact fun j hj hal => hagr j hj hal
            · rw [if_neg hleaf]
              have hr := ihm (d + 1) (by omega) (by omega)
                (regs.set! d (DbDom.at p (doms.getD d (DbDom.range 0)) i)) vals alive
                live started hrs'' hmask' (fun j hj hjk => hagd j (by omega) hjk)
              obtain ⟨hr1, hr2, hr3⟩ := hr
              exact dbScanY_preserveL facts denv ks items ops lstart doms d _ _ _
                (i + 1) n _ _ _ _ _ ⟨hr1, hr2, hr3⟩
    -- the depth dispatch
    obtain ⟨kidx, hkidx, hkat⟩ := hmem d hd
    simp only [dbScanDepth]
    by_cases hsmall : (doms.getD d (DbDom.range 0)).size < 12
    · rw [if_pos hsmall]
      exact hloopreach kidx (doms.getD d (DbDom.range 0)).size hkidx hkat
        (doms.getD d (DbDom.range 0)).size 0 regs vals alive live started (by omega)
        (by omega) hrs hmask houter
    · rw [if_neg hsmall]
      rcases hpiv : dbFindPivot p items ops regs d (lstart.getD d 0)
          (lstart.getD (d + 1) 0) with _ | piv
      · exact hloopreach kidx (doms.getD d (DbDom.range 0)).size hkidx hkat
          (doms.getD d (DbDom.range 0)).size 0 regs vals alive live started (by omega)
          (by omega) hrs hmask houter
      · rcases piv with ⟨o, target⟩
        obtain ⟨b, l, haff, hroot⟩ := hval d regs o target hd
          (fun j hj hjk => houter j hj hjk) hpiv
        simp only [haff]
        split
        · -- coset: the sweep (the direct flag is false, definitionally)
          exact hloopreach kidx (doms.getD d (DbDom.range 0)).size hkidx hkat
            (doms.getD d (DbDom.range 0)).size 0 regs vals alive live started (by omega)
            (by omega) hrs hmask houter
        · -- directly indexable: one lookup
          rename_i hne
          obtain ⟨i0, hfind, hi0, hat0⟩ := dbDomFind_mem (doms.getD d (DbDom.range 0))
            (denv ks[d]).val (ZMod.val_lt _) (fun cb cn ca h => hne cb cn ca h)
            ⟨kidx, hkidx, hkat⟩
          rw [hroot, hfind]
          exact hloopreach i0 (i0 + 1) (by omega) hat0 1 i0 regs vals alive live started
            (by omega) (le_refl _) hrs hmask houter

/-- The compiled scan of a preflighted box ends with a good mask: the assignment's own point is
    never skipped — pivots pin it, `.dead` levels are refuted — and absorbing it makes every
    surviving key carry its value. -/
theorem dbScanDepth_good [Fact p.Prime] [NeZero p] {bs : BusSemantics p}
    (facts : BusFacts p bs) (denv : VarId → ZMod p) (ks : Array VarId) (hks : 0 < ks.size)
    (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array ℕ) (doms : Array DbDom)
    (hmem : ∀ dd, ∀ hdd : dd < ks.size, DbDomMem p (doms.getD dd (.range 0)) (denv ks[dd]).val)
    (hitems : ∀ (dd : ℕ) (sregs : Array ℕ), dd < ks.size → DbSRegs denv ks sregs dd →
      dbLevOkY facts items ops sregs (lstart.getD dd 0) (lstart.getD (dd + 1) 0) = true)
    (hval : ∀ (dd : ℕ) (sregs : Array ℕ) (o target : ℕ), ∀ hdd : dd < ks.size,
      (∀ j, j < dd → ∀ hj : j < ks.size, sregs.getD j 0 = (denv ks[j]).val) →
      dbFindPivot p items ops sregs dd (lstart.getD dd 0) (lstart.getD (dd + 1) 0)
        = some (DbPivot.val o target) →
      ∃ b l, dbOpAffine? p ops sregs dd o = some (b, l) ∧
        dbPivotRoot p b l target = (denv ks[dd]).val) :
    DbScanYGood denv ks (dbScanDepth facts items ops lstart doms ks.size 0
      (Array.replicate ks.size 0) #[] #[] 0 false) := by
  exact dbScanY_reach facts denv ks items ops lstart doms hmem hitems hval
    ks.size 0 (le_refl _) hks (Array.replicate ks.size 0) #[] #[] 0 false
    (by rw [Array.size_replicate]) (fun h => by simp at h)
    (fun j hj => absurd hj (by omega))

/-- What the compiled scan's answer forces, given a good mask. -/
theorem dbScanYAnswer_sound [NeZero p] (denv : VarId → ZMod p) (ks : Array VarId)
    (st : DbScanY) (hgood : DbScanYGood denv ks st) :
    ∀ f ∈ (if !st.started then dbZeroAll ks
      else if st.live == 0 then [] else dbForcedOfMask p ks st.vals st.alive 0),
      denv f.1 = f.2 := by
  obtain ⟨hstarted, _, hlive⟩ := hgood
  rw [hstarted]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  by_cases hl : st.live == 0
  · rw [if_pos hl]; intro f hf; simp at hf
  · rw [if_neg hl]
    rcases hlive with h0 | hag
    · exact absurd (by simpa using h0) hl
    · exact dbForcedOfMask_sound denv ks st.vals st.alive (fun j hj hal => hag j hj hal) 0

/-- A register file carrying the assignment on a variable set, for instantiating the gathered
    items' obligations. -/
def dbWitness (denv : VarId → ZMod p) (vs : Array VarId) (nv : ℕ) : Array ℕ :=
  vs.foldl (fun a v => a.set! v.index (denv v).val) (Array.replicate nv 0)

private theorem dbWitnessGo_size (denv : VarId → ZMod p) :
    ∀ (l : List VarId) (a : Array ℕ),
      (l.foldl (fun a v => a.set! v.index (denv v).val) a).size = a.size := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons u rest ih => intro a; rw [List.foldl_cons, ih, dbSet_size]

private theorem dbWitnessGo_untouched (denv : VarId → ZMod p) :
    ∀ (l : List VarId) (a : Array ℕ) (q : ℕ), (∀ u ∈ l, u.index ≠ q) →
      (l.foldl (fun a v => a.set! v.index (denv v).val) a).getD q 0 = a.getD q 0 := by
  intro l
  induction l with
  | nil => intro a q _; rfl
  | cons u rest ih =>
    intro a q hq
    rw [List.foldl_cons, ih _ q (fun u' hu' => hq u' (List.mem_cons_of_mem _ hu')),
      dbSetD_ne _ _ _ _ _ (Ne.symm (hq u List.mem_cons_self))]

private theorem dbWitnessGo_agree (denv : VarId → ZMod p) :
    ∀ (l : List VarId) (a : Array ℕ) (v : VarId), v ∈ l → v.index < a.size →
      (l.foldl (fun a v => a.set! v.index (denv v).val) a).getD v.index 0 = (denv v).val := by
  intro l
  induction l with
  | nil => intro a v hv; simp at hv
  | cons u rest ih =>
    intro a v hv hsz
    rw [List.foldl_cons]
    by_cases hrest : ∃ u' ∈ rest, u'.index = v.index
    · obtain ⟨u', hu', hui⟩ := hrest
      have huv : u' = v := dbVarId_eq _ _ hui
      subst huv
      exact ih _ u' hu' (by rwa [dbSet_size])
    · rcases List.mem_cons.mp hv with rfl | hv'
      · rw [dbWitnessGo_untouched denv rest _ _
          (fun u' hu' hne => hrest ⟨u', hu', hne⟩),
          dbSetD_at _ _ _ _, if_pos hsz]
      · exact absurd ⟨v, hv', rfl⟩ hrest

theorem dbWitness_agree (denv : VarId → ZMod p) (vs : Array VarId) (nv : ℕ)
    (hnv : ∀ v ∈ vs, v.index < nv) :
    DbRegsAgreeA denv (dbWitness denv vs nv) vs := by
  intro v hv
  rw [dbWitness, ← Array.foldl_toList]
  exact dbWitnessGo_agree denv vs.toList _ v (by simpa using hv)
    (by rw [Array.size_replicate]; exact hnv v hv)

/-! ### Preflight -/

/-- A preflighted target's plan is sound on the compiled engine. -/
theorem dbPreflight_soundY [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size)
    (mark : Array ℕ) (gen : ℕ) (xs : Array VarId) (hne : xs.isEmpty = false)
    (hnodup : DbNodupIdx xs) (hnv : ∀ i ∈ xs, i.index < ctx.nv)
    (plan : DbPlan p) (hpre : dbPreflight ctx mark gen xs = some plan) :
    ∀ f ∈ dbRunPlanYNew facts plan, ∀ denv, d.satisfies bs denv → denv f.1 = f.2 := by
  intro f hf denv hsat
  have hg := hgood denv hsat
  rw [dbPreflight] at hpre
  rcases hdoms : dbDomsOf ctx.T xs with _ | doms
  · rw [hdoms] at hpre; simp at hpre
  · rw [hdoms] at hpre
    dsimp only at hpre
    have hmem : ∀ k, ∀ hk : k < xs.size,
        DbDomMem p (doms.getD k (.range 0)) (denv xs[k]).val := fun k hk =>
      hg.tab _ _ (dbDomsOf_get ctx.T xs doms hdoms k hk)
    split_ifs at hpre
    · rw [show plan = DbPlan.done (dbConstantDomains p xs doms) from (Option.some.inj hpre).symm,
        dbRunPlanYNew] at hf
      exact dbConstantDomains_sound denv xs doms hmem f hf
    · set g := dbGather ctx mark gen xs with hgdef
      set ks := (dbOrderKeys ctx.T xs doms).1 with hks
      set ds := (dbOrderKeys ctx.T xs doms).2 with hds
      set lv := dbLevelItems ks g.items g.ivars 0 #[] #[] with hlv
      obtain ⟨hknd, hksub, hkssz, hkdom⟩ := dbOrderKeys_spec ctx.T xs doms ks ds rfl hdoms hnodup
      have hksne : 0 < ks.size := by
        rw [hkssz]
        rcases Nat.eq_zero_or_pos xs.size with h | h
        · rw [show xs.isEmpty = true from by simp [Array.isEmpty, h]] at hne
          exact absurd hne (by simp)
        · exact h
      have hkne : ks.isEmpty = false := by
        have : ks.size ≠ 0 := by omega
        simpa [Array.isEmpty] using this
      rw [show plan = DbPlan.scan ks ds lv.1 lv.2 ctx.constOk from (Option.some.inj hpre).symm,
        dbRunPlanYNew, hg.constOk, hkne] at hf
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at hf
      have hmemk : ∀ k, ∀ hk : k < ks.size,
          DbDomMem p (ds.getD k (.range 0)) (denv ks[k]).val := fun k hk =>
        hg.tab _ _ (hkdom k hk)
      have hgok := dbGather_ok facts denv ctx hg hvl mark gen xs
      obtain ⟨hlsz, hlsz2, hlspec⟩ := dbLevelItems_spec ks g.items g.ivars 0 #[] #[] rfl rfl
        (Nat.zero_le _) (fun i hi => absurd hi (by omega))
      rw [← hlv] at hlsz hlsz2 hlspec
      set C := dbCompilePlan (ks.map (fun v => v.index)) ks.size lv.1 lv.2 with hC
      set wregs := dbWitness denv ks ctx.nv with hwdef
      have hwag : ∀ (vs' : Array VarId), (∀ v ∈ vs', v ∈ ks) →
          DbRegsAgreeA denv wregs vs' := by
        intro vs' hsub v hv
        exact dbWitness_agree denv ks ctx.nv (fun u hu => hnv u (hksub u hu)) v (hsub v hv)
      have hsrc : ∀ dd, DbPivotSrc facts denv ks dd C.items C.ops
          (C.lstart.getD dd 0) (C.lstart.getD (dd + 1) 0) := by
        intro dd pos hlo hhi hps
        rcases dbCompilePlan_from (ks.map (fun v => v.index)) ks.size lv.1 lv.2 dd pos hlo hhi
          with h | ⟨k, hk, hlev, hfrom⟩
        · exact Or.inl h
        · rcases hlspec k (by omega) with hAlw | ⟨heq, hlevq⟩
          · rw [hAlw] at hfrom
            exact Or.inr ⟨DbItem.always, #[], wregs, trivial,
              fun v hv => absurd hv (by simp), hfrom, fun v hv => absurd hv (by simp), rfl⟩
          · have hkg : k < g.items.size := by omega
            have hlevdd : dbItemLevel? ks (g.ivars.getD k #[]) = some dd := by
              rw [hlevq, hlev]
            have hposvs := dbItemLevel?_spec ks (g.ivars.getD k #[]) dd hlevdd
            have hsub : ∀ v ∈ g.ivars.getD k #[], v ∈ ks := by
              intro v hv
              obtain ⟨j, _, hj, he⟩ := hposvs v hv
              exact he ▸ Array.getElem_mem hj
            rw [heq] at hfrom
            exact Or.inr ⟨g.items.getD k DbItem.always, g.ivars.getD k #[], wregs,
              hgok.vars k hkg, hposvs, hfrom, hwag _ hsub, hgok.ok k hkg wregs (hwag _ hsub)⟩
      have hitemsY : ∀ (dd : ℕ) (sregs : Array ℕ), dd < ks.size → DbSRegs denv ks sregs dd →
          dbLevOkY facts C.items C.ops sregs (C.lstart.getD dd 0)
            (C.lstart.getD (dd + 1) 0) = true := by
        intro dd sregs hdd hagg
        refine dbLevOkY_of facts _ _ _ _ _ (fun pos hlo hhi hps => ?_)
        rcases hsrc dd pos hlo hhi hps with h | ⟨it, vs', w', hiv, hpos', hfrom, hagr, hok⟩
        · rw [h]; rfl
        · exact dbXItOk_bridge facts denv ks hknd sregs dd hagg it vs' hiv hpos' _ C.ops
            hfrom w' hagr hok
      have hgoodY := dbScanDepth_good facts denv ks hksne C.items C.ops C.lstart ds hmemk
        hitemsY
        (fun dd sregs o tg hdd hagg h =>
          dbFindPivot_val facts denv ks hknd sregs dd hdd hagg C.items C.ops _ _
            (hsrc dd) o tg h)
      exact dbScanYAnswer_sound denv ks _ hgoodY f hf

/-- A preflighted target's plan is sound. -/
theorem dbPreflight_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size)
    (mark : Array ℕ) (gen : ℕ) (xs : Array VarId) (hne : xs.isEmpty = false)
    (hnodup : DbNodupIdx xs) (hnv : ∀ i ∈ xs, i.index < ctx.nv)
    (plan : DbPlan p) (hpre : dbPreflight ctx mark gen xs = some plan) :
    DbPlanSound facts ctx.nv d plan := by
  refine ⟨?_, dbPreflight_soundY bs facts d ctx hgood hvl mark gen xs hne hnodup hnv plan hpre⟩
  intro regs0 f hf denv hsat
  have hg := hgood denv hsat
  rw [dbPreflight] at hpre
  rcases hdoms : dbDomsOf ctx.T xs with _ | doms
  · rw [hdoms] at hpre; simp at hpre
  · rw [hdoms] at hpre
    dsimp only at hpre
    have hmem : ∀ k, ∀ hk : k < xs.size,
        DbDomMem p (doms.getD k (.range 0)) (denv xs[k]).val := fun k hk =>
      hg.tab _ _ (dbDomsOf_get ctx.T xs doms hdoms k hk)
    split_ifs at hpre
    · -- every domain is a single value: no scan needed
      rw [show plan = DbPlan.done (dbConstantDomains p xs doms) from (Option.some.inj hpre).symm,
        dbRunPlanNew] at hf
      exact dbConstantDomains_sound denv xs doms hmem f hf
    · -- the scan
      set g := dbGather ctx mark gen xs with hgdef
      set ks := (dbOrderKeys ctx.T xs doms).1 with hks
      set ds := (dbOrderKeys ctx.T xs doms).2 with hds
      set lv := dbLevelItems ks g.items g.ivars 0 #[] #[] with hlv
      rw [show plan = DbPlan.scan ks ds lv.1 lv.2 ctx.constOk from (Option.some.inj hpre).symm,
        dbRunPlanNew, hg.constOk] at hf
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at hf
      obtain ⟨hknd, hksub, hkssz, hkdom⟩ := dbOrderKeys_spec ctx.T xs doms ks ds rfl hdoms hnodup
      have hksne : 0 < ks.size := by
        rw [hkssz]
        rcases Nat.eq_zero_or_pos xs.size with h | h
        · rw [show xs.isEmpty = true from by simp [Array.isEmpty, h]] at hne
          exact absurd hne (by simp)
        · exact h
      have hcovr : ∀ i ∈ ks,
          i.index < (if regs0.size == ctx.nv then regs0 else Array.replicate ctx.nv 0).size := by
        intro i hi
        have hix := hnv i (hksub i hi)
        split
        · next hs => rw [show regs0.size = ctx.nv from by simpa using hs]; exact hix
        · rw [Array.size_replicate]; exact hix
      have hmemk : ∀ k, ∀ hk : k < ks.size,
          DbDomMem p (ds.getD k (.range 0)) (denv ks[k]).val := fun k hk =>
        hg.tab _ _ (hkdom k hk)
      have hgok := dbGather_ok facts denv ctx hg hvl mark gen xs
      obtain ⟨hlsz, hlsz2, hlspec⟩ := dbLevelItems_spec ks g.items g.ivars 0 #[] #[] rfl rfl
        (Nat.zero_le _) (fun i hi => absurd hi (by omega))
      rw [← hlv] at hlsz hlsz2 hlspec
      have hitems : ∀ (dd : ℕ) (regs' : Array ℕ), dd < ks.size →
          (∀ d', d' ≤ dd → ∀ h : d' < ks.size, regs'.getD ks[d'].index 0 = (denv ks[d']).val) →
          dbAllOkLev facts lv.1 lv.2 dd regs' 0 = true := by
        intro dd regs' hdd hreg
        have hstep : ∀ i, i < lv.1.size →
            dbItemOk facts regs' (lv.1.getD i DbItem.always) = true ∨
            lv.2.getD i 0 ≠ dd := by
          intro i hi
          rcases hlspec i (by omega) with h | ⟨h1, h2⟩
          · exact Or.inl (by rw [h]; rfl)
          · by_cases hlev : lv.2.getD i 0 = dd
            · refine Or.inl ?_
              rw [h1]
              refine hgok.ok i (by rw [← hlsz]; exact hi) regs' (fun v hv => ?_)
              obtain ⟨j, hjle, hj, hkj⟩ := dbItemLevel?_spec ks (g.ivars.getD i #[])
                (lv.2.getD i 0) h2 v hv
              rw [← hkj]
              exact hreg j (by omega) hj
            · exact Or.inr hlev
        -- walk the item array
        have hall : ∀ (m : ℕ), dbAllOkLev facts lv.1 lv.2 dd regs' m = true := by
          intro m
          induction hnm : lv.1.size - m generalizing m with
          | zero => rw [dbAllOkLev, dif_neg (by omega)]
          | succ n ihm =>
            have hm : m < lv.1.size := by omega
            rw [dbAllOkLev, dif_pos hm]
            by_cases hlev : lv.2.getD m 0 == dd
            · rw [if_pos hlev]
              rcases hstep m hm with h | h
              · rw [dbGetD_lt _ _ DbItem.always hm] at h
                rw [if_pos h]
                exact ihm (m + 1) (by omega)
              · exact absurd (by simpa using hlev) h
            · rw [if_neg hlev]
              exact ihm (m + 1) (by omega)
        exact hall 0
      exact dbScanAnswer_sound denv ks _
        (dbScanBox_good facts denv lv.1 lv.2 ks ds _ hknd hcovr hmemk hitems (fun hemp => by
          have : ks.size = 0 := by simpa [Array.isEmpty] using hemp
          omega)) f hf

/-! ### The target loop -/

theorem dbTargetStep_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size)
    (xs : Array VarId) (hnodup : DbNodupIdx xs) (hnv : ∀ i ∈ xs, i.index < ctx.nv)
    (st : DbTargetSt p) (hst : ∀ plan ∈ st.plans, DbPlanSound facts ctx.nv d plan) :
    ∀ plan ∈ (dbTargetStep ctx xs st).plans, DbPlanSound facts ctx.nv d plan := by
  rw [dbTargetStep]
  split
  · exact hst
  · split
    · exact hst
    · split
      · exact hst
      · dsimp only
        split
        · exact hst
        · split
          · exact hst
          · next plan heq =>
            intro plan' hplan'
            rcases List.mem_cons.mp hplan' with rfl | hrest
            · exact dbPreflight_sound bs facts d ctx hgood hvl _ _ xs
                (by simpa using ‹¬ xs.isEmpty = true›) hnodup hnv plan' heq
            · exact hst plan' hrest

theorem dbTargetsCs_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p) (hshape : DbCtxShape ctx)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size) :
    ∀ (k : ℕ) (st : DbTargetSt p),
      (∀ plan ∈ st.plans, DbPlanSound facts ctx.nv d plan) →
      ∀ plan ∈ (dbTargetsCs ctx k st).plans, DbPlanSound facts ctx.nv d plan := by
  intro k
  induction hn : ctx.csVars.size - k generalizing k with
  | zero => intro st hst; rw [dbTargetsCs, dif_neg (by omega)]; exact hst
  | succ n ih =>
    intro st hst
    have hlt : k < ctx.csVars.size := by omega
    rw [dbTargetsCs, dif_pos hlt]
    refine ih (k + 1) (by omega) _ (dbTargetStep_sound bs facts d ctx hgood hvl _ ?_ ?_ st hst)
    · have := hshape.csNodup k; rwa [dbGetD_lt _ _ _ hlt] at this
    · intro i hi
      exact hshape.csNv k i (by rwa [dbGetD_lt _ _ _ hlt])

theorem dbTargetsBis_sound [Fact p.Prime] [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (ctx : DbCtx p) (hshape : DbCtxShape ctx)
    (hgood : ∀ denv, d.satisfies bs denv → DbCtxGood facts denv ctx)
    (hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size) :
    ∀ (k : ℕ) (st : DbTargetSt p),
      (∀ plan ∈ st.plans, DbPlanSound facts ctx.nv d plan) →
      ∀ plan ∈ (dbTargetsBis ctx k st).plans, DbPlanSound facts ctx.nv d plan := by
  intro k
  induction hn : ctx.biVars.size - k generalizing k with
  | zero => intro st hst; rw [dbTargetsBis, dif_neg (by omega)]; exact hst
  | succ n ih =>
    intro st hst
    have hlt : k < ctx.biVars.size := by omega
    rw [dbTargetsBis, dif_pos hlt]
    refine ih (k + 1) (by omega) _ (dbTargetStep_sound bs facts d ctx hgood hvl _ ?_ ?_ st hst)
    · have := hshape.biNodup k; rwa [dbGetD_lt _ _ _ hlt] at this
    · intro i hi
      exact hshape.biNv k i (by rwa [dbGetD_lt _ _ _ hlt])

/-! ### The run and the solution map -/

/-- `dbRunPlans_sound` for the hybrid engine: each plan contributes either engine's answer, and
    `DbPlanSound` covers both. -/
theorem dbRunPlansFast_sound {bs : BusSemantics p} (facts : BusFacts p bs) (nv : ℕ)
    (d : DenseConstraintSystem p) (plans : List (DbPlan p))
    (hplans : ∀ plan ∈ plans, DbPlanSound facts nv d plan) :
    ∀ forced ∈ dbRunPlansFast facts nv plans, ∀ f ∈ forced,
      ∀ denv, d.satisfies bs denv → denv f.1 = f.2 := by
  rw [dbRunPlansFast]
  have key : ∀ (l : List (DbPlan p)) (st : Array ℕ × List (List (VarId × ZMod p))),
      (∀ plan ∈ l, DbPlanSound facts nv d plan) →
      (∀ forced ∈ st.2, ∀ f ∈ forced, ∀ denv, d.satisfies bs denv → denv f.1 = f.2) →
      ∀ forced ∈ (l.foldl (dbRunPlanH facts nv) st).2, ∀ f ∈ forced,
        ∀ denv, d.satisfies bs denv → denv f.1 = f.2 := by
    intro l
    induction l with
    | nil => intro st _ hst; exact hst
    | cons pl rest ih =>
      intro st hpl hst
      refine ih _ (fun plan hplan => hpl plan (List.mem_cons_of_mem _ hplan)) ?_
      intro forced hforced f hf denv hsat
      rcases dbRunPlanH_snd facts nv st pl with hsnd | hsnd <;> rw [hsnd] at hforced
      · rcases List.mem_cons.mp hforced with rfl | hrest
        · exact (hpl pl List.mem_cons_self).1 st.1 f hf denv hsat
        · exact hst forced hrest f hf denv hsat
      · rcases List.mem_cons.mp hforced with rfl | hrest
        · exact (hpl pl List.mem_cons_self).2 f hf denv hsat
        · exact hst forced hrest f hf denv hsat
  intro forced hforced
  rw [List.mem_reverse] at hforced
  exact key plans ⟨#[], []⟩ hplans (fun forced hf => by simp at hf) forced hforced

/-- Every constant the run collects into the array is forced by every satisfying assignment. -/
theorem dbSolvedOf_sound {bs : BusSemantics p} (d : DenseConstraintSystem p) (nv : ℕ)
    (results : List (List (VarId × ZMod p)))
    (hres : ∀ forced ∈ results, ∀ f ∈ forced, ∀ denv, d.satisfies bs denv → denv f.1 = f.2) :
    ∀ (q : ℕ) (c : ZMod p), (dbSolvedOf nv results).1.getD q none = some c →
      ∀ denv, d.satisfies bs denv → denv ⟨q⟩ = c := by
  have inner : ∀ (l : List (VarId × ZMod p)) (st : Array (Option (ZMod p)) × Bool),
      (∀ f ∈ l, ∀ denv, d.satisfies bs denv → denv f.1 = f.2) →
      (∀ q c, st.1.getD q none = some c → ∀ denv, d.satisfies bs denv → denv ⟨q⟩ = c) →
      ∀ q c, (l.foldl (fun st f => (st.1.set! f.1.index (some f.2), true)) st).1.getD q none
        = some c → ∀ denv, d.satisfies bs denv → denv ⟨q⟩ = c := by
    intro l
    induction l with
    | nil => intro st _ hst; exact hst
    | cons f rest ih =>
      intro st hf hst
      refine ih _ (fun g hg => hf g (List.mem_cons_of_mem _ hg)) (fun q c hq denv hsat => ?_)
      by_cases hqi : q = f.1.index
      · rw [hqi] at hq ⊢
        rw [dbSetD_at st.1 f.1.index (some f.2) none] at hq
        split at hq
        · rw [show c = f.2 from (Option.some.inj hq).symm,
            show (⟨f.1.index⟩ : VarId) = f.1 from rfl]
          exact hf f List.mem_cons_self denv hsat
        · simp at hq
      · rw [dbSetD_ne st.1 f.1.index q (some f.2) none hqi] at hq
        exact hst q c hq denv hsat
  have outer : ∀ (l : List (List (VarId × ZMod p))) (st : Array (Option (ZMod p)) × Bool),
      (∀ forced ∈ l, ∀ f ∈ forced, ∀ denv, d.satisfies bs denv → denv f.1 = f.2) →
      (∀ q c, st.1.getD q none = some c → ∀ denv, d.satisfies bs denv → denv ⟨q⟩ = c) →
      ∀ q c, (l.foldl (fun st forced =>
        forced.foldl (fun st f => (st.1.set! f.1.index (some f.2), true)) st) st).1.getD q none
        = some c → ∀ denv, d.satisfies bs denv → denv ⟨q⟩ = c := by
    intro l
    induction l with
    | nil => intro st _ hst; exact hst
    | cons forced rest ih =>
      intro st hforced hst
      exact ih _ (fun l' hl' => hforced l' (List.mem_cons_of_mem _ hl'))
        (inner forced st (hforced forced List.mem_cons_self) hst)
  rw [dbSolvedOf]
  exact outer results _ hres (fun q c hq => by
    rw [dbGetD_replicate] at hq
    split at hq <;> simp at hq)

/-! ### The fused context build

The four walks of `dbBuildCtxFast` are proved directly: the two collecting walks fix each
position's variable list, resolved facts and domain table; the two item walks fix each position's
item. The on-demand table growth is invisible to `DbTab.get` (`dbTab_grow_get`), so `insertG`
reads exactly like `insert`. -/

private theorem dbTab_grow_get (dom : Array (Option DbDom)) (n j : ℕ) :
    (⟨dom ++ Array.replicate n none⟩ : DbTab p).get j = (⟨dom⟩ : DbTab p).get j := by
  simp only [DbTab.get]
  rcases Nat.lt_or_ge j dom.size with h | h
  · rw [dbGetD_lt _ _ _ (by simp; omega), dbGetD_lt _ _ _ h, Array.getElem_append_left h]
  · rw [dbGetD_ge _ _ _ h]
    rcases Nat.lt_or_ge j (dom ++ Array.replicate n none).size with h2 | h2
    · rw [dbGetD_lt _ _ _ h2, Array.getElem_append_right h, Array.getElem_replicate]
    · rw [dbGetD_ge _ _ _ h2]

private theorem dbTabSound_insertG (denv : VarId → ZMod p) (T : DbTab p) (i : ℕ) (dm : DbDom)
    (hT : DbTabSound p denv T) (hdm : DbDomMem p dm (denv ⟨i⟩).val) :
    DbTabSound p denv (T.insertG i dm) := by
  rcases T with ⟨dom⟩
  rw [show (⟨dom⟩ : DbTab p).insertG i dm
      = DbTab.insert ⟨if i < dom.size then dom
          else dom ++ Array.replicate (max (dom.size * 2) (i + 1) - dom.size) none⟩ i dm from rfl]
  refine dbTabSound_insert denv _ i dm (fun j dj hj => hT j dj ?_) hdm
  have hgrow := dbTab_grow_get (p := p) dom (max (dom.size * 2) (i + 1) - dom.size) j
  simp only [DbTab.get] at hj hgrow ⊢
  split at hj
  · exact hj
  · rw [← hgrow]; exact hj

private theorem dbAddConstraintVarsG_sound [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p)
    (c : DenseExpr p) (hc : c.eval denv = 0) (vs : Array VarId) (hvs : vs.size ≤ 3)
    (hsub : ∀ v ∈ c.vars, v ∈ vs) :
    ∀ (k : ℕ) (T : DbTab p), DbTabSound p denv T →
      DbTabSound p denv (dbAddConstraintVarsG c vs k T) := by
  intro k
  induction hk : vs.size - k generalizing k with
  | zero =>
    intro T hT
    rw [dbAddConstraintVarsG, dif_neg (by omega)]
    exact hT
  | succ n ih =>
    intro T hT
    have hlt : k < vs.size := by omega
    rw [dbAddConstraintVarsG, dif_pos hlt]
    split
    · next rs hr =>
      refine ih (k + 1) (by omega) _ (dbTabSound_insertG denv T _ _ hT ?_)
      refine dbDomMem_explicit _ _ ?_
      have hmem : denv vs[k] ∈ rs := dbRootsAt_sound vs hvs k hlt c hsub rs hr denv hc
      simpa using List.mem_map.mpr ⟨denv vs[k], hmem, rfl⟩
    · exact ih (k + 1) (by omega) T hT

/-- Walk 1 records one variable list per constraint, in order. -/
private theorem dbCsWalk_vars : ∀ (cs : List (DenseExpr p)) (csVars : Array (Array VarId))
    (nv : ℕ) (T : DbTab p),
    (dbCsWalk cs csVars nv T).1.size = csVars.size + cs.length ∧
    (∀ pos, pos < csVars.size →
      (dbCsWalk cs csVars nv T).1.getD pos #[] = csVars.getD pos #[]) ∧
    (∀ i, ∀ hi : i < cs.length,
      (dbCsWalk cs csVars nv T).1.getD (csVars.size + i) #[] = dbVarsOf cs[i] #[]) := by
  intro cs
  induction cs with
  | nil => intro csVars nv T; exact ⟨by rw [dbCsWalk]; simp, fun _ _ => by rw [dbCsWalk],
      fun i hi => absurd hi (by simp)⟩
  | cons c rest ih =>
    intro csVars nv T
    rw [dbCsWalk]
    obtain ⟨hsz, hpre, hat⟩ := ih (csVars.push (dbVarsOf c (Array.emptyWithCapacity 4)))
      ((dbVarsOf c (Array.emptyWithCapacity 4)).foldl (init := nv) fun b v => max b (v.index + 1))
      (if (dbVarsOf c (Array.emptyWithCapacity 4)).size ≤ 3 then
        dbAddConstraintVarsG c (dbVarsOf c (Array.emptyWithCapacity 4)) 0 T else T)
    refine ⟨by rw [hsz, Array.size_push]; simp; omega, fun pos hpos => ?_, fun i hi => ?_⟩
    · rw [hpre pos (by rw [Array.size_push]; omega), dbPushGetD _ _ _ _ hpos]
    · cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hpre csVars.size (by rw [Array.size_push]; omega),
          dbPushGetD_at csVars _ csVars.size _ rfl]
        rfl
      | succ j =>
        have := hat j (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hi))
        rw [Array.size_push] at this
        simp only [List.getElem_cons_succ]
        rw [show csVars.size + (j + 1) = csVars.size + 1 + j from by omega, this]

private theorem dbCsWalk_nv : ∀ (cs : List (DenseExpr p)) (csVars : Array (Array VarId))
    (nv : ℕ) (T : DbTab p), nv ≤ (dbCsWalk cs csVars nv T).2.1 ∧
      (∀ i, ∀ hi : i < cs.length, ∀ v ∈ dbVarsOf cs[i] (Array.emptyWithCapacity 4),
        v.index < (dbCsWalk cs csVars nv T).2.1) := by
  intro cs
  induction cs with
  | nil => intro csVars nv T; exact ⟨by rw [dbCsWalk], fun i hi => absurd hi (by simp)⟩
  | cons c rest ih =>
    intro csVars nv T
    rw [dbCsWalk]
    set vs := dbVarsOf c (Array.emptyWithCapacity 4) with hvs
    set nv' := vs.foldl (init := nv) (fun b v => max b (v.index + 1)) with hnv'
    have hge : nv ≤ nv' := by rw [hnv', ← Array.foldl_toList]; exact dbFoldMaxL_ge vs.toList nv
    obtain ⟨hge', hmem⟩ := ih (csVars.push vs) nv'
      (if vs.size ≤ 3 then dbAddConstraintVarsG c vs 0 T else T)
    refine ⟨Nat.le_trans hge hge', fun i hi v hv => ?_⟩
    cases i with
    | zero =>
      refine Nat.lt_of_lt_of_le ?_ hge'
      rw [hnv', ← Array.foldl_toList]
      exact dbFoldMaxL_mem vs.toList nv v (by simpa using hv)
    | succ j => exact hmem j (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hi)) v hv

private theorem dbCsWalk_tab [Fact p.Prime] [NeZero p] (denv : VarId → ZMod p) :
    ∀ (cs : List (DenseExpr p)), (∀ c ∈ cs, c.eval denv = 0) →
      ∀ (csVars : Array (Array VarId)) (nv : ℕ) (T : DbTab p), DbTabSound p denv T →
        DbTabSound p denv (dbCsWalk cs csVars nv T).2.2 := by
  intro cs
  induction cs with
  | nil => intro _ csVars nv T hT; rw [dbCsWalk]; exact hT
  | cons c rest ih =>
    intro hcs csVars nv T hT
    rw [dbCsWalk]
    refine ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) _ _ _ ?_
    split
    · next hsz =>
      exact dbAddConstraintVarsG_sound denv c (hcs c List.mem_cons_self) _ hsz
        (fun v hv => (dbVarsOf_mem c _).2 v hv) 0 T hT
    · exact hT

private theorem dbBusSlotsG_sound [NeZero p] {bs : BusSemantics p} (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) :
    ∀ (rest : List (DenseExpr p)) (ps : List (Option (ZMod p))) (slot : ℕ) (seen : Array VarId)
      (inf : Bool) (T : DbTab p),
      (∀ k, rest[k]? = bi.payload[slot + k]?) → DbTabSound p denv T →
      DbTabSound p denv (dbBusSlotsG facts bi bi.multiplicity.constValue?
        (bi.payload.map DenseExpr.constValue?) rest ps slot seen inf T).2 := by
  intro rest
  induction rest with
  | nil => intro ps slot seen inf T _ hT; exact hT
  | cons e rest ih =>
    intro ps slot seen inf T hsuf hT
    have hshift : ∀ k, rest[k]? = bi.payload[(slot + 1) + k]? := by
      intro k
      have := hsuf (k + 1)
      simpa [Nat.add_assoc, Nat.add_comm 1 k, Nat.add_left_comm] using this
    cases e with
    | var i =>
      rw [dbBusSlotsG]
      dsimp only
      by_cases hseen : seen.contains i
      · rw [if_pos hseen]; exact ih ps.tail (slot + 1) seen inf T hshift hT
      · rw [if_neg hseen]
        have hslot : bi.payload[slot]? = some (.var i) := by
          have := hsuf 0; simpa using this.symm
        rcases hsb : dbSlotBound facts bi bi.multiplicity.constValue?
          (bi.payload.map DenseExpr.constValue?) slot with _ | bound
        · dsimp only; exact ih ps.tail (slot + 1) (seen.push i) true T hshift hT
        · dsimp only
          refine ih ps.tail (slot + 1) (seen.push i) inf _ hshift ?_
          by_cases hb : bound ≤ maxDomainBound
          · rw [if_pos hb]
            refine dbTabSound_insertG denv T i.index _ hT ?_
            exact dbDomMem_range bound _ (ZMod.val_lt _)
              (dbSlotBound_sound facts bi slot bound i hslot hsb denv hob)
          · rw [if_neg hb]; exact hT
    | const c => exact ih ps.tail (slot + 1) seen _ T hshift hT
    | add a b => exact ih ps.tail (slot + 1) seen _ T hshift hT
    | mul a b => exact ih ps.tail (slot + 1) seen _ T hshift hT

/-- Walk 2 records one variable list and one resolved-facts entry per interaction, in order. -/
private theorem dbBiWalk_at {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p) :
    ∀ (bis : List (BusInteraction (DenseExpr p))) (biVars : Array (Array VarId))
      (pre : Array (DbBiPre p)) (inf : Array Bool) (nv : ℕ) (T : DbTab p),
      biVars.size = pre.size →
      (dbBiWalk facts bc bis biVars pre inf nv T).1.size = biVars.size + bis.length ∧
      (dbBiWalk facts bc bis biVars pre inf nv T).2.1.size = biVars.size + bis.length ∧
      (∀ pos, pos < biVars.size →
        (dbBiWalk facts bc bis biVars pre inf nv T).1.getD pos #[] = biVars.getD pos #[] ∧
        (dbBiWalk facts bc bis biVars pre inf nv T).2.1.getD pos dbBiPreEmpty
          = pre.getD pos dbBiPreEmpty) ∧
      (∀ i, ∀ hi : i < bis.length,
        (dbBiWalk facts bc bis biVars pre inf nv T).1.getD (biVars.size + i) #[]
            = dbBiVars bis[i] ∧
        (dbBiWalk facts bc bis biVars pre inf nv T).2.1.getD (biVars.size + i) dbBiPreEmpty
            = dbPreOne facts bc bis[i] (dbBiVars bis[i])) := by
  intro bis
  induction bis with
  | nil =>
    intro biVars pre inf nv T hsz
    exact ⟨by rw [dbBiWalk]; simp, by rw [dbBiWalk]; simp [hsz],
      fun _ _ => by rw [dbBiWalk]; exact ⟨rfl, rfl⟩, fun i hi => absurd hi (by simp)⟩
  | cons bi rest ih =>
    intro biVars pre inf nv T hsz
    rw [dbBiWalk]
    obtain ⟨h1, h2, hpre, hat⟩ := ih (biVars.push (dbBiVars bi))
      (pre.push (dbPreOne facts bc bi (dbBiVars bi))) _ _ _ (by simp [hsz])
    refine ⟨by rw [h1, Array.size_push]; simp; omega,
      by rw [h2, Array.size_push]; simp; omega, fun pos hpos => ?_, fun i hi => ?_⟩
    · obtain ⟨ha, hb⟩ := hpre pos (by rw [Array.size_push]; omega)
      exact ⟨by rw [ha, dbPushGetD _ _ _ _ hpos],
        by rw [hb, dbPushGetD _ _ _ _ (by omega)]⟩
    · cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        obtain ⟨ha, hb⟩ := hpre biVars.size (by rw [Array.size_push]; omega)
        exact ⟨by rw [ha, dbPushGetD_at biVars _ biVars.size _ rfl],
          by rw [hb, dbPushGetD_at pre _ biVars.size _ hsz]⟩
      | succ j =>
        obtain ⟨ha, hb⟩ := hat j (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hi))
        rw [Array.size_push] at ha hb
        simp only [List.getElem_cons_succ]
        rw [show biVars.size + (j + 1) = biVars.size + 1 + j from by omega]
        exact ⟨ha, hb⟩

private theorem dbBiWalk_nv {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p) :
    ∀ (bis : List (BusInteraction (DenseExpr p))) (biVars : Array (Array VarId))
      (pre : Array (DbBiPre p)) (inf : Array Bool) (nv : ℕ) (T : DbTab p),
      nv ≤ (dbBiWalk facts bc bis biVars pre inf nv T).2.2.2.1 ∧
      (∀ i, ∀ hi : i < bis.length, ∀ v ∈ dbBiVars bis[i],
        v.index < (dbBiWalk facts bc bis biVars pre inf nv T).2.2.2.1) := by
  intro bis
  induction bis with
  | nil => intro biVars pre inf nv T; exact ⟨by rw [dbBiWalk], fun i hi => absurd hi (by simp)⟩
  | cons bi rest ih =>
    intro biVars pre inf nv T
    rw [dbBiWalk]
    set vars := dbBiVars bi with hvars
    set nv' := vars.foldl (init := nv) (fun b v => max b (v.index + 1)) with hnv'
    have hge : nv ≤ nv' := by rw [hnv', ← Array.foldl_toList]; exact dbFoldMaxL_ge vars.toList nv
    obtain ⟨hge', hmem⟩ := ih (biVars.push vars) (pre.push (dbPreOne facts bc bi vars)) _ _ _
    refine ⟨Nat.le_trans hge hge', fun i hi v hv => ?_⟩
    cases i with
    | zero =>
      refine Nat.lt_of_lt_of_le ?_ hge'
      rw [hnv', ← Array.foldl_toList]
      exact dbFoldMaxL_mem vars.toList nv v (by simpa using hv)
    | succ j => exact hmem j (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hi)) v hv

private theorem dbBiWalk_tab [Fact p.Prime] [NeZero p] {bs : BusSemantics p}
    (facts : BusFacts p bs) (bc : DbBusCache p) (denv : VarId → ZMod p) :
    ∀ (bis : List (BusInteraction (DenseExpr p))),
      (∀ bi ∈ bis, (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) →
      ∀ (biVars : Array (Array VarId)) (pre : Array (DbBiPre p)) (inf : Array Bool) (nv : ℕ)
        (T : DbTab p), DbTabSound p denv T →
        DbTabSound p denv (dbBiWalk facts bc bis biVars pre inf nv T).2.2.2.2 := by
  intro bis
  induction bis with
  | nil => intro _ biVars pre inf nv T hT; rw [dbBiWalk]; exact hT
  | cons bi rest ih =>
    intro hbis biVars pre inf nv T hT
    rw [dbBiWalk]
    have key : ∀ (b : Bool) (X Y : Bool × DbTab p), DbTabSound p denv X.2 →
        DbTabSound p denv Y.2 → DbTabSound p denv (if b = true then X else Y).2 := by
      intro b X Y hX hY
      cases b
      · exact hY
      · exact hX
    refine ih (fun b hb => hbis b (List.mem_cons_of_mem _ hb)) _ _ _ _ _ (key _ _ _ ?_ hT)
    exact dbBusSlotsG_sound facts bi denv (hbis bi List.mem_cons_self) bi.payload
      (bi.payload.map DenseExpr.constValue?) 0 (Array.emptyWithCapacity 4) false T
      (fun m => by simp) hT

/-- Walk 3's item at each position is the constraint itself, or the dropped `.always`. -/
private theorem dbCsWalk2_items {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (csVars : Array (Array VarId)) :
    ∀ (cs : List (DenseExpr p)) (k : ℕ) (regs : Array ℕ) (items : Array (DbItem p))
      (act : Array Bool) (buckets : Array (Array ℕ)) (vlCount : ℕ) (vlItems : Array (DbItem p)),
      items.size = k →
      (dbCsWalk2 facts T cs csVars k regs items act buckets vlCount vlItems).1.size
          = k + cs.length ∧
      (∀ pos, pos < k →
        (dbCsWalk2 facts T cs csVars k regs items act buckets vlCount vlItems).1.getD pos
            DbItem.always = items.getD pos DbItem.always) ∧
      (∀ i, ∀ hi : i < cs.length,
        (dbCsWalk2 facts T cs csVars k regs items act buckets vlCount vlItems).1.getD (k + i)
            DbItem.always = DbItem.always ∨
        (dbCsWalk2 facts T cs csVars k regs items act buckets vlCount vlItems).1.getD (k + i)
            DbItem.always = DbItem.zero cs[i]) ∧
      (∀ item ∈ (dbCsWalk2 facts T cs csVars k regs items act buckets vlCount vlItems).2.2.2.2,
        item ∈ vlItems ∨ item = DbItem.always ∨
          ∃ i, ∃ hi : i < cs.length, item = DbItem.zero cs[i] ∧
            csVars.getD (k + i) #[] = #[]) := by
  intro cs
  induction cs with
  | nil =>
    intro k regs items act buckets vlCount vlItems hsz
    exact ⟨by rw [dbCsWalk2]; simp [hsz], fun _ _ => by rw [dbCsWalk2],
      fun i hi => absurd hi (by simp), fun item hitem => Or.inl (by rwa [dbCsWalk2] at hitem)⟩
  | cons c rest ih =>
    intro k regs items act buckets vlCount vlItems hsz
    rw [dbCsWalk2]
    -- `X` is the head's `(item, registers, redundancy verdict)`, computed before the recursion
    have hkey : ∀ (X : DbItem p × Array ℕ × Bool) (bk : Array (Array ℕ)) (vc : ℕ)
        (vl : Array (DbItem p)), (X.1 = DbItem.always ∨ X.1 = DbItem.zero c) →
        (∀ item ∈ vl, item ∈ vlItems ∨ item = DbItem.always ∨
          ∃ i, ∃ hi : i < (c :: rest).length, item = DbItem.zero (c :: rest)[i] ∧
            csVars.getD (k + i) #[] = #[]) →
        (dbCsWalk2 facts T rest csVars (k + 1) X.2.1 (items.push X.1)
            (act.push (!X.2.2)) bk vc vl).1.size = k + (c :: rest).length ∧
        (∀ pos, pos < k →
          (dbCsWalk2 facts T rest csVars (k + 1) X.2.1 (items.push X.1)
              (act.push (!X.2.2)) bk vc vl).1.getD pos DbItem.always
            = items.getD pos DbItem.always) ∧
        (∀ i, ∀ hi : i < (c :: rest).length,
          (dbCsWalk2 facts T rest csVars (k + 1) X.2.1 (items.push X.1)
              (act.push (!X.2.2)) bk vc vl).1.getD (k + i) DbItem.always = DbItem.always ∨
          (dbCsWalk2 facts T rest csVars (k + 1) X.2.1 (items.push X.1)
              (act.push (!X.2.2)) bk vc vl).1.getD (k + i) DbItem.always
            = DbItem.zero (c :: rest)[i]) ∧
        (∀ item ∈ (dbCsWalk2 facts T rest csVars (k + 1) X.2.1 (items.push X.1)
            (act.push (!X.2.2)) bk vc vl).2.2.2.2,
          item ∈ vlItems ∨ item = DbItem.always ∨
            ∃ i, ∃ hi : i < (c :: rest).length, item = DbItem.zero (c :: rest)[i] ∧
              csVars.getD (k + i) #[] = #[]) := by
      intro X bk vc vl hX hvl
      obtain ⟨h1, h2, h3, h4⟩ := ih (k + 1) X.2.1 (items.push X.1) (act.push (!X.2.2))
        bk vc vl (by rw [Array.size_push, hsz])
      refine ⟨by rw [h1]; simp; omega, fun pos hpos => ?_, fun i hi => ?_, fun item hit => ?_⟩
      · rw [h2 pos (by omega), dbPushGetD _ _ _ _ (by omega)]
      · cases i with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [h2 k (by omega), dbPushGetD_at items _ k _ hsz.symm]
          exact hX
        | succ j =>
          simp only [List.getElem_cons_succ]
          rw [show k + (j + 1) = k + 1 + j from by omega]
          exact h3 j (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hi))
      · rcases h4 item hit with hv | h | ⟨i, hi', heq, hemp⟩
        · exact hvl item hv
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨i + 1, by simpa using Nat.succ_lt_succ hi', by
            simpa using heq, by rw [show k + (i + 1) = k + 1 + i from by omega]; exact hemp⟩)
    rcases hv0 : (csVars.getD k #[])[0]? with _ | v
    · -- the head mentions no variable: its item joins the varless list
      have hvsempty : csVars.getD k #[] = #[] := by
        have hz : (csVars.getD k #[]).size = 0 := by
          rcases Nat.eq_zero_or_pos (csVars.getD k #[]).size with h | h
          · exact h
          · rw [Array.getElem?_eq_getElem h] at hv0; simp at hv0
        exact Array.eq_empty_of_size_eq_zero hz
      have hvlgen : ∀ (it : DbItem p) (b : Bool), (it = DbItem.always ∨ it = DbItem.zero c) →
          ∀ item ∈ (if b = true then vlItems.push it else vlItems),
            item ∈ vlItems ∨ item = DbItem.always ∨
              ∃ i, ∃ hi : i < (c :: rest).length, item = DbItem.zero (c :: rest)[i] ∧
                csVars.getD (k + i) #[] = #[] := by
        intro it b hitem item hmem
        split at hmem
        · rcases Array.mem_push.mp hmem with h' | rfl
          · exact Or.inl h'
          · rcases hitem with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨0, by simp, by simpa using h, by simpa using hvsempty⟩)
        · exact Or.inl hmem
      refine hkey _ _ _ _ ?_ ?_
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · refine hvlgen _ _ ?_
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
    · refine hkey _ _ _ _ ?_ ?_
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact fun item hit => Or.inl hit

private theorem dbCompileRange_vars (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p)
    (mult : DenseExpr p) (vs : Array VarId) (hmult : ∀ v ∈ mult.vars, v ∈ vs)
    (hpay : ∀ x ∈ bi.payload, ∀ v ∈ x.vars, v ∈ vs) :
    ∀ item, dbCompileRange bi e mult = some item → DbItemVars item vs := by
  intro item h
  rw [dbCompileRange] at h
  rcases hm : e.mult? with _ | m
  · rw [hm] at h; simp at h
  · rw [hm] at h
    dsimp only at h
    by_cases hone : zmodIsOne m
    · rw [if_pos hone] at h
      rcases hra : e.rangeAt? with _ | ⟨slot, bound⟩
      · rw [hra] at h; simp at h
      · rw [hra] at h
        dsimp only at h
        rcases hpl : bi.payload[slot]? with _ | value
        · rw [hpl] at h; simp at h
        · rw [hpl] at h
          rw [← Option.some.inj h]
          obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hpl
          exact ⟨hmult, hpay value (heq ▸ List.getElem_mem hlt)⟩
    · rw [if_neg hone] at h; simp at h

private theorem dbCompileByte_vars (e : DbBiPre p) (mult : DenseExpr p) (vs : Array VarId)
    (hmult : ∀ v ∈ mult.vars, v ∈ vs)
    (hb : ∀ b, e.byte? = some b → (∀ v ∈ b.o1.vars, v ∈ vs) ∧ (∀ v ∈ b.o2.vars, v ∈ vs) ∧
      (∀ v ∈ b.result.vars, v ∈ vs)) :
    ∀ item, dbCompileByte e mult = some item → DbItemVars item vs := by
  intro item h
  rw [dbCompileByte] at h
  rcases hby : e.byte? with _ | b
  · rw [hby] at h; simp at h
  · rw [hby] at h
    obtain ⟨h1, h2, h3⟩ := hb b hby
    dsimp only at h
    rcases hop : b.op? with _ | opv
    · rw [hop] at h; simp at h
    · rw [hop] at h
      dsimp only at h
      repeat' split at h
      all_goals first
        | (rw [← Option.some.inj h]; exact ⟨hmult, h1, h2, h3⟩)
        | simp at h

/-- Every expression a compiled interaction item reads is one of the interaction's own, so the
    item's variables are among `dbBiVars`. -/
private theorem dbCompileBi_vars {bs : BusSemantics p} (facts : BusFacts p bs)
    (bc : DbBusCache p) (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p)
    (hpre : DbBiPreOf facts bi e) : DbItemVars (dbCompileBi facts bc bi e) (dbBiVars bi) := by
  have hmult : ∀ v ∈ bi.multiplicity.vars, v ∈ dbBiVars bi := fun v hv =>
    (dbVarsOfList_mem bi.payload (dbVarsOf bi.multiplicity (Array.emptyWithCapacity 4))).1 v
      ((dbVarsOf_mem bi.multiplicity _).2 v hv)
  have hpay : ∀ x ∈ bi.payload, ∀ v ∈ x.vars, v ∈ dbBiVars bi := fun x hx v hv =>
    (dbVarsOfList_mem bi.payload (dbVarsOf bi.multiplicity (Array.emptyWithCapacity 4))).2 x hx v hv
  have hbyte : ∀ b, e.byte? = some b →
      (∀ v ∈ b.o1.vars, v ∈ dbBiVars bi) ∧ (∀ v ∈ b.o2.vars, v ∈ dbBiVars bi) ∧
      (∀ v ∈ b.result.vars, v ∈ dbBiVars bi) := by
    intro b hb
    obtain ⟨_, _, hbb, _, _, _⟩ := hpre
    obtain ⟨_, op, hdec, _⟩ := hbb b hb
    obtain ⟨m1, m2, m3⟩ := b.spec.decode_mem bi.payload op b.o1 b.o2 b.result hdec
    exact ⟨hpay _ m1, hpay _ m2, hpay _ m3⟩
  have hother : DbItemVars (dbCompileOther bi e bi.multiplicity) (dbBiVars bi) := by
    rw [dbCompileOther]
    rcases hr : dbCompileRange bi e bi.multiplicity with _ | it1
    · dsimp only
      rcases hbb : dbCompileByte e bi.multiplicity with _ | it2
      · exact ⟨hmult, fun x hx v hv => hpay x hx v hv⟩
      · exact dbCompileByte_vars e bi.multiplicity _ hmult hbyte it2 hbb
    · exact dbCompileRange_vars bi e bi.multiplicity _ hmult hpay it1 hr
  rw [dbCompileBi]
  split
  · trivial
  · dsimp only
    split
    · next x width heq =>
      have hx : x ∈ bi.payload := by rw [heq]; simp
      have hw : width ∈ bi.payload := by rw [heq]; simp
      split
      · split
        · split
          · exact ⟨hmult, hpay x hx⟩
          · exact ⟨hmult, hpay x hx, hpay width hw⟩
        · exact ⟨hmult, hpay x hx, hpay width hw⟩
      · split
        · exact ⟨hmult, hpay x hx, hpay width hw⟩
        · exact hother
    · exact hother

/-- Walk 4's item at each position is the interaction's compiled item, or the dropped `.always`. -/
private theorem dbBiWalk2_items {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (T : DbTab p) (pre : Array (DbBiPre p)) (biInf : Array Bool) :
    ∀ (bis : List (BusInteraction (DenseExpr p))) (k : ℕ) (items : Array (DbItem p))
      (dred : Array Bool) (buckets : Array (Array ℕ)) (summary : ℕ × Bool × Bool × Bool),
      items.size = k →
      (dbBiWalk2 facts bc T bis pre biInf k items dred buckets summary).1.size = k + bis.length ∧
      (∀ pos, pos < k →
        (dbBiWalk2 facts bc T bis pre biInf k items dred buckets summary).1.getD pos
          DbItem.always = items.getD pos DbItem.always) ∧
      (∀ i, ∀ hi : i < bis.length,
        (dbBiWalk2 facts bc T bis pre biInf k items dred buckets summary).1.getD (k + i)
            DbItem.always = DbItem.always ∨
        (dbBiWalk2 facts bc T bis pre biInf k items dred buckets summary).1.getD (k + i)
            DbItem.always = dbCompileBi facts bc bis[i] (pre.getD (k + i) dbBiPreEmpty)) ∧
      (summary.2.2.2 = true →
        (∀ i, ∀ hi : i < bis.length, (pre.getD (k + i) dbBiPreEmpty).vars[0]? = none →
          dbItemOk facts #[]
            (dbCompileBi facts bc bis[i] (pre.getD (k + i) dbBiPreEmpty)) = true) →
        (dbBiWalk2 facts bc T bis pre biInf k items dred buckets summary).2.2.2.2.2.2 = true) := by
  intro bis
  induction bis with
  | nil =>
    intro k items dred buckets summary hsz
    exact ⟨by rw [dbBiWalk2]; simp [hsz], fun _ _ => by rw [dbBiWalk2],
      fun i hi => absurd hi (by simp), fun hs _ => by rwa [dbBiWalk2]⟩
  | cons bi rest ih =>
    intro k items dred buckets summary hsz
    rw [dbBiWalk2]
    have hkey : ∀ (it : DbItem p) (drb : Bool) (bk : Array (Array ℕ))
        (sm : ℕ × Bool × Bool × Bool),
        (it = DbItem.always ∨ it = dbCompileBi facts bc bi (pre.getD k dbBiPreEmpty)) →
        (summary.2.2.2 = true →
          (∀ i, ∀ hi : i < (bi :: rest).length, (pre.getD (k + i) dbBiPreEmpty).vars[0]? = none →
            dbItemOk facts #[]
              (dbCompileBi facts bc (bi :: rest)[i] (pre.getD (k + i) dbBiPreEmpty)) = true) →
          sm.2.2.2 = true) →
        (dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push it) (dred.push drb)
            bk sm).1.size = k + (bi :: rest).length ∧
        (∀ pos, pos < k →
          (dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push it) (dred.push drb)
            bk sm).1.getD pos DbItem.always = items.getD pos DbItem.always) ∧
        (∀ i, ∀ hi : i < (bi :: rest).length,
          (dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push it) (dred.push drb)
              bk sm).1.getD (k + i) DbItem.always = DbItem.always ∨
          (dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push it) (dred.push drb)
              bk sm).1.getD (k + i) DbItem.always
            = dbCompileBi facts bc (bi :: rest)[i] (pre.getD (k + i) dbBiPreEmpty)) ∧
        (summary.2.2.2 = true →
          (∀ i, ∀ hi : i < (bi :: rest).length, (pre.getD (k + i) dbBiPreEmpty).vars[0]? = none →
            dbItemOk facts #[]
              (dbCompileBi facts bc (bi :: rest)[i] (pre.getD (k + i) dbBiPreEmpty)) = true) →
          (dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push it) (dred.push drb)
            bk sm).2.2.2.2.2.2 = true) := by
      intro it drb bk sm hit hsm
      obtain ⟨h1, h2, h3, h4⟩ := ih (k + 1) (items.push it) (dred.push drb) bk sm
        (by rw [Array.size_push, hsz])
      refine ⟨by rw [h1]; simp; omega, fun pos hpos => ?_, fun i hi => ?_, fun hs hall => ?_⟩
      · rw [h2 pos (by omega), dbPushGetD _ _ _ _ (by omega)]
      · cases i with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [h2 k (by omega), dbPushGetD_at items _ k _ hsz.symm]
          exact hit
        | succ j =>
          simp only [List.getElem_cons_succ]
          rw [show k + (j + 1) = k + 1 + j from by omega]
          exact h3 j (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hi))
      · refine h4 (hsm hs hall) (fun i hi' hvar => ?_)
        have hnext := hall (i + 1) (by simpa using Nat.succ_lt_succ hi')
          (by rw [show k + (i + 1) = k + 1 + i from by omega]; exact hvar)
        rw [show k + 1 + i = k + (i + 1) from by omega]
        simpa using hnext
    have hit : (if ((pre.getD k dbBiPreEmpty).usable &&
          (dbBoxOf T (pre.getD k dbBiPreEmpty).vars 0 1).isSome) = true then
            dbCompileBi facts bc bi (pre.getD k dbBiPreEmpty) else DbItem.always)
        = DbItem.always ∨
        (if ((pre.getD k dbBiPreEmpty).usable &&
          (dbBoxOf T (pre.getD k dbBiPreEmpty).vars 0 1).isSome) = true then
            dbCompileBi facts bc bi (pre.getD k dbBiPreEmpty) else DbItem.always)
        = dbCompileBi facts bc bi (pre.getD k dbBiPreEmpty) := by
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
    rcases hv0 : (pre.getD k dbBiPreEmpty).vars[0]? with _ | v
    · refine hkey _ _ _ _ hit (fun hs hall => ?_)
      split
      · next hus =>
        rw [hs, Bool.and_eq_true]
        refine ⟨rfl, ?_⟩
        rcases hit with h | h
        · rw [h]; rfl
        · rw [h]
          exact hall 0 (by simp) (by simpa using hv0)
      · exact hs
    · exact hkey _ _ _ _ hit (fun hs _ => hs)

theorem dbBuildCtxFast_shape (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DbCtxShape (dbBuildCtxFast bs facts d) := by
  have hcsV : (dbBuildCtxFast bs facts d).csVars
      = (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).1 := rfl
  have hbiV : (dbBuildCtxFast bs facts d).biVars
      = (dbBiWalk facts (dbBusCacheOf facts
          (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)) d.busInteractions
          #[] #[] #[] (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
          (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).1 := rfl
  have hnvE : (dbBuildCtxFast bs facts d).nv
      = (dbBiWalk facts (dbBusCacheOf facts
          (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)) d.busInteractions
          #[] #[] #[] (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
          (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).2.2.2.1 := rfl
  obtain ⟨hsz1, -, hat1⟩ := dbCsWalk_vars d.algebraicConstraints #[] 0 (⟨#[]⟩ : DbTab p)
  obtain ⟨hge1, hmem1⟩ := dbCsWalk_nv d.algebraicConstraints #[] 0 (⟨#[]⟩ : DbTab p)
  obtain ⟨hsz2, -, -, hat2⟩ := dbBiWalk_at facts (dbBusCacheOf facts
      (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)) d.busInteractions #[] #[] #[]
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2 rfl
  obtain ⟨hge2, hmem2⟩ := dbBiWalk_nv facts (dbBusCacheOf facts
      (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)) d.busInteractions #[] #[] #[]
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2
  simp only [Array.size_empty, Nat.zero_add] at hsz1 hsz2 hat1 hat2
  refine ⟨fun pos => ?_, fun pos i hi => ?_, fun pos => ?_, fun pos i hi => ?_⟩
  · rw [hcsV]
    rcases Nat.lt_or_ge pos d.algebraicConstraints.length with h | h
    · rw [hat1 pos h]; exact dbVarsOf_nodupIdx _
    · rw [dbGetD_ge _ _ _ (by omega)]; exact dbNodupIdx_empty
  · rw [hcsV] at hi
    rw [hnvE]
    rcases Nat.lt_or_ge pos d.algebraicConstraints.length with h | h
    · rw [hat1 pos h] at hi
      exact Nat.lt_of_lt_of_le (hmem1 pos h i hi) hge2
    · rw [dbGetD_ge _ _ _ (by omega)] at hi; simp at hi
  · rw [hbiV]
    rcases Nat.lt_or_ge pos d.busInteractions.length with h | h
    · rw [(hat2 pos h).1]; exact dbBiVars_nodupIdx _
    · rw [dbGetD_ge _ _ _ (by omega)]; exact dbNodupIdx_empty
  · rw [hbiV] at hi
    rw [hnvE]
    rcases Nat.lt_or_ge pos d.busInteractions.length with h | h
    · rw [(hat2 pos h).1] at hi
      exact hmem2 pos h i hi
    · rw [dbGetD_ge _ _ _ (by omega)] at hi; simp at hi

theorem dbBuildCtxFast_good [Fact p.Prime] [NeZero p] (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (denv : VarId → ZMod p)
    (hsat : d.satisfies bs denv) : DbCtxGood facts denv (dbBuildCtxFast bs facts d) := by
  have hcs : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := fun c hc => hsat.1 c hc
  have hbis : ∀ bi ∈ d.busInteractions,
      (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv) :=
    fun bi hbi => hsat.2 bi hbi
  -- the bus cache resolves every interaction's facts, so the pre-pass entries are faithful
  have hfoldge : ∀ (l : List (BusInteraction (DenseExpr p))) (m : ℕ),
      m ≤ l.foldl (fun m b => max m (b.busId + 1)) m := by
    intro l
    induction l with
    | nil => intro m; exact Nat.le_refl m
    | cons y r ihy => intro m; exact le_trans (le_max_left _ _) (ihy _)
  have hfoldmem : ∀ (l : List (BusInteraction (DenseExpr p))) (m : ℕ)
      (b : BusInteraction (DenseExpr p)), b ∈ l →
      b.busId < l.foldl (fun m b => max m (b.busId + 1)) m := by
    intro l
    induction l with
    | nil => intro m b hb; simp at hb
    | cons x rest ihr =>
      intro m b hb
      rcases List.mem_cons.mp hb with rfl | hrest
      · exact lt_of_lt_of_le (by omega) (hfoldge rest (max m (b.busId + 1)))
      · exact ihr _ b hrest
  have hbcok : ∀ bi ∈ d.busInteractions, DbBusCacheOk facts (dbBusCacheOf facts
      (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)) bi.busId := fun bi hbi =>
    dbBusCacheOf_ok facts _ _ (hfoldmem d.busInteractions 0 bi hbi)
  obtain ⟨hsz1, -, hat1⟩ := dbCsWalk_vars d.algebraicConstraints #[] 0 (⟨#[]⟩ : DbTab p)
  obtain ⟨hsz2, hsz2', -, hat2⟩ := dbBiWalk_at facts (dbBusCacheOf facts
      (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)) d.busInteractions #[] #[] #[]
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2 rfl
  simp only [Array.size_empty, Nat.zero_add] at hsz1 hsz2 hsz2' hat1 hat2
  set bc := dbBusCacheOf facts
    (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0) with hbcdef
  set pre := (dbBiWalk facts bc d.busInteractions #[] #[] #[]
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).2.1 with hpredef
  have hpre : ∀ i, ∀ hi : i < d.busInteractions.length,
      pre.getD i dbBiPreEmpty = dbPreOne facts bc d.busInteractions[i]
        (dbBiVars d.busInteractions[i]) := fun i hi => (hat2 i hi).2
  have hpreOf : ∀ i, ∀ hi : i < d.busInteractions.length,
      DbBiPreOf facts d.busInteractions[i] (pre.getD i dbBiPreEmpty) := by
    intro i hi
    rw [hpre i hi]
    exact dbPreOne_preOf facts bc _ (hbcok _ (List.getElem_mem hi)) _
  -- the table: constraint roots, then bus slot bounds, then the byte-operand cosets
  have htab : DbTabSound p denv (dbBuildCtxFast bs facts d).T := by
    show DbTabSound p denv (dbBytePhase pre 0 (dbBiWalk facts bc d.busInteractions #[] #[] #[]
      (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
      (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).2.2.2.2)
    refine dbBytePhase_sound facts denv pre (fun k hk => ?_) 0 _ ?_
    · have hk' : k < d.busInteractions.length := by omega
      refine ⟨d.busInteractions[k], ?_, hbis _ (List.getElem_mem hk')⟩
      rw [← dbGetD_lt _ _ dbBiPreEmpty hk]
      exact hpreOf k hk'
    · refine dbBiWalk_tab facts bc denv d.busInteractions hbis _ _ _ _ _ ?_
      exact dbCsWalk_tab denv d.algebraicConstraints hcs _ _ _ (dbTabSound_empty denv 0)
  -- items, position by position
  obtain ⟨hcssz, -, hcsat, hcsvl⟩ := dbCsWalk2_items facts (dbBuildCtxFast bs facts d).T
    (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).1 d.algebraicConstraints 0
    (Array.replicate (dbBuildCtxFast bs facts d).nv 0) #[] #[]
    (Array.replicate (dbBuildCtxFast bs facts d).nv #[]) 0 #[] rfl
  obtain ⟨hbisz, -, hbiat, hbicon⟩ := dbBiWalk2_items facts bc (dbBuildCtxFast bs facts d).T pre
    (dbBiWalk facts bc d.busInteractions #[] #[] #[]
      (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
      (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).2.2.1
    d.busInteractions 0 #[] #[] (Array.replicate (dbBuildCtxFast bs facts d).nv #[])
    (0, false, true, true) rfl
  simp only [Nat.zero_add] at hcssz hcsat hcsvl hbisz hbiat hbicon
  have hcsItems : (dbBuildCtxFast bs facts d).csItems
      = (dbCsWalk2 facts (dbBuildCtxFast bs facts d).T d.algebraicConstraints
          (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).1 0
          (Array.replicate (dbBuildCtxFast bs facts d).nv 0) #[] #[]
          (Array.replicate (dbBuildCtxFast bs facts d).nv #[]) 0 #[]).1 := rfl
  have hcsVarless : (dbBuildCtxFast bs facts d).csVarlessItems
      = (dbCsWalk2 facts (dbBuildCtxFast bs facts d).T d.algebraicConstraints
          (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).1 0
          (Array.replicate (dbBuildCtxFast bs facts d).nv 0) #[] #[]
          (Array.replicate (dbBuildCtxFast bs facts d).nv #[]) 0 #[]).2.2.2.2 := rfl
  have hbiItems : (dbBuildCtxFast bs facts d).biItems
      = (dbBiWalk2 facts bc (dbBuildCtxFast bs facts d).T d.busInteractions pre
          (dbBiWalk facts bc d.busInteractions #[] #[] #[]
            (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
            (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).2.2.1
          0 #[] #[] (Array.replicate (dbBuildCtxFast bs facts d).nv #[])
          (0, false, true, true)).1 := rfl
  have hcsV : (dbBuildCtxFast bs facts d).csVars
      = (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).1 := rfl
  have hbiV : (dbBuildCtxFast bs facts d).biVars
      = (dbBiWalk facts bc d.busInteractions #[] #[] #[]
          (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.1
          (dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩).2.2).1 := rfl
  -- a variable-free interaction's obligation, read at the empty register file
  have hbiOk : ∀ i, ∀ hi : i < d.busInteractions.length, ∀ regs : Array ℕ,
      DbRegsAgreeA denv regs (dbBiVars d.busInteractions[i]) →
      dbItemOk facts regs
        (dbCompileBi facts bc d.busInteractions[i] (pre.getD i dbBiPreEmpty)) = true := by
    intro i hi regs hagree
    exact dbCompileBi_ok facts bc _ _ (hpreOf i hi) denv regs
      (dbBiVars_agree denv regs _ hagree) (hbis _ (List.getElem_mem hi))
  refine ⟨htab, ?_, fun pos regs hagree => ?_, fun item hitem regs => ?_,
    fun pos regs hagree => ?_, fun pos => ?_, fun item hitem => ?_, fun pos => ?_⟩
  · -- `constOk`
    show (dbBiWalk2 facts bc (dbBuildCtxFast bs facts d).T d.busInteractions pre _ 0 #[] #[]
      (Array.replicate (dbBuildCtxFast bs facts d).nv #[]) (0, false, true, true)).2.2.2.2.2.2 = true
    refine hbicon (by trivial) (fun i hi hvar => ?_)
    refine hbiOk i hi #[] (fun v hv => ?_)
    rw [hpre i hi] at hvar
    have hem : dbBiVars d.busInteractions[i] = #[] := by
      have hz : (dbBiVars d.busInteractions[i]).size = 0 := by
        rcases Nat.eq_zero_or_pos (dbBiVars d.busInteractions[i]).size with h | h
        · exact h
        · rw [show (dbPreOne facts bc d.busInteractions[i]
              (dbBiVars d.busInteractions[i])).vars = dbBiVars d.busInteractions[i] from rfl,
            Array.getElem?_eq_getElem h] at hvar
          simp at hvar
      exact Array.eq_empty_of_size_eq_zero hz
    rw [hem] at hv; simp at hv
  · -- `csItem`
    rw [hcsItems]
    rcases Nat.lt_or_ge pos d.algebraicConstraints.length with h | h
    · rcases hcsat pos h with hit | hit
      · rw [hit]; rfl
      · rw [hit]
        rw [hcsV, hat1 pos h] at hagree
        show (dbEval p regs d.algebraicConstraints[pos] == 0) = true
        rw [dbEval_zero denv regs _ (dbVarsOf_agree denv regs _ hagree)]
        exact decide_eq_true (hcs _ (List.getElem_mem h))
    · rw [dbGetD_ge _ _ _ (by omega)]; rfl
  · -- variable-free constraint items
    rw [hcsVarless] at hitem
    rcases hcsvl item hitem with hv | hv | ⟨i, hi, heq, hemp⟩
    · simp at hv
    · rw [hv]; rfl
    · rw [heq]
      rw [hat1 i hi] at hemp
      show (dbEval p regs d.algebraicConstraints[i] == 0) = true
      rw [dbEval_zero denv regs _ (fun v hv => by
        have hm := (dbVarsOf_mem d.algebraicConstraints[i] #[]).2 v hv
        rw [hemp] at hm; simp at hm)]
      exact decide_eq_true (hcs _ (List.getElem_mem hi))
  · -- `biItem`
    rw [hbiItems]
    rcases Nat.lt_or_ge pos d.busInteractions.length with h | h
    · rcases hbiat pos h with hit | hit
      · rw [hit]; rfl
      · rw [hit]
        rw [hbiV, (hat2 pos h).1] at hagree
        exact hbiOk pos h regs hagree
    · rw [dbGetD_ge _ _ _ (by omega)]; rfl
  · -- `csItemVars`
    rw [hcsItems, hcsV]
    rcases Nat.lt_or_ge pos d.algebraicConstraints.length with h | h
    · rcases hcsat pos h with hit | hit
      · rw [hit]; trivial
      · rw [hit, hat1 pos h]
        exact fun v hv => (dbVarsOf_mem d.algebraicConstraints[pos] _).2 v hv
    · rw [dbGetD_ge _ _ _ (by omega)]; trivial
  · -- variable-free constraint items mention no variable
    rw [hcsVarless] at hitem
    rcases hcsvl item hitem with hv | hv | ⟨i, hi, heq, hemp⟩
    · simp at hv
    · rw [hv]; trivial
    · rw [heq]
      rw [hat1 i hi] at hemp
      intro v hv
      have hm := (dbVarsOf_mem d.algebraicConstraints[i] #[]).2 v hv
      rw [hemp] at hm
      exact hm
  · -- `biItemVars`
    rw [hbiItems, hbiV]
    rcases Nat.lt_or_ge pos d.busInteractions.length with h | h
    · rcases hbiat pos h with hit | hit
      · rw [hit]; trivial
      · rw [hit, (hat2 pos h).1]
        exact dbCompileBi_vars facts bc _ _ (hpreOf pos h)
    · rw [dbGetD_ge _ _ _ (by omega)]; trivial

theorem dbBuildCtxFast_vl (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    (dbBuildCtxFast bs facts d).csVarlessVars.size
      = (dbBuildCtxFast bs facts d).csVarlessItems.size := by
  simp [dbBuildCtxFast]

theorem dbDomainBatchσ_entailed [Fact p.Prime] [NeZero p]
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    ∀ (i : VarId) (t : DenseExpr p), dbSubstFn (dbDomainBatchσ bs facts d).1 i = some t →
      (∀ z ∈ t.vars, z ∈ d.occ) ∧ ∀ denv, d.satisfies bs denv → denv i = t.eval denv := by
  intro i t ht
  set ctx := dbBuildCtxFast bs facts d with hctx
  have hvl : ctx.csVarlessVars.size = ctx.csVarlessItems.size := dbBuildCtxFast_vl bs facts d
  have hsound := dbRunPlansFast_sound facts ctx.nv d _ (fun plan hplan => by
    rw [List.mem_reverse] at hplan
    exact dbTargetsBis_sound bs facts d ctx (dbBuildCtxFast_shape bs facts d)
      (fun denv hsat => dbBuildCtxFast_good bs facts d denv hsat) hvl 0 _
      (dbTargetsCs_sound bs facts d ctx (dbBuildCtxFast_shape bs facts d)
        (fun denv hsat => dbBuildCtxFast_good bs facts d denv hsat) hvl 0
        ⟨⟨∅⟩, Array.replicate ctx.nv 0, 0, []⟩ (fun plan hplan => by simp at hplan))
      plan hplan)
  rw [dbSubstFn] at ht
  rcases hq : (dbDomainBatchσ bs facts d).1.getD i.index none with _ | c
  · rw [hq] at ht; simp at ht
  · rw [hq, Option.map_some] at ht
    rw [← Option.some.inj ht]
    refine ⟨fun z hz => by simp [DenseExpr.vars] at hz, fun denv hsat => ?_⟩
    rw [DenseExpr.eval]
    rw [dbDomainBatchσ] at hq
    split at hq
    · rw [show (#[] : Array (Option (ZMod p))).getD i.index none = none from rfl] at hq
      simp at hq
    · exact dbSolvedOf_sound d ctx.nv _ hsound i.index c hq denv hsat

theorem dbDomainBatchTransform_covered (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (hcov : d.CoveredBy reg) :
    (dbDomainBatchTransform pw bs facts d).CoveredBy reg := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show dbDomainBatchTransform pw bs facts d
        = (if (dbDomainBatchσ bs facts d).2 then d.substF (dbSubstFn (dbDomainBatchσ bs facts d).1)
            else d) from by simp only [dbDomainBatchTransform, if_pos hpB]]
    split
    · refine DenseConstraintSystem.substF_covered hcov (fun i _ t ht z hz => ?_)
      exact DenseConstraintSystem.occ_valid hcov z
        ((dbDomainBatchσ_entailed bs facts d i t ht).1 z hz)
    · exact hcov
  · rw [show dbDomainBatchTransform pw bs facts d = d
        from by simp only [dbDomainBatchTransform, if_neg hpB]]
    exact hcov

theorem dbDomainBatchTransform_correct (pw : PrimeWitness p) (reg : VarRegistry)
    (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (dbDomainBatchTransform pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    haveI : NeZero p := ⟨(pw.correct hpB).ne_zero⟩
    rw [show dbDomainBatchTransform pw bs facts d
        = (if (dbDomainBatchσ bs facts d).2 then d.substF (dbSubstFn (dbDomainBatchσ bs facts d).1)
            else d) from by simp only [dbDomainBatchTransform, if_pos hpB]]
    split
    · refine DenseConstraintSystem.substF_denseCorrect d (dbSubstFn (dbDomainBatchσ bs facts d).1)
        bs reg.isInput (fun denv hsat j t hjt => ?_) (fun j t hjt z hz => ?_)
      · exact (dbDomainBatchσ_entailed bs facts d j t hjt).2 denv hsat
      · exact (dbDomainBatchσ_entailed bs facts d j t hjt).1 z hz
    · exact DensePassCorrect_refl reg.isInput d bs
  · rw [show dbDomainBatchTransform pw bs facts d = d
        from by simp only [dbDomainBatchTransform, if_neg hpB]]
    exact DensePassCorrect_refl reg.isInput d bs

/-- The rebuilt domain-batch pass (see `dbDomainBatchσ`). -/
def dbDomainBatchPass (pw : PrimeWitness p) : DenseVerifiedPassW p := fun reg d hcov bs facts =>
  { reg' := reg
    out := dbDomainBatchTransform pw bs facts d
    derivs := []
    ext := VarRegistry.Extends.refl reg
    covered := dbDomainBatchTransform_covered pw reg bs facts d hcov
    dcovered := by intro x hx; simp at hx
    correct := DensePassCorrect.lift hcov
      (dbDomainBatchTransform_covered pw reg bs facts d hcov) (by intro x hx; simp at hx)
      (dbDomainBatchTransform_correct pw reg bs facts d) }

end ApcOptimizer.Dense
