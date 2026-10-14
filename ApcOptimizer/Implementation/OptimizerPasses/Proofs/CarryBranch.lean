import ApcOptimizer.Implementation.OptimizerPasses.CarryBranch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DigitFold

set_option autoImplicit false

/-! # Correctness for the dense carry-branch resolution (`CarryBranch.lean`). Value bounds are
consumed through `denseBuild_sound` (`Proofs/DigitFold.lean`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Two-sided interval certificate

Only `true` is a claim, so the fail-fast bound gate, the candidate rescalings and the batch
inversion carry nothing: the certificate is sound for *every* scalar `k`, since `k · l ≠ 0` gives
`l ≠ 0`. What has to be proved is the scan — that a run reaching the end of the row pins the
rescaled form's value strictly inside `(0, p)`. -/

/-- The scan's rescaled coefficient is the `ZMod` product's `val`. -/
theorem denseCbVal_mul (kv : Nat) (a : ZMod p) :
    (((kv : ℕ) : ZMod p) * a).val = kv * a.val % p := by
  rw [ZMod.val_mul, ZMod.val_natCast]
  conv_rhs => rw [Nat.mul_mod]
  rw [Nat.mul_mod (kv % p) a.val, Nat.mod_mod_of_dvd _ dvd_rfl]

/-- Scaling a term list by `k` distributes over its sum. -/
theorem denseCbSum_mul (k : ZMod p) (denv : VarId → ZMod p) (ts : List (VarId × ZMod p)) :
    (ts.map (fun t => k * t.2 * denv t.1)).sum = k * (ts.map (fun t => t.2 * denv t.1)).sum := by
  induction ts with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **The scan is sound.** A run that reaches the end of the row decomposes the rescaled term sum
    as `P − N` with each side still inside its remaining budget. The two caps are exactly the
    certificate's two inequalities, so a run that never trips them *is* the certificate; the
    aborting branches return `false` and claim nothing. Mirrors the argument the deleted
    `denseSplitSum_val` carried, on `Nat` values via `ZMod.val_mul`. -/
theorem denseCbScan_sound (hp : 0 < p) (B : Std.HashMap VarId Nat) (kv loCap hiCap : Nat)
    (hhi : hiCap ≤ p) (hlo : loCap ≤ p) (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    ∀ (ts : List (VarId × ZMod p)) (row : DenseCbRow) (mp mn : Nat),
      denseCbRow? B ts = some row → mp < hiCap → mn < loCap →
      denseCbScan p kv loCap hiCap row mp mn = true →
      ∃ P N : ZMod p,
        (ts.map (fun t => ((kv : ℕ) : ZMod p) * t.2 * denv t.1)).sum = P - N ∧
        P.val + mp < hiCap ∧ N.val + mn < loCap := by
  haveI : NeZero p := ⟨hp.ne'⟩
  intro ts
  induction ts with
  | nil =>
      intro row mp mn hrow hmp hmn _
      rw [denseCbRow?] at hrow
      simp only [Option.some.injEq] at hrow
      subst hrow
      have hz : (0 : ZMod p).val = 0 := ZMod.val_zero
      exact ⟨0, 0, by simp, by omega, by omega⟩
  | cons t rest ih =>
      obtain ⟨v, a⟩ := t
      intro row mp mn hrow hmp hmn hscan
      -- the row entry for this term
      rw [denseCbRow?] at hrow
      cases hbv : B[v]? with
      | none => simp [hbv] at hrow
      | some bound =>
      simp only [hbv] at hrow
      by_cases hb0 : bound = 0
      · rw [if_pos hb0] at hrow; exact absurd hrow (by simp)
      rw [if_neg hb0] at hrow
      cases hr : denseCbRow? B rest with
      | none => simp [hr] at hrow
      | some r =>
      simp only [hr] at hrow
      simp only [Option.some.injEq] at hrow
      subst hrow
      have hv : (denv v).val < bound := hB v bound hbv
      have hvw : (denv v).val ≤ bound - 1 := by omega
      -- the rescaled coefficient
      set k : ZMod p := ((kv : ℕ) : ZMod p) with hk
      have hka : (k * a).val = kv * a.val % p := denseCbVal_mul kv a
      rw [denseCbScan] at hscan
      simp only at hscan
      by_cases hle : kv * a.val % p ≤ p - kv * a.val % p
      · rw [if_pos hle] at hscan
        by_cases hmp' : mp + kv * a.val % p * (bound - 1) < hiCap
        case neg => rw [if_neg hmp'] at hscan; exact absurd hscan (by simp)
        rw [if_pos hmp'] at hscan
        -- positive side: the term's magnitude goes into `mp`
        obtain ⟨P', N', hsum', hP', hN'⟩ := ih r _ mn hr hmp' hmn hscan
        have hprod : (k * a).val * (denv v).val < p := by
          have : (k * a).val * (denv v).val ≤ (kv * a.val % p) * (bound - 1) := by
            rw [hka]; exact Nat.mul_le_mul_left _ hvw
          omega
        have hhead : ((k * a) * denv v).val = (k * a).val * (denv v).val :=
          ZMod.val_mul_of_lt hprod
        have hheadle : ((k * a) * denv v).val ≤ (kv * a.val % p) * (bound - 1) := by
          rw [hhead, hka]; exact Nat.mul_le_mul_left _ hvw
        have hadd : ((k * a) * denv v).val + P'.val < p := by omega
        refine ⟨(k * a) * denv v + P', N', ?_, ?_, hN'⟩
        · simp only [List.map_cons, List.sum_cons, hsum']; ring
        · rw [ZMod.val_add_of_lt hadd]; omega
      · rw [if_neg hle] at hscan
        by_cases hmn' : mn + (p - kv * a.val % p) * (bound - 1) < loCap
        case neg => rw [if_neg hmn'] at hscan; exact absurd hscan (by simp)
        rw [if_pos hmn'] at hscan
        -- negative side: the term's magnitude goes into `mn`
        obtain ⟨P', N', hsum', hP', hN'⟩ := ih r mp _ hr hmp hmn' hscan
        have hvpos : 0 < (k * a).val := by rw [hka]; omega
        have hne : k * a ≠ 0 := fun hz => by rw [hz] at hvpos; simp at hvpos
        haveI : NeZero (k * a) := ⟨hne⟩
        have hneg : (-(k * a)).val = p - (k * a).val := ZMod.val_neg_of_ne_zero (k * a)
        have hnegv : (-(k * a)).val = p - kv * a.val % p := by rw [hneg, hka]
        have hprod : (-(k * a)).val * (denv v).val < p := by
          have : (-(k * a)).val * (denv v).val ≤ (p - kv * a.val % p) * (bound - 1) := by
            rw [hnegv]; exact Nat.mul_le_mul_left _ hvw
          omega
        have hhead : ((-(k * a)) * denv v).val = (-(k * a)).val * (denv v).val :=
          ZMod.val_mul_of_lt hprod
        have hheadle : ((-(k * a)) * denv v).val ≤ (p - kv * a.val % p) * (bound - 1) := by
          rw [hhead, hnegv]; exact Nat.mul_le_mul_left _ hvw
        have hadd : ((-(k * a)) * denv v).val + N'.val < p := by omega
        refine ⟨P', (-(k * a)) * denv v + N', ?_, hP', ?_⟩
        · simp only [List.map_cons, List.sum_cons, hsum']; ring
        · rw [ZMod.val_add_of_lt hadd]; omega

/-- One rescaling's certificate is sound: the value sits strictly inside `(0, p)`. -/
theorem denseCbCert_sound (hp : 0 < p) (B : Std.HashMap VarId Nat) (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound)
    (l : DenseLinExpr p) (kv : Nat) (row : DenseCbRow)
    (hrow : denseCbRow? B l.terms = some row)
    (h : denseCbCert p l.const.val kv row = true) :
    l.eval denv ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne'⟩
  set k : ZMod p := ((kv : ℕ) : ZMod p) with hk
  rw [denseCbCert] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc0, hcp⟩, hscan⟩ := h
  have hcval : (k * l.const).val = kv * l.const.val % p := denseCbVal_mul kv l.const
  obtain ⟨P, N, hsum, hP, hN⟩ :=
    denseCbScan_sound hp B kv (kv * l.const.val % p) (p - kv * l.const.val % p)
      (Nat.sub_le _ _) (le_of_lt hcp) denv hB l.terms row 0 0 hrow (by omega) hc0 hscan
  intro h0
  -- scaling the vanishing form by `k` keeps it zero
  have hzero : k * l.const + (P - N) = 0 := by
    rw [← hsum, denseCbSum_mul]
    rw [DenseLinExpr.eval] at h0
    rw [← mul_add, h0, mul_zero]
  have hPN : N = k * l.const + P := by linear_combination -hzero
  have hlt : (k * l.const).val + P.val < p := by omega
  rw [hPN, ZMod.val_add_of_lt hlt, hcval] at hN
  omega

/-- Some rescaling in the batch certifies. The scalars themselves carry no obligation. -/
theorem denseCbTryRow_sound (P cv : Nat) (row : DenseCbRow) :
    ∀ (l : DenseCbRow) (pre : Nat), (denseCbTryRow P cv row l pre).2 = true →
      ∃ kv, denseCbCert P cv kv row = true := by
  intro l
  induction l with
  | nil => intro pre h; exact absurd h (by simp [denseCbTryRow])
  | cons t rest ih =>
      obtain ⟨av, w⟩ := t
      intro pre h
      rw [denseCbTryRow] at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact ih _ h
      · exact ⟨_, h⟩

theorem denseCbSearch_sound (P cv : Nat) (row : DenseCbRow) (h : denseCbSearch P cv row = true) :
    ∃ kv, denseCbCert P cv kv row = true := by
  rw [denseCbSearch] at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h | h
  · exact ⟨_, h⟩
  · exact denseCbTryRow_sound P cv row row cv h
  · exact ⟨_, h⟩

/-- Checked never-zero certificate for an expression (over the candidate rescalings). -/
theorem denseNeverZeroB_sound (hp : 0 < p) (ops : DenseZModOps p) (B : Std.HashMap VarId Nat)
    (e : DenseExpr p)
    (h : denseNeverZeroB ops B e = true) (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    e.eval denv ≠ 0 := by
  rw [denseNeverZeroB, denseLinearizeWith_eq, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases hl : denseLinearize e with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some l =>
  rw [hl] at h
  simp only [DenseLinExpr.normWith_eq] at h
  split_ifs at h with hcv
  cases hrow : denseCbRow? B l.norm.terms with
  | none => rw [hrow] at h; exact absurd h (by simp)
  | some row =>
  rw [hrow] at h
  obtain ⟨kv, hcert⟩ := denseCbSearch_sound p l.norm.const.val row h
  have hne : l.norm.eval denv ≠ 0 :=
    denseCbCert_sound hp B denv hB l.norm kv row hrow hcert
  rw [DenseLinExpr.norm_eval] at hne
  rw [denseLinearize_eval e l hl denv]
  exact hne

/-- The resolution is an *equivalence* on satisfying assignments: with the bounds valid and `p`
    prime, `f·g = 0 ↔ f = 0` whenever `g` is certified never-zero. -/
theorem denseResolveExpr_eval_iff [Fact p.Prime] (ops : DenseZModOps p)
    (B : Std.HashMap VarId Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p)
    (hB : ∀ v bound, B[v]? = some bound → (denv v).val < bound) :
    (denseResolveExpr ops B e).eval denv = 0 ↔ e.eval denv = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction e with
  | mul f g ihf ihg =>
      simp only [denseResolveExpr]
      split_ifs with h1 h2
      · have hg : g.eval denv ≠ 0 := denseNeverZeroB_sound hp ops B g h1 denv hB
        refine ihf.trans ?_
        show f.eval denv = 0 ↔ f.eval denv * g.eval denv = 0
        exact ⟨fun h => by rw [h, zero_mul], fun h => (mul_eq_zero.mp h).resolve_right hg⟩
      · have hf : f.eval denv ≠ 0 := denseNeverZeroB_sound hp ops B f h2 denv hB
        refine ihg.trans ?_
        show g.eval denv = 0 ↔ f.eval denv * g.eval denv = 0
        exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hf⟩
      · exact Iff.rfl
  | const n => exact Iff.rfl
  | var x => exact Iff.rfl
  | add a b iha ihb => exact Iff.rfl

/-! ## The pass correctness -/

/-- Carry-branch correctness: the `denseResolveExpr` rewrite preserves the satisfying set exactly;
    value bounds hold for every satisfying assignment via `denseBuild_sound`. -/
theorem denseCarryBranchF_correct (pw : PrimeWitness p) (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DensePassCorrect reg.isInput d (denseCarryBranchF pw bs facts d) [] bs := by
  by_cases hpB : pw.isPrime = true
  · haveI : Fact p.Prime := ⟨pw.correct hpB⟩
    have hout : denseCarryBranchF pw bs facts d = { d with
          algebraicConstraints :=
            d.algebraicConstraints.map
              (denseResolveExpr denseZModOps (denseBuild bs facts d.busInteractions)) } := by
      unfold denseCarryBranchF; rw [if_pos hpB]
    rw [hout]
    set B := denseBuild bs facts d.busInteractions with hBdef
    -- for any assignment whose bus interactions are non-violating, the built bounds are valid
    have hBof : ∀ denv, (∀ bi ∈ d.busInteractions,
        (denseBIEval bi denv).multiplicity ≠ 0 →
          bs.accepts (denseBIEval bi denv)) →
        ∀ v bound, B[v]? = some bound → (denv v).val < bound := by
      intro denv hbus v bound hlk
      rw [hBdef] at hlk
      exact denseBuild_sound bs facts d.busInteractions v bound hlk denv hbus
    -- satisfaction is preserved under the constraint rewrite
    have hsat_iff : ∀ denv, (∀ v bound, B[v]? = some bound → (denv v).val < bound) →
        (d.satisfies bs denv ↔
          ({ d with algebraicConstraints :=
              d.algebraicConstraints.map (denseResolveExpr denseZModOps B) } :
            DenseConstraintSystem p).satisfies bs denv) := by
      intro denv hB
      constructor
      · rintro ⟨hc, hb⟩
        refine ⟨fun c' hc' => ?_, hb⟩
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
        exact (denseResolveExpr_eval_iff denseZModOps B c denv hB).mpr (hc c hcmem)
      · rintro ⟨hc, hb⟩
        refine ⟨fun c hcmem => ?_, hb⟩
        exact (denseResolveExpr_eval_iff denseZModOps B c denv hB).mp (hc _ (List.mem_map_of_mem hcmem))
    refine DensePassCorrect.ofEnvEq ?_ ?_ ?_ ?_
    · -- soundness: the same assignment satisfies the input
      intro denv hsatout
      have hB := hBof denv hsatout.2
      exact ⟨(hsat_iff denv hB).mpr hsatout, rfl⟩
    · -- invariant preservation (bus interactions are untouched)
      intro hgi denv hsatout
      have hB := hBof denv hsatout.2
      exact hgi denv ((hsat_iff denv hB).mpr hsatout)
    · -- no new variables
      intro i hi
      have hocc :
          ({ d with algebraicConstraints := d.algebraicConstraints.map (denseResolveExpr denseZModOps B) }
              : DenseConstraintSystem p).occ
            = (d.algebraicConstraints.map (denseResolveExpr denseZModOps B)).flatMap DenseExpr.vars
              ++ d.busInteractions.flatMap denseBIVars := rfl
      rw [hocc, List.mem_append] at hi
      rcases hi with hi | hi
      · obtain ⟨c', hc', hic'⟩ := List.mem_flatMap.1 hi
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.1 hc'
        exact DenseConstraintSystem.mem_occ_of_constraint hcmem (denseResolveExpr_vars denseZModOps B c i hic')
      · obtain ⟨bi, hbi, hib⟩ := List.mem_flatMap.1 hi
        exact DenseConstraintSystem.mem_occ_of_bi hbi hib
    · -- completeness: same assignment, same side effects, `admissible` untouched
      intro denv hadm hsat
      have hB := hBof denv hsat.2
      exact ⟨(hsat_iff denv hB).mp hsat, hadm, rfl⟩
  · rw [show denseCarryBranchF pw bs facts d = d from by unfold denseCarryBranchF; rw [if_neg hpB]]
    exact DensePassCorrect.refl reg.isInput d bs

/-- The dense carry-branch-resolution pass; correctness via `denseCarryBranchF_correct`. -/
def denseCarryBranchPass (pw : PrimeWitness p) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of
    (denseCarryBranchF pw)
    (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseCarryBranchF_covered pw reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d _ => denseCarryBranchF_correct pw reg bs facts d)

end ApcOptimizer.Dense
