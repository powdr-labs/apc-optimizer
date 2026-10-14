import ApcOptimizer.Implementation.OptimizerPasses.DomainTable
import ApcOptimizer.Implementation.OptimizerPasses.Bridge
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! # Shared correctness surface for the domain passes

Simultaneous substitution (`substF_denseCorrect`, the correctness of applying a solution map),
entailment of a solution map (`EntailedMap`), affine-root soundness, the constant/fact soundness
lemmas, domain-table soundness (`DenseTableSoundAt`) and the byte-operand domain bound. The
`domainBatch` and `domainFold` passes and every pass that emits a solution map build on these. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Simultaneous substitution semantics -/

/-- The dense environment with every mapped `VarId` rebound to its solution's value. -/
def denseEnvF (df : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p) : VarId → ZMod p :=
  fun j => match df j with | some t => t.eval denv | none => denv j

@[simp] theorem substitutionHints_eval (df : VarId → Option (DenseExpr p))
    (env : VarId → ZMod p) :
    (fun i => (substitutionHints df i).eval env) = denseEnvF df env := by
  funext i
  cases h : df i <;> simp [substitutionHints, denseEnvF, h, WitnessExpr.eval]

theorem DenseExpr.eval_substF (e : DenseExpr p) (df : VarId → Option (DenseExpr p))
    (denv : VarId → ZMod p) : (e.substF df).eval denv = e.eval (denseEnvF df denv) := by
  induction e with
  | const n => rfl
  | var j =>
      show (match df j with | some t => t | none => DenseExpr.var j).eval denv = denseEnvF df denv j
      unfold denseEnvF
      cases df j <;> rfl
  | add a b iha ihb => simp only [DenseExpr.substF, DenseExpr.eval, iha, ihb]
  | mul a b iha ihb => simp only [DenseExpr.substF, DenseExpr.eval, iha, ihb]

/-- If every mapped pair is respected by `denv`, rebinding changes nothing. -/
theorem denseEnvF_eq_self (df : VarId → Option (DenseExpr p)) (denv : VarId → ZMod p)
    (H : ∀ j t, df j = some t → denv j = t.eval denv) : denseEnvF df denv = denv := by
  funext j
  unfold denseEnvF
  cases hj : df j with
  | none => rfl
  | some t => exact (H j t hj).symm

theorem denseBIEval_substF (bi : BusInteraction (DenseExpr p)) (df : VarId → Option (DenseExpr p))
    (denv : VarId → ZMod p) :
    denseBIEval (denseBIsubstF bi df) denv = denseBIEval bi (denseEnvF df denv) := by
  simp only [denseBIsubstF, denseBIEval, DenseExpr.eval_substF, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, DenseExpr.eval_substF]

theorem DenseConstraintSystem.satisfies_substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (denv : VarId → ZMod p) :
    (d.substF df).satisfies bs denv ↔ d.satisfies bs (denseEnvF df denv) := by
  simp only [DenseConstraintSystem.satisfies, DenseConstraintSystem.substF]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c0 hc0 => ?_, fun bi0 hbi0 => ?_⟩
    · have := hc _ (List.mem_map.2 ⟨c0, hc0, rfl⟩)
      rwa [DenseExpr.eval_substF] at this
    · have := hb _ (List.mem_map.2 ⟨bi0, hbi0, rfl⟩)
      rwa [denseBIEval_substF] at this
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hc' => ?_, fun bi hbi' => ?_⟩
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc'
      rw [DenseExpr.eval_substF]; exact hc c0 hc0
    · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi'
      rw [denseBIEval_substF]; exact hb bi0 hbi0

theorem DenseConstraintSystem.admissible_substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (denv : VarId → ZMod p) :
    (d.substF df).admissible bs denv ↔ d.admissible bs (denseEnvF df denv) := by
  unfold DenseConstraintSystem.admissible
  have hmap : (d.substF df).busInteractions.map (fun bi => denseBIEval bi denv)
      = d.busInteractions.map (fun bi => denseBIEval bi (denseEnvF df denv)) := by
    simp only [DenseConstraintSystem.substF, List.map_map]
    exact List.map_congr_left (fun bi _ => denseBIEval_substF bi df denv)
  rw [hmap]

theorem DenseConstraintSystem.sideEffects_substF (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (denv : VarId → ZMod p) :
    (d.substF df).sideEffects bs denv = d.sideEffects bs (denseEnvF df denv) := by
  unfold DenseConstraintSystem.sideEffects DenseConstraintSystem.substF
  refine funext (fun message => congrArg (multiplicitySum message) ?_)
  rw [show (fun bi : BusInteraction (DenseExpr p) => bs.isStateful bi.busId) =
        (fun bi => bs.isStateful bi.busId) from rfl]
  rw [filter_map_busId_comm d.busInteractions (fun bi => denseBIsubstF bi df) bs (fun _ => rfl),
    List.map_map]
  refine List.map_congr_left (fun bi _ => ?_)
  simp only [Function.comp_apply, denseBIEval_substF]

/-- Substitution by an entailed map of constants introduces no new occurrence. -/
theorem DenseConstraintSystem.substF_occ_subset (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p))
    (hfv : ∀ (j : VarId) (t : DenseExpr p), df j = some t → ∀ z ∈ t.vars, z ∈ d.occ) :
    ∀ i ∈ (d.substF df).occ, i ∈ d.occ := by
  intro i hi
  simp only [DenseConstraintSystem.occ, DenseConstraintSystem.substF, List.mem_append,
    List.mem_flatMap] at hi
  rcases hi with ⟨c, hc, hic⟩ | ⟨bi, hbi, hib⟩
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    rcases DenseExpr.substF_vars df c0 i hic with h | ⟨j, hj, t, hft, hit⟩
    · exact DenseConstraintSystem.mem_occ_of_constraint hc0 h
    · exact hfv j t hft i hit
  · obtain ⟨bi0, hbi0, rfl⟩ := List.mem_map.1 hbi
    simp only [denseBIsubstF, denseBIVars, List.mem_append, List.mem_flatMap] at hib
    rcases hib with hm | ⟨e, he, hie⟩
    · rcases DenseExpr.substF_vars df bi0.multiplicity i hm with h | ⟨j, hj, t, hft, hit⟩
      · exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
          simp only [denseBIVars, List.mem_append]; exact Or.inl h)
      · exact hfv j t hft i hit
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      rcases DenseExpr.substF_vars df e0 i hie with h | ⟨j, hj, t, hft, hit⟩
      · exact DenseConstraintSystem.mem_occ_of_bi hbi0 (by
          simp only [denseBIVars, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨e0, he0, h⟩)
      · exact hfv j t hft i hit

/-- **Simultaneous-substitution correctness.** If every satisfying assignment of `d` forces
    `denv j = t.eval denv` for each mapped pair `df j = some t`, and every solution mentions only
    `d`'s occurring variables, then substituting the whole map at once satisfies `DensePassCorrect`
    (no derivations). -/
theorem DenseConstraintSystem.substF_denseCorrect (d : DenseConstraintSystem p)
    (df : VarId → Option (DenseExpr p)) (bs : BusSemantics p) (isInput : VarId → Bool)
    (H : ∀ denv, d.satisfies bs denv → ∀ j t, df j = some t → denv j = t.eval denv)
    (hfv : ∀ (j : VarId) (t : DenseExpr p), df j = some t → ∀ z ∈ t.vars, z ∈ d.occ) :
    DensePassCorrect isInput d (d.substF df) [] bs (substitutionHints df) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- soundness: `(d.substF df).implies d`
    intro denv hsat
    simp only [substitutionHints_eval]
    exact ⟨(d.satisfies_substF df bs denv).1 hsat, d.sideEffects_substF df bs denv⟩
  · -- invariant preservation
    intro hinv denv hsat bi hbi
    have hsatd : d.satisfies bs (denseEnvF df denv) := (d.satisfies_substF df bs denv).1 hsat
    simp only [DenseConstraintSystem.substF, List.mem_map] at hbi
    obtain ⟨bi0, hbi0, rfl⟩ := hbi
    show (denseBIEval (denseBIsubstF bi0 df) denv).multiplicity ≠ 0 →
      bs.maintainsInvariants (denseBIEval (denseBIsubstF bi0 df) denv)
    rw [denseBIEval_substF]
    exact hinv (denseEnvF df denv) hsatd bi0 hbi0
  · -- no new occurrence at all (hence none introduced at an input column)
    intro i hi _
    exact d.substF_occ_subset df hfv i hi
  · -- completeness with derivations
    intro denv hadm hsat
    have henv : denseEnvF df denv = denv := denseEnvF_eq_self df denv (H denv hsat)
    refine ⟨denv, ?_, ?_, ?_, fun _ _ => rfl, ?_⟩
    · rw [d.satisfies_substF df bs denv, henv]; exact hsat
    · rw [d.admissible_substF df bs denv, henv]; exact hadm
    · rw [d.sideEffects_substF df bs denv, henv]
    · -- reconstruction: no derivations, and out.occ ⊆ d.occ, denv' = denv
      intro inputVarIds _
      unfold DenseOutReconstructs
      intro i hi _
      show i ∈ d.occ ∧ denv i = denv i
      exact ⟨d.substF_occ_subset df hfv i hi, rfl⟩

/-! ## Root soundness

The affine-form eval-preservation lemmas used here live in `Dense/Affine.lean` and
`Dense/Normalize.lean`. -/

theorem denseRootsOfTerms_sound [Fact p.Prime] (i : VarId) (c : ZMod p)
    (ts : List (VarId × ZMod p)) (roots : List (ZMod p))
    (h : denseRootsOfTerms i c ts = some roots) (denv : VarId → ZMod p)
    (hsum : c + (ts.map (fun t => t.2 * denv t.1)).sum = 0) : denv i ∈ roots := by
  rcases ts with _ | ⟨⟨j, a⟩, _ | ⟨t2, rest⟩⟩
  · simp only [denseRootsOfTerms] at h
    split_ifs at h with hc
    exact absurd (by simpa using hsum) hc
  · simp only [denseRootsOfTerms] at h
    split_ifs at h with hcond
    obtain ⟨rfl, ha, hr⟩ := hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
    have hxy : a * denv j + c = 0 := by linear_combination hsum
    have hcancel : a * denv j = a * (-(a⁻¹ * c)) := by
      rw [eq_neg_of_add_eq_zero_left hxy, ← eq_neg_of_add_eq_zero_left hr]
    simpa using mul_left_cancel₀ ha hcancel
  · exact absurd h (by simp [denseRootsOfTerms])

theorem denseAffineRootsIn_sound [Fact p.Prime] (i : VarId) (e : DenseExpr p)
    (roots : List (ZMod p)) (h : denseAffineRootsIn i e = some roots)
    (denv : VarId → ZMod p) (he : e.eval denv = 0) : denv i ∈ roots := by
  simp only [denseAffineRootsIn, Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hroot⟩ := h
  have heval : l.norm.const + (l.norm.terms.map (fun t => t.2 * denv t.1)).sum = 0 := by
    have h1 : l.norm.eval denv = 0 := by
      rw [DenseLinExpr.norm_eval, ← denseLinearize_eval e l hlin]; exact he
    simpa [DenseLinExpr.eval] using h1
  exact denseRootsOfTerms_sound i l.norm.const l.norm.terms roots hroot denv heval

theorem denseRootsIn_sound [Fact p.Prime] (i : VarId) (e : DenseExpr p) (roots : List (ZMod p))
    (h : denseRootsIn i e = some roots) (denv : VarId → ZMod p) (he : e.eval denv = 0) :
    denv i ∈ roots := by
  induction e generalizing roots with
  | const n => exact denseAffineRootsIn_sound i _ roots h denv he
  | var y => exact denseAffineRootsIn_sound i _ roots h denv he
  | add a b _ _ => exact denseAffineRootsIn_sound i _ roots h denv he
  | mul a b iha ihb =>
    rw [denseRootsIn] at h
    split at h
    · rename_i r haff
      simp only [Option.some.injEq] at h
      subst h
      exact denseAffineRootsIn_sound i _ _ haff denv he
    · rename_i haff
      split at h
      · rename_i ra rb hra hrb
        simp only [Option.some.injEq] at h
        subst h
        have he' : a.eval denv * b.eval denv = 0 := he
        rcases mul_eq_zero.mp he' with hz | hz
        · exact List.mem_append.2 (Or.inl (iha ra hra hz))
        · exact List.mem_append.2 (Or.inr (ihb rb hrb hz))
      all_goals exact absurd h (by simp)

/-! ## Constant / fact soundness -/

theorem DenseExpr.constValue?_sound (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  unfold DenseExpr.constValue? at h
  cases hf : e.fold with
  | const n => rw [hf] at h; simp only [Option.some.injEq] at h; subst h; rfl
  | var j => rw [hf] at h; simp at h
  | add a b => rw [hf] at h; simp at h
  | mul a b => rw [hf] at h; simp at h

theorem denseIsVarOf_sound (i : VarId) (e : DenseExpr p) (h : denseIsVarOf i e = true) :
    e = DenseExpr.var i := by
  cases e with
  | var j => simp only [denseIsVarOf, decide_eq_true_eq] at h; rw [h]
  | const n => simp [denseIsVarOf] at h
  | add a b => simp [denseIsVarOf] at h
  | mul a b => simp [denseIsVarOf] at h

theorem denseVarSlot_sound (i : VarId) (payload : List (DenseExpr p)) (slot : Nat)
    (h : denseVarSlot i payload = some slot) : payload[slot]? = some (.var i) := by
  induction payload generalizing slot with
  | nil => exact absurd h (by simp [denseVarSlot])
  | cons e rest ih =>
    rw [denseVarSlot] at h
    split_ifs at h with hv
    · simp only [Option.some.injEq] at h
      subst h
      simpa using denseIsVarOf_sound i e hv
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨s, hs, rfl⟩ := h
      simpa using ih s hs

theorem denseMatches_evalPattern (payload : List (DenseExpr p)) (denv : VarId → ZMod p) :
    Matches (payload.map (fun e => e.eval denv)) (payload.map DenseExpr.constValue?) := by
  refine ⟨by simp, ?_⟩
  intro slot c hc
  rw [List.getElem?_map] at hc
  rw [List.getElem?_map]
  cases he : payload[slot]? with
  | none => rw [he] at hc; simp at hc
  | some e =>
      rw [he] at hc
      simp only [Option.map_some, Option.some.injEq] at hc ⊢
      exact e.constValue?_sound c hc denv

theorem denseInteractionBound_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (i : VarId) (bound : Nat)
    (h : denseInteractionBound bs facts bi i = some bound) (denv : VarId → ZMod p)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.accepts (denseBIEval bi denv)) :
    (denv i).val < bound := by
  unfold denseInteractionBound at h
  split at h
  · exact absurd h (by simp)
  · rename_i mval hm
    split_ifs at h with hmz
    split at h
    · exact absurd h (by simp)
    · rename_i slot hslot
      have hmeval : (denseBIEval bi denv).multiplicity = mval :=
        bi.multiplicity.constValue?_sound mval hm denv
      have hviol : bs.accepts (denseBIEval bi denv) := by
        apply hob; rw [hmeval]; exact hmz
      have hgete : bi.payload[slot]? = some (.var i) := denseVarSlot_sound i bi.payload slot hslot
      have hget : (denseBIEval bi denv).payload[slot]? = some (denv i) := by
        show (bi.payload.map (fun e => e.eval denv))[slot]? = some (denv i)
        rw [List.getElem?_map, hgete]
        rfl
      rw [← hmeval] at h
      exact facts.slotBound_sound (denseBIEval bi denv)
        (bi.payload.map DenseExpr.constValue?) slot bound (denv i) h
        (denseMatches_evalPattern bi.payload denv) hviol hget

/-! ## Domain tables and point evaluation -/

/-- Soundness of a dense domain table at a fixed environment: every stored domain contains the
    environment's value for its variable. -/
def DenseTableSoundAt (denv : VarId → ZMod p) (T : DenseDomainTable p) : Prop :=
  ∀ i dm, T.map[i]? = some dm → denv i ∈ dm.toList

/-- The value-only environment reads a key's value from the positionally-aligned point. -/
theorem denseEnvOfKeysV_map (denv : VarId → ZMod p) :
    ∀ (keys : List VarId) (y : VarId), y ∈ keys → denseEnvOfKeysV keys (keys.map denv) y = denv y := by
  intro keys
  induction keys with
  | nil => intro y hy; simp at hy
  | cons x rest ih =>
    intro y hy
    rw [List.map_cons]
    show denseEnvOfKeysV (x :: rest) (denv x :: rest.map denv) y = denv y
    rw [denseEnvOfKeysV]
    by_cases hyx : (y == x) = true
    · have hyx' : y = x := by simpa using hyx
      rw [if_pos hyx, hyx']
    · rw [if_neg hyx]
      rcases List.mem_cons.1 hy with rfl | hy'
      · simp at hyx
      · exact ih y hy'

/-- Positional lookup on a value-only point matches the keyed environment lookup. -/
theorem denseVarIx_lookupV_env (keys : List VarId) (pt : List (ZMod p)) (y : VarId) (idx : Nat)
    (h : denseVarIx keys y = some idx) :
    denseLookupIxV 0 pt idx = denseEnvOfKeysV keys pt y := by
  induction keys generalizing pt idx with
  | nil => simp [denseVarIx] at h
  | cons x rest ih =>
    rw [denseVarIx] at h
    cases pt with
    | nil => rfl
    | cons v vs =>
      split_ifs at h with hyx
      · simp only [Option.some.injEq] at h; subst h
        show denseLookupIxV 0 (v :: vs) 0 = denseEnvOfKeysV (x :: rest) (v :: vs) y
        rw [denseLookupIxV, denseEnvOfKeysV, if_pos hyx]
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        show denseLookupIxV 0 (v :: vs) (j + 1) = denseEnvOfKeysV (x :: rest) (v :: vs) y
        rw [denseLookupIxV, denseEnvOfKeysV, if_neg hyx]
        exact ih vs j hj

/-- Compiled value-only evaluation agrees with the keyed-environment evaluation of the source. -/
theorem denseCompileE_evalV (ops : DenseZModOps p) (keys : List VarId) (pt : List (ZMod p)) :
    ∀ (e : DenseExpr p) (ic : IExpr p), denseCompileE keys e = some ic →
      denseIExprEvalWithV ops pt ic = e.eval (denseEnvOfKeysV keys pt) := by
  intro e
  induction e with
  | const n => intro ic h; simp only [denseCompileE, Option.some.injEq] at h; subst h; rfl
  | var y =>
      intro ic h
      rw [denseCompileE, Option.map_eq_some_iff] at h
      obtain ⟨idx, hidx, rfl⟩ := h
      show denseIExprEvalWithV ops pt (.ix idx) = denseEnvOfKeysV keys pt y
      rw [denseIExprEvalWithV]
      rw [ops.zero_eq]
      exact denseVarIx_lookupV_env keys pt y idx hidx
  | add a b iha ihb =>
      intro ic h
      cases ha : denseCompileE keys a with
      | none => rw [denseCompileE, ha] at h; simp at h
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [denseCompileE, ha, hb] at h; simp at h
        | some ib =>
          rw [denseCompileE, ha, hb] at h; simp only [Option.some.injEq] at h; subst h
          show denseIExprEvalWithV ops pt (.add ia ib) = (a.add b).eval (denseEnvOfKeysV keys pt)
          rw [denseIExprEvalWithV, DenseExpr.eval, ops.add_eq, iha ia ha, ihb ib hb]
  | mul a b iha ihb =>
      intro ic h
      cases ha : denseCompileE keys a with
      | none => rw [denseCompileE, ha] at h; simp at h
      | some ia =>
        cases hb : denseCompileE keys b with
        | none => rw [denseCompileE, ha, hb] at h; simp at h
        | some ib =>
          rw [denseCompileE, ha, hb] at h; simp only [Option.some.injEq] at h; subst h
          show denseIExprEvalWithV ops pt (.mul ia ib) = (a.mul b).eval (denseEnvOfKeysV keys pt)
          rw [denseIExprEvalWithV, DenseExpr.eval, ops.mul_eq, iha ia ha, ihb ib hb]

private theorem denseByteXorSpec_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (op.eval denv = spec.xorOp →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            (r.eval denv).val = Nat.xor (o1.eval denv).val (o2.eval denv).val)) ∧
    (op.eval denv = spec.pairOp →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            r.eval denv = 0)) := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
  have hdecEv : spec.decode (denseBIEval bi denv).payload =
      some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]
    rfl
  exact hsound (denseBIEval bi denv).payload (op.eval denv) (o1.eval denv) (o2.eval denv)
    (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

private theorem denseByteBoolSound_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (∀ oop, spec.orOp = some oop → op.eval denv = oop →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            (r.eval denv).val = Nat.lor (o1.eval denv).val (o2.eval denv).val)) ∧
    (∀ aop, spec.andOp = some aop → op.eval denv = aop →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧
            (r.eval denv).val = Nat.land (o1.eval denv).val (o2.eval denv).val)) := by
  have hdecEv : spec.decode (denseBIEval bi denv).payload =
      some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]
    rfl
  exact facts.byteBoolSound bi.busId spec hspec (denseBIEval bi denv).payload (op.eval denv)
    (o1.eval denv) (o2.eval denv) (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

/-! ## Byte-operand domain soundness

`denseAddByteDoms` mines each recognized byte interaction's operand bound (`spec.bound`): a
bare-variable operand gets a `.range` domain, an affine operand `a·x + b < bound` the `bound`-element
coset `{(v - b)·a⁻¹ : v < bound}`. -/

/-- The single-variable affine form recovered by `denseAffineOfExpr` evaluates as expected, with a
    nonzero leading coefficient. -/
theorem denseAffineOfExpr_eval (e : DenseExpr p) (x : VarId) (a b : ZMod p)
    (h : denseAffineOfExpr e = some (x, a, b)) (denv : VarId → ZMod p) :
    e.eval denv = a * denv x + b ∧ a ≠ 0 := by
  unfold denseAffineOfExpr at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨l, hlin, hm⟩ := h
  cases ht : l.norm.terms with
  | nil => rw [ht] at hm; simp at hm
  | cons t rest =>
    cases rest with
    | cons _ _ => rw [ht] at hm; simp at hm
    | nil =>
      obtain ⟨x0, a0⟩ := t
      rw [ht] at hm
      simp only at hm
      by_cases ha0 : a0 = 0
      · rw [if_pos ha0] at hm; simp at hm
      · rw [if_neg ha0] at hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        refine ⟨?_, ha0⟩
        rw [denseLinearize_eval e l hlin, ← DenseLinExpr.norm_eval, DenseLinExpr.eval, ht]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [add_comm]

/-- The affine coset domain contains `denv x` when the operand's value is below `bound`. -/
theorem denseByteOperandCosetMem [Fact p.Prime] [NeZero p] (e : DenseExpr p) (bound : Nat)
    (x : VarId) (a b : ZMod p) (haff : denseAffineOfExpr e = some (x, a, b))
    (denv : VarId → ZMod p) (hbnd : (e.eval denv).val < bound) :
    denv x ∈ ((List.range bound).map (Nat.cast : Nat → ZMod p)).map (fun z => (z - b) * a⁻¹) := by
  obtain ⟨heval, ha0⟩ := denseAffineOfExpr_eval e x a b haff denv
  have hmem : e.eval denv ∈ (List.range bound).map (Nat.cast : Nat → ZMod p) :=
    mem_range_cast (e.eval denv) bound hbnd
  set z0 := e.eval denv with hz0
  have hdenv : denv x = (z0 - b) * a⁻¹ := by
    rw [heval, add_sub_cancel_right, mul_right_comm, mul_inv_cancel₀ ha0, one_mul]
  rw [hdenv]
  exact List.mem_map_of_mem hmem

/-- Under a nonzero-constant multiplicity and a recognized byte op, both operands are below the byte
    bound (`BusFacts.byteXorSpec_sound` / `byteBoolSound`). -/
theorem denseByteOperandBound [NeZero p] (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (denv : VarId → ZMod p) (mult : ZMod p)
    (hmult : bi.multiplicity.constValue? = some mult) (hmz : mult ≠ 0) (spec : ByteXorSpec p)
    (hspec : facts.byteXorSpec bi.busId = some spec) (op o1 o2 r : DenseExpr p)
    (hdec : spec.decode bi.payload = some (op, o1, o2, r)) (opv : ZMod p)
    (hop : op.constValue? = some opv) (hb : denseByteOpBounds spec opv = true)
    (hob : (denseBIEval bi denv).multiplicity ≠ 0 →
      bs.accepts (denseBIEval bi denv)) :
    (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound := by
  have hmeval : (denseBIEval bi denv).multiplicity = mult :=
    bi.multiplicity.constValue?_sound mult hmult denv
  have hviol : bs.accepts (denseBIEval bi denv) := hob (by rw [hmeval]; exact hmz)
  have hopeval : op.eval denv = opv := op.constValue?_sound opv hop denv
  obtain ⟨hxor, hpair⟩ := denseByteXorSpec_decode_iff bs facts spec bi hspec op o1 o2 r hdec denv
  obtain ⟨hor, hand⟩ := denseByteBoolSound_decode_iff bs facts spec bi hspec op o1 o2 r hdec denv
  simp only [denseByteOpBounds, Bool.or_eq_true, Option.any_eq_true, decide_eq_true_eq] at hb
  rcases hb with ((hsel | hsel) | ⟨o, ho, hsel⟩) | ⟨aop, ha, hsel⟩
  · have := (hxor (by rw [hopeval, hsel])).1 hviol; exact ⟨this.1, this.2.1⟩
  · have := (hpair (by rw [hopeval, hsel])).1 hviol; exact ⟨this.1, this.2.1⟩
  · have := (hor o ho (by rw [hopeval, hsel])).1 hviol; exact ⟨this.1, this.2.1⟩
  · have := (hand aop ha (by rw [hopeval, hsel])).1 hviol; exact ⟨this.1, this.2.1⟩

/-! ## The entailment invariant on a collected solution map -/

/-- A `(i, t)` solution pair is entailed by `d`: its variables occur in `d`, and every satisfying
    assignment forces `denv i = t.eval denv`. -/
def EntailedPair (d : DenseConstraintSystem p) (bs : BusSemantics p) (i : VarId) (t : DenseExpr p) :
    Prop :=
  (∀ z ∈ t.vars, z ∈ d.occ) ∧ (∀ denv, d.satisfies bs denv → denv i = t.eval denv)

/-- Every entry of a solution map is entailed. -/
def EntailedMap (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (m : Std.HashMap VarId (DenseExpr p)) : Prop :=
  ∀ i t, m[i]? = some t → EntailedPair d bs i t

/-! ## Reflexive (identity) correctness -/

theorem DensePassCorrect_refl (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) : DensePassCorrect isInput d d [] bs := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro denv hsat; exact ⟨hsat, rfl⟩
  · intro hinv; exact hinv
  · intro i hi _; exact hi
  · intro denv hadm hsat
    refine ⟨denv, hsat, hadm, rfl, fun _ _ => rfl, ?_⟩
    intro inputVarIds _
    unfold DenseOutReconstructs
    intro i hi _
    show i ∈ d.occ ∧ denv i = denv i
    exact ⟨hi, rfl⟩

end ApcOptimizer.Dense
