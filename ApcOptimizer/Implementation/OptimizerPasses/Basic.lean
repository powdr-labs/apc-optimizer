import ApcOptimizer.Spec
import ApcOptimizer.Implementation.Variable

set_option autoImplicit false

variable {p : ℕ}

/-! # Optimizer scaffolding

The reusable framework for building the optimizer out of small, individually-proven passes: the
relation glue (`OutputCircuit.implies`/`.reconstructs`), `PassCorrect`, and `VerifiedPass`
bundling a pass with its own `PassCorrect` proof. -/

/-! ## Net multiplicity over contribution lists

`BusState` is a function (`ApcOptimizer/Spec.lean`), but the pass proofs reason by induction over
the *list* of per-interaction contributions. `multiplicitySum` is that list view and
`OutputCircuit.sideEffects_eq` relates it to the spec's definition. -/

/-- The net multiplicity with which `message` is sent by a list of per-interaction contributions. -/
def multiplicitySum (message : BusMessage p) (state : List (BusMessage p × ZMod p)) : ZMod p :=
  match state with
  | [] => 0
  | (msg, mult) :: tl =>
      (if msg = message then mult else 0) + multiplicitySum message tl

/-- The contribution list of a circuit's stateful interactions under `env`. -/
def OutputCircuit.contributions (circuit : OutputCircuit p) (bs : BusSemantics p)
    (env : OutputVariable → ZMod p) : List (BusMessage p × ZMod p) :=
  (circuit.busInteractions.filter (fun bi => bs.isStateful bi.busId)).map
    (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))

theorem multiplicitySum_map_filter (bs : BusSemantics p) (env : OutputVariable → ZMod p)
    (message : BusMessage p) (bis : List (BusInteraction (OutputExpression p))) :
    (((bis.map (fun bi => bi.eval env)).filter
        (fun m => bs.isStateful m.busId && decide ((m.busId, m.payload) = message))).map
      (fun m => m.multiplicity)).sum
      = multiplicitySum message
          ((bis.filter (fun bi => bs.isStateful bi.busId)).map
            (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))) := by
  induction bis with
  | nil => rfl
  | cons bi rest ih =>
      -- `BusInteraction.eval` keeps `busId`, so the two spellings of the statefulness test agree.
      have hb : bs.isStateful (bi.eval env).busId = bs.isStateful bi.busId := rfl
      by_cases hstate : bs.isStateful bi.busId = true
      · by_cases hmsg : ((bi.eval env).busId, (bi.eval env).payload) = message
        · simp [hb, hstate, hmsg, multiplicitySum, ih]
        · simp [hb, hstate, hmsg, multiplicitySum, ih]
      · simp [hb, hstate, ih]

/-- The spec's `sideEffects` is the net multiplicity of the contribution list. -/
theorem OutputCircuit.sideEffects_eq (cs : OutputCircuit p) (bs : BusSemantics p) (env : OutputVariable → ZMod p)
    (message : BusMessage p) :
    cs.sideEffects bs env message = multiplicitySum message (cs.contributions bs env) :=
  multiplicitySum_map_filter bs env message cs.busInteractions

/-- Soundness half of a replacement: every satisfying assignment of `self` maps to one of `other`
    with the same stateful side effects. The spec's `isSoundReplacementOf` is this plus invariant
    preservation. -/
def OutputCircuit.implies (self other : OutputCircuit p) (busSemantics : BusSemantics p) :
    Prop :=
  ∀ env, self.satisfies busSemantics env →
    ∃ env', other.satisfies busSemantics env' ∧
      self.sideEffects busSemantics env = other.sideEffects busSemantics env'

/-- Every no-powdr-ID variable of `cs` is computed by `ds`'s method for it, reading only powdr-ID
    variables from `inputVars`. Threaded through passes; the pipeline top uses it to match the
    spec's `witgen` output and `Derivations.cover`. -/
def OutputCircuit.reconstructs (inputVars : List InputVariable) (cs : OutputCircuit p)
    (ds : Derivations p) (e : OutputVariable → ZMod p) : Prop :=
  ∀ v ∈ cs.vars, v.powdrId? = none →
    ∃ cm, Derivations.methodFor ds v = some cm ∧
      (∀ x ∈ cm.vars, x ∈ inputVars) ∧
      cm.eval (fun x => e x.toVariable) = e v

theorem OutputCircuit.implies_refl (cs : OutputCircuit p) (busSemantics : BusSemantics p) :
    cs.implies cs busSemantics :=
  fun env hsat => ⟨env, hsat, rfl⟩

theorem OutputCircuit.implies_trans {a b c : OutputCircuit p} {busSemantics : BusSemantics p}
    (h1 : a.implies b busSemantics) (h2 : b.implies c busSemantics) : a.implies c busSemantics :=
  fun env hsat =>
    let ⟨env', hb, hab⟩ := h1 env hsat
    let ⟨env'', hc, hbc⟩ := h2 env' hb
    ⟨env'', hc, (hab.trans hbc)⟩

/-! ## Precomputed primality witness

`decide (Nat.Prime p)` is expensive (≈ √p trial division). `PrimeWitness p` computes it once and
carries the `Bool` with a proof that `true` entails `Nat.Prime p`; the pipeline threads one to each
prime-gated pass, which branches on it in O(1). -/

structure PrimeWitness (p : ℕ) where
  isPrime : Bool
  /-- `isPrime = true` entails `Nat.Prime p` — the fact prime-gated passes consume. -/
  correct : isPrime = true → Nat.Prime p

/-- The single `decide (Nat.Prime p)` per optimizer run. -/
def PrimeWitness.of (p : ℕ) : PrimeWitness p :=
  ⟨decide (Nat.Prime p), fun h => of_decide_eq_true h⟩

/-! ## Verified passes

A `VerifiedPass` maps a constraint system to a new one bundled with a `PassCorrect` proof, so a
pass cannot be written without discharging its obligations. Passes compose with `andThen`. -/

/-- The per-pass correctness obligation: `out` is sound (`implies cs`), preserves invariants, adds
    no new powdr-ID column, and is real-trace complete — every admissible satisfying assignment of
    `cs` extends to one of `out` with equal side effects, preserving input-column values and
    reconstructing `out`'s derived variables. `dsLocal` are the derivations this step introduces,
    concatenated onto any incoming `dsIn` so passes compose. -/
def PassCorrect (cs out : OutputCircuit p) (dsLocal : Derivations p) (bs : BusSemantics p) :
    Prop :=
  out.implies cs bs ∧
  (cs.guaranteesInvariants bs → out.guaranteesInvariants bs) ∧
  (∀ v ∈ out.vars, v.powdrId?.isSome → v ∈ cs.vars) ∧
  (∀ env, cs.admissible bs env → cs.satisfies bs env →
    ∃ env', out.satisfies bs env' ∧ out.admissible bs env' ∧
      cs.sideEffects bs env = out.sideEffects bs env' ∧
      (∀ v, v.powdrId?.isSome → env' v = env v) ∧
      (∀ inputVars, (∀ v ∈ cs.vars, v.powdrId?.isSome → v.toInput ∈ inputVars) →
        ∀ dsIn, cs.reconstructs inputVars dsIn env →
          out.reconstructs inputVars (dsIn ++ dsLocal) env'))

theorem PassCorrect.refl (cs : OutputCircuit p) (bs : BusSemantics p) :
    PassCorrect cs cs [] bs :=
  ⟨cs.implies_refl bs, _root_.id, fun _ hv _ => hv,
   fun env hadm hsat =>
     ⟨env, hsat, hadm, rfl,
       ⟨fun _ _ => rfl, fun _ _ dsIn hrec => by rwa [List.append_nil]⟩⟩⟩

/-- Sequential composition: derivations concatenate, soundness/invariants compose, reconstruction
    chains. -/
theorem PassCorrect.andThen {cs mid out : OutputCircuit p} {bs : BusSemantics p}
    {df dg : Derivations p} (hf : PassCorrect cs mid df bs) (hg : PassCorrect mid out dg bs) :
    PassCorrect cs out (df ++ dg) bs := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨OutputCircuit.implies_trans hg1 hf1, fun h => hg2 (hf2 h),
    fun v hv hpw => hf3 v (hg3 v hv hpw) hpw, fun env hadm hsat => ?_⟩
  obtain ⟨env1, hs1, ha1, he1, hpw1, hr1⟩ := hf4 env hadm hsat
  obtain ⟨env2, hs2, ha2, he2, hpw2, hr2⟩ := hg4 env1 ha1 hs1
  refine ⟨env2, hs2, ha2, (he1.trans he2),
    ⟨fun v hpw => by rw [hpw2 v hpw, hpw1 v hpw],
      fun inputVars hpowIn dsIn hrec => ?_⟩⟩
  have hmidIn : ∀ v ∈ mid.vars, v.powdrId?.isSome → v.toInput ∈ inputVars :=
    fun v hv hpw => hpowIn v (hf3 v hv hpw) hpw
  have := hr2 inputVars hmidIn (dsIn ++ df) (hr1 inputVars hpowIn dsIn hrec)
  rwa [List.append_assoc] at this

/-- The result of a verified pass: transformed system, introduced derivations, correctness proof. -/
structure PassResult {p : ℕ} (cs : OutputCircuit p) (bs : BusSemantics p) where
  out : OutputCircuit p
  derivs : Derivations p
  correct : PassCorrect cs out derivs bs

/-! ## OutputVariable-set membership -/

/-- A variable of `cs.vars` occurs in some constraint, multiplicity, or payload expression. -/
theorem OutputCircuit.mem_vars {cs : OutputCircuit p} {x : OutputVariable} :
    x ∈ cs.vars ↔
      (∃ c ∈ cs.algebraicConstraints, x ∈ c.vars) ∨
      (∃ bi ∈ cs.busInteractions, x ∈ bi.multiplicity.vars ∨ ∃ e ∈ bi.payload, x ∈ e.vars) := by
  simp only [Circuit.vars, List.mem_append, List.mem_flatMap]

theorem OutputCircuit.mem_vars_of_constraint {cs : OutputCircuit p} {c : OutputExpression p}
    {x : OutputVariable} (hc : c ∈ cs.algebraicConstraints) (hx : x ∈ c.vars) : x ∈ cs.vars :=
  OutputCircuit.mem_vars.2 (Or.inl ⟨c, hc, hx⟩)

theorem OutputCircuit.mem_vars_of_mult {cs : OutputCircuit p}
    {bi : BusInteraction (OutputExpression p)} {x : OutputVariable} (hbi : bi ∈ cs.busInteractions)
    (hx : x ∈ bi.multiplicity.vars) : x ∈ cs.vars :=
  OutputCircuit.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inl hx⟩)

theorem OutputCircuit.mem_vars_of_payload {cs : OutputCircuit p}
    {bi : BusInteraction (OutputExpression p)} {e : OutputExpression p} {x : OutputVariable}
    (hbi : bi ∈ cs.busInteractions) (he : e ∈ bi.payload) (hx : x ∈ e.vars) : x ∈ cs.vars :=
  OutputCircuit.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inr ⟨e, he, hx⟩⟩)

private theorem outputExprEval_toInput (e : OutputExpression p) (env : OutputVariable → ZMod p)
    (hpow : ∀ v ∈ e.vars, v.powdrId?.isSome) :
    (e.mapVar OutputVariable.toInput).eval (fun x => env x.toVariable) = e.eval env := by
  induction e with
  | const n => rfl
  | var v =>
      have hv : v.powdrId?.isSome := hpow v (by simp [Expression.vars])
      simp [Expression.mapVar, Expression.eval, OutputVariable.toInput_toVariable hv]
  | add a b iha ihb =>
      simp [Expression.mapVar, Expression.eval,
        iha (fun v hv => hpow v (by simp [Expression.vars, hv])),
        ihb (fun v hv => hpow v (by simp [Expression.vars, hv]))]
  | mul a b iha ihb =>
      simp [Expression.mapVar, Expression.eval,
        iha (fun v hv => hpow v (by simp [Expression.vars, hv])),
        ihb (fun v hv => hpow v (by simp [Expression.vars, hv]))]

private theorem busEval_toInput (bi : BusInteraction (OutputExpression p))
    (env : OutputVariable → ZMod p)
    (hmultIn : ∀ v ∈ bi.multiplicity.vars, v.powdrId?.isSome)
    (hpayloadIn : ∀ e ∈ bi.payload, ∀ v ∈ e.vars, v.powdrId?.isSome) :
    ({ busId := bi.busId,
       multiplicity := bi.multiplicity.mapVar OutputVariable.toInput,
       payload := bi.payload.map (·.mapVar OutputVariable.toInput) } : BusInteraction (InputExpression p)).eval
      (fun x => env x.toVariable) = bi.eval env := by
  have hmult : (bi.multiplicity.mapVar OutputVariable.toInput).eval (fun x => env x.toVariable)
      = bi.multiplicity.eval env :=
    outputExprEval_toInput bi.multiplicity env hmultIn
  have hpayEq :
      bi.payload.map (fun e => e.mapVar OutputVariable.toInput |>.eval (fun x => env x.toVariable))
        = bi.payload.map (fun e => e.eval env) := by
    apply List.map_congr_left
    intro e he
    exact outputExprEval_toInput e env (hpayloadIn e he)
  have hpayEq' :
      List.map ((fun e => e.eval (fun x => env x.toVariable)) ∘ fun x => x.mapVar OutputVariable.toInput)
        bi.payload = bi.payload.map (fun e => e.eval env) := by
    simpa [Function.comp] using hpayEq
  rw [BusInteraction.eval, BusInteraction.eval, hmult, List.map_map, hpayEq']

private theorem OutputCircuit.satisfies_toInput {cs : OutputCircuit p} {bs : BusSemantics p}
    (hpow : ∀ v ∈ cs.vars, v.powdrId?.isSome) (env : OutputVariable → ZMod p) :
    cs.satisfies bs env →
      (cs.mapVar OutputVariable.toInput).satisfies bs (fun x => env x.toVariable) := by
  intro hsat
  refine ⟨?_, ?_⟩
  · intro c hc
    rcases List.mem_map.mp hc with ⟨c', hc', rfl⟩
    simpa [outputExprEval_toInput c' env (fun v hv => hpow v (OutputCircuit.mem_vars_of_constraint hc' hv))]
      using hsat.1 c' hc'
  · intro bi hbi
    rcases List.mem_map.mp hbi with ⟨bi', hbi', rfl⟩
    have hbe := busEval_toInput bi' env
      (fun v hv => hpow v (OutputCircuit.mem_vars_of_mult hbi' hv))
      (fun e he v hv => hpow v (OutputCircuit.mem_vars_of_payload hbi' he hv))
    simpa [hbe] using hsat.2 bi' hbi'

private theorem OutputCircuit.sideEffects_toInput {cs : OutputCircuit p} {bs : BusSemantics p}
    (hpow : ∀ v ∈ cs.vars, v.powdrId?.isSome) (env : OutputVariable → ZMod p) :
    (cs.mapVar OutputVariable.toInput).sideEffects bs (fun x => env x.toVariable) = cs.sideEffects bs env := by
  have hmap : (cs.mapVar OutputVariable.toInput).busInteractions.map
      (fun bi => bi.eval (fun x => env x.toVariable))
      = cs.busInteractions.map (fun bi => bi.eval env) := by
    rw [Circuit.mapVar, List.map_map]
    refine List.map_congr_left ?_
    intro bi hbi
    exact busEval_toInput bi env
      (fun v hv => hpow v (OutputCircuit.mem_vars_of_mult hbi hv))
      (fun e he v hv => hpow v (OutputCircuit.mem_vars_of_payload hbi he hv))
  unfold Circuit.sideEffects
  rw [hmap]

private theorem OutputCircuit.guaranteesInvariants_toInput {cs : OutputCircuit p} {bs : BusSemantics p}
    (hpow : ∀ v ∈ cs.vars, v.powdrId?.isSome) :
    (cs.mapVar OutputVariable.toInput).guaranteesInvariants bs → cs.guaranteesInvariants bs := by
  intro hgi env hsat bi hbi
  change (bi.eval env).multiplicity ≠ 0 → bs.maintainsInvariants (bi.eval env)
  let bi' : BusInteraction (InputExpression p) :=
    { busId := bi.busId,
      multiplicity := bi.multiplicity.mapVar OutputVariable.toInput,
      payload := bi.payload.map (·.mapVar OutputVariable.toInput) }
  have hbi' : bi' ∈ (cs.mapVar OutputVariable.toInput).busInteractions := by
    exact List.mem_map.mpr ⟨bi, hbi, rfl⟩
  have hbe := busEval_toInput bi env
    (fun v hv => hpow v (OutputCircuit.mem_vars_of_mult hbi hv))
    (fun e he v hv => hpow v (OutputCircuit.mem_vars_of_payload hbi he hv))
  intro hmult
  have hmaint := hgi (fun x => env x.toVariable) (OutputCircuit.satisfies_toInput hpow env hsat) bi' hbi'
  change (bi'.eval (fun x => env x.toVariable)).multiplicity ≠ 0 →
      bs.maintainsInvariants (bi'.eval (fun x => env x.toVariable)) at hmaint
  have hmult' : (bi'.eval (fun x => env x.toVariable)).multiplicity ≠ 0 := by
    simpa [bi', hbe] using hmult
  have hres := hmaint hmult'
  simpa [bi', hbe] using hres

/-- A `PassCorrect` gives the audited `isSoundReplacementOf` when the source circuit carries only
    powdr-id variables. The completeness half is discharged at the pipeline top
    (`Implementation/Optimizer.lean`). -/
theorem PassCorrect.toSound {cs out : OutputCircuit p} {ds : Derivations p}
    {bs : BusSemantics p} (hpow : ∀ v ∈ cs.vars, v.powdrId?.isSome) (h : PassCorrect cs out ds bs) :
    out.isSoundReplacementOf (cs.mapVar OutputVariable.toInput) bs := by
  refine ⟨?_, ?_⟩
  · intro assignment hsat
    obtain ⟨assignment', hsat', hside⟩ := h.1 assignment hsat
    refine ⟨fun x => assignment' x.toVariable, OutputCircuit.satisfies_toInput hpow assignment' hsat', ?_⟩
    rw [OutputCircuit.sideEffects_toInput hpow assignment']
    exact hside
  · intro hgi
    exact h.2.1 (OutputCircuit.guaranteesInvariants_toInput hpow hgi)

/-! ## Decidable degree-bound check

A `Bool` twin of the spec's `Circuit.withinDegree` for the degree guard to branch on. -/

/-- Decidable twin of `Circuit.withinDegree`. -/
def OutputCircuit.withinDegreeB (s : OutputCircuit p) (b : DegreeBound) : Bool :=
  s.algebraicConstraints.all (fun c => c.degree ≤ b.identities) &&
  s.busInteractions.all (fun bi =>
    decide (bi.multiplicity.degree ≤ b.busInteractions) &&
      bi.payload.all (fun e => e.degree ≤ b.busInteractions))

theorem OutputCircuit.withinDegreeB_iff (s : OutputCircuit p) (b : DegreeBound) :
    s.withinDegreeB b = true ↔ s.withinDegree b := by
  unfold OutputCircuit.withinDegreeB Circuit.withinDegree
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcm => by simpa using hc c hcm, fun bi hbm => ?_⟩
    have := hb bi hbm
    rw [Bool.and_eq_true, List.all_eq_true] at this
    exact ⟨by simpa using this.1, fun e he => by simpa using this.2 e he⟩
  · rintro ⟨hc, hb⟩
    refine ⟨fun c hcm => by simpa using hc c hcm, fun bi hbm => ?_⟩
    rw [Bool.and_eq_true, List.all_eq_true]
    exact ⟨by simpa using (hb bi hbm).1, fun e he => by simpa using (hb bi hbm).2 e he⟩
