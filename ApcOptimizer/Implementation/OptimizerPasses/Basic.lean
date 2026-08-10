import ApcOptimizer.Spec
import ApcOptimizer.Implementation.Variable

set_option autoImplicit false

variable {p : ℕ}

/-! # Optimizer scaffolding

The reusable framework for building the optimizer out of small, individually-proven passes: the
relation glue (`Circuit.implies`/`.reconstructs`), `PassCorrect`, and `VerifiedPass`
bundling a pass with its own `PassCorrect` proof. -/

/-! ## Net multiplicity over contribution lists

`BusState` is a function (`ApcOptimizer/Spec.lean`), but the pass proofs reason by induction over
the *list* of per-interaction contributions. `multiplicitySum` is that list view and
`Circuit.sideEffects_eq` relates it to the spec's definition. -/

/-- The net multiplicity with which `message` is sent by a list of per-interaction contributions. -/
def multiplicitySum (message : BusMessage p) (state : List (BusMessage p × ZMod p)) : ZMod p :=
  match state with
  | [] => 0
  | (msg, mult) :: tl =>
      (if msg = message then mult else 0) + multiplicitySum message tl

/-- The contribution list of a circuit's stateful interactions under `env`. -/
def Circuit.contributions (circuit : Circuit p) (bs : BusSemantics p)
    (env : Variable → ZMod p) : List (BusMessage p × ZMod p) :=
  (circuit.busInteractions.filter (fun bi => bs.isStateful bi.busId)).map
    (fun bi => let m := bi.eval env; ((m.busId, m.payload), m.multiplicity))

theorem multiplicitySum_map_filter (bs : BusSemantics p) (env : Variable → ZMod p)
    (message : BusMessage p) (bis : List (BusInteraction (Expression p))) :
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
theorem Circuit.sideEffects_eq (cs : Circuit p) (bs : BusSemantics p) (env : Variable → ZMod p)
    (message : BusMessage p) :
    cs.sideEffects bs env message = multiplicitySum message (cs.contributions bs env) :=
  multiplicitySum_map_filter bs env message cs.busInteractions

/-- Soundness half of a replacement: every satisfying assignment of `self` maps to one of `other`
    with the same stateful side effects. The spec's `isSoundReplacementOf` is this plus invariant
    preservation. -/
def Circuit.implies (self other : Circuit p) (busSemantics : BusSemantics p) :
    Prop :=
  ∀ env, self.satisfies busSemantics env →
    ∃ env', other.satisfies busSemantics env' ∧
      self.sideEffects busSemantics env = other.sideEffects busSemantics env'

/-- Every no-powdr-ID variable of `cs` is computed by `ds`'s method for it, reading only powdr-ID
    variables from `inputVars`. Threaded through passes; the pipeline top uses it to match the
    spec's `witgen` output and `Derivations.cover`. -/
def Circuit.reconstructs (inputVars : List Variable) (cs : Circuit p)
    (ds : Derivations p) (e : Variable → ZMod p) : Prop :=
  ∀ v ∈ cs.vars, v.powdrId? = none →
    ∃ cm, Derivations.methodFor ds v = some cm ∧
      (∀ x ∈ cm.vars, x.powdrId?.isSome) ∧
      (∀ x ∈ cm.vars, x ∈ inputVars) ∧
      cm.eval e = e v

theorem Circuit.implies_refl (cs : Circuit p) (busSemantics : BusSemantics p) :
    cs.implies cs busSemantics :=
  fun env hsat => ⟨env, hsat, rfl⟩

theorem Circuit.implies_trans {a b c : Circuit p} {busSemantics : BusSemantics p}
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
def PassCorrect (cs out : Circuit p) (dsLocal : Derivations p) (bs : BusSemantics p) :
    Prop :=
  out.implies cs bs ∧
  (cs.guaranteesInvariants bs → out.guaranteesInvariants bs) ∧
  (∀ v ∈ out.vars, v.powdrId?.isSome → v ∈ cs.vars) ∧
  (∀ env, cs.admissible bs env → cs.satisfies bs env →
    ∃ env', out.satisfies bs env' ∧ out.admissible bs env' ∧
      cs.sideEffects bs env = out.sideEffects bs env' ∧
      (∀ v, v.powdrId?.isSome → env' v = env v) ∧
      (∀ inputVars, (∀ v ∈ cs.vars, v.powdrId?.isSome → v ∈ inputVars) →
        ∀ dsIn, cs.reconstructs inputVars dsIn env →
          out.reconstructs inputVars (dsIn ++ dsLocal) env'))

theorem PassCorrect.refl (cs : Circuit p) (bs : BusSemantics p) :
    PassCorrect cs cs [] bs :=
  ⟨cs.implies_refl bs, _root_.id, fun _ hv _ => hv,
   fun env hadm hsat =>
     ⟨env, hsat, hadm, rfl,
       ⟨fun _ _ => rfl, fun _ _ dsIn hrec => by rwa [List.append_nil]⟩⟩⟩

/-- Sequential composition: derivations concatenate, soundness/invariants compose, reconstruction
    chains. -/
theorem PassCorrect.andThen {cs mid out : Circuit p} {bs : BusSemantics p}
    {df dg : Derivations p} (hf : PassCorrect cs mid df bs) (hg : PassCorrect mid out dg bs) :
    PassCorrect cs out (df ++ dg) bs := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨Circuit.implies_trans hg1 hf1, fun h => hg2 (hf2 h),
    fun v hv hpw => hf3 v (hg3 v hv hpw) hpw, fun env hadm hsat => ?_⟩
  obtain ⟨env1, hs1, ha1, he1, hpw1, hr1⟩ := hf4 env hadm hsat
  obtain ⟨env2, hs2, ha2, he2, hpw2, hr2⟩ := hg4 env1 ha1 hs1
  refine ⟨env2, hs2, ha2, (he1.trans he2),
    ⟨fun v hpw => by rw [hpw2 v hpw, hpw1 v hpw],
      fun inputVars hpowIn dsIn hrec => ?_⟩⟩
  have hmidIn : ∀ v ∈ mid.vars, v.powdrId?.isSome → v ∈ inputVars :=
    fun v hv hpw => hpowIn v (hf3 v hv hpw) hpw
  have := hr2 inputVars hmidIn (dsIn ++ df) (hr1 inputVars hpowIn dsIn hrec)
  rwa [List.append_assoc] at this

/-- A `PassCorrect` gives the audited `isSoundReplacementOf`. The completeness half is discharged
    at the pipeline top (`Implementation/Optimizer.lean`). -/
theorem PassCorrect.toSound {cs out : Circuit p} {ds : Derivations p}
    {bs : BusSemantics p} (h : PassCorrect cs out ds bs) : out.isSoundReplacementOf cs bs :=
  ⟨h.1, h.2.1⟩

/-- The result of a verified pass: transformed system, introduced derivations, correctness proof. -/
structure PassResult {p : ℕ} (cs : Circuit p) (bs : BusSemantics p) where
  out : Circuit p
  derivs : Derivations p
  correct : PassCorrect cs out derivs bs

/-! ## Variable-set membership -/

/-- A variable of `cs.vars` occurs in some constraint, multiplicity, or payload expression. -/
theorem Circuit.mem_vars {cs : Circuit p} {x : Variable} :
    x ∈ cs.vars ↔
      (∃ c ∈ cs.algebraicConstraints, x ∈ c.vars) ∨
      (∃ bi ∈ cs.busInteractions, x ∈ bi.multiplicity.vars ∨ ∃ e ∈ bi.payload, x ∈ e.vars) := by
  simp only [CircuitG.vars, List.mem_append, List.mem_flatMap]

theorem Circuit.mem_vars_of_constraint {cs : Circuit p} {c : Expression p}
    {x : Variable} (hc : c ∈ cs.algebraicConstraints) (hx : x ∈ c.vars) : x ∈ cs.vars :=
  Circuit.mem_vars.2 (Or.inl ⟨c, hc, hx⟩)

theorem Circuit.mem_vars_of_mult {cs : Circuit p}
    {bi : BusInteraction (Expression p)} {x : Variable} (hbi : bi ∈ cs.busInteractions)
    (hx : x ∈ bi.multiplicity.vars) : x ∈ cs.vars :=
  Circuit.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inl hx⟩)

theorem Circuit.mem_vars_of_payload {cs : Circuit p}
    {bi : BusInteraction (Expression p)} {e : Expression p} {x : Variable}
    (hbi : bi ∈ cs.busInteractions) (he : e ∈ bi.payload) (hx : x ∈ e.vars) : x ∈ cs.vars :=
  Circuit.mem_vars.2 (Or.inr ⟨bi, hbi, Or.inr ⟨e, he, hx⟩⟩)

/-! ## Decidable degree-bound check

A `Bool` twin of the spec's `CircuitG.withinDegree` for the degree guard to branch on. -/

/-- Decidable twin of `CircuitG.withinDegree`. -/
def Circuit.withinDegreeB (s : Circuit p) (b : DegreeBound) : Bool :=
  s.algebraicConstraints.all (fun c => c.degree ≤ b.identities) &&
  s.busInteractions.all (fun bi =>
    decide (bi.multiplicity.degree ≤ b.busInteractions) &&
      bi.payload.all (fun e => e.degree ≤ b.busInteractions))

theorem Circuit.withinDegreeB_iff (s : Circuit p) (b : DegreeBound) :
    s.withinDegreeB b = true ↔ s.withinDegree b := by
  unfold Circuit.withinDegreeB CircuitG.withinDegree
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
