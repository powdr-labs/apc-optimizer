import ApcOptimizer.Implementation.OptimizerPasses.Basic
import ApcOptimizer.Implementation.OptimizerPasses.FactPass
import ApcOptimizer.Implementation.OptimizerPasses.DomainProp
import ApcOptimizer.Implementation.OptimizerPasses.MonicScale
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.MonicScale
import ApcOptimizer.Implementation.OptimizerPasses.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.TupleRange
import ApcOptimizer.Implementation.OptimizerPasses.DisconnectedComponent
import ApcOptimizer.Implementation.OptimizerPasses.Reencode
import ApcOptimizer.Implementation.OptimizerPasses.HintCollapse
import ApcOptimizer.Implementation.OptimizerPasses.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.RedundantByteDrop
import ApcOptimizer.Implementation.OptimizerPasses.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.SubsumedCheck
import ApcOptimizer.Implementation.OptimizerPasses.XorEqExtract
import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.SplitBytePair
import ApcOptimizer.Implementation.OptimizerPasses.SeqzCollapse
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.SeqzCollapse
import ApcOptimizer.Implementation.OptimizerPasses.IntervalForce
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DegenRange
import ApcOptimizer.Implementation.OptimizerPasses.IdentitySubst
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.IdentitySubst
import ApcOptimizer.Implementation.OptimizerPasses.DenseUmbrella

set_option autoImplicit false

open ApcOptimizer.Dense

variable {p : ℕ}

/-! # The circuit optimizer pipeline (implementation)

Assembles the passes (`OptimizerPasses/`) into the fact-aware `optimizerWithBusFacts`. The audited
correctness theorems in `ApcOptimizer/Optimizer.lean` are projections of `optimizerWithBusFacts_correct` /
`optimizerWithBusFacts_respectsDegree` proved here. To add a pass, see AGENTS.md → "Adding an optimization". -/

/-- Wrap every pass of a stage list in the degree guard, so degree safety holds uniformly
    (`guardAll_chain_respectsDeg`) with zero per-pass proof burden. -/
def guardAll (b : DegreeBound) (l : List (String × DenseVerifiedPassW p)) :
    List (String × DenseVerifiedPassW p) :=
  l.map (fun (n, f) => (n, f.guardDegree b))

/-- Stage 1 of 3 (`preludePasses`, `cleanupPasses`, `codaPasses`): run once to canonicalize the
    freshly-parsed system. The three lists are the single source of truth for the pass sequence —
    `pipeline` folds them and the `profile` CLI (`Main.lean`) times the same lists, so they cannot
    drift. `String` labels name passes in the profiler only. -/
def preludePasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  guardAll b [ ("constFold0", denseConstantFoldPass) ]

/-- Stage 2 of 3 (see `preludePasses`): the cleanup schedule, iterated to a fixpoint
    (`denseIterateToFixpoint`, no budget). Each entry's optimization is documented at its own
    definition. To add a pass, append one `(name, pass)` entry here (AGENTS.md →
    "Adding an optimization"). -/
def cleanupPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  -- One primality decision per run, threaded to every prime-gated pass (each reads the `Bool` in
  -- O(1) instead of re-running `decide (Nat.Prime p)`).
  let pw := PrimeWitness.of p
  guardAll b
  [ ("degenRange", denseDegenRangePass pw),
    ("xorEqExtract", denseXorEqExtractPass),
    ("carryBranch", denseCarryBranchPass pw),
    ("gauss", denseGaussElimPass),
    ("normalize1", denseNormalizePass),
    ("constFold1", denseConstantFoldPass),
    ("domainBatch", denseDomainBatchPassV pw),
    ("normalize2", denseNormalizePass),
    ("constFold2", denseConstantFoldPass),
    ("zeroRegister", denseZeroRegisterPass),
    ("intervalForce", denseIntervalForcePass),
    ("digitFold", denseDigitFoldPass),
    ("oneHotAnnihilate", denseOneHotAnnihilatePass),
    ("hintCollapse", denseHintCollapsePass pw),
    ("rootPairUnify", denseRootPairUnifyPass pw),
    ("flagUnify", denseFlagUnifyPass pw),
    ("flagFold", denseFlagFoldPass' pw b),
    ("dedup", denseDedupPass),
    ("trivialConstr", denseTrivialConstraintDropPass),
    ("zeroMultBus", denseZeroMultBusDropPass),
    ("tautoBus", denseTautoBusDropPass),
    ("domainFold", denseDomainFoldPassV pw),
    ("busUnify", denseBusUnifyPass),
    ("busPairCancel", denseBusPairCancelPass pw false),
    ("bytePack", denseByteCheckPackPass),
    ("disconnected", denseDisconnectedPass),
    ("reencode", denseReencodePass pw b) ]

/-- Stage 3 of 3 (see `preludePasses`): run once after the cleanup fixpoint. Order matters — the
    inline notes below flag the non-obvious sequencing; each pass's own definition documents what it
    does. -/
def codaPasses (b : DegreeBound) : List (String × DenseVerifiedPassW p) :=
  let pw := PrimeWitness.of p
  guardAll b
  [ ("busPairCancelLate", denseBusPairCancelPass pw true),
    -- Explode packed pair byte checks into singles so `dedupLate`/`redundantByteDrop` act
    -- operand-granularly; `bytePackLate` re-packs the survivors.
    ("splitBytePair", denseSplitBytePairPass),
    -- Rename OR-identity results to their operand before drop/pack, exposing degenerate byte checks
    -- (`[or, x, x, 0]`) for `dedupLate`/`redundantByteDrop`/`bytePackLate`.
    ("identitySubst", denseIdentitySubstPass),
    ("dedupLate", denseDedupPass),
    ("redundantByteDrop", denseRedundantByteDropPass pw),
    ("subsumedRange", denseSubsumedRangeDropPass),
    ("subsumedCheck", denseSubsumedCheckDropPass),
    -- Layout-only packing, run after `redundantByteDrop` (packing earlier would hide byte checks
    -- from the drop). Drains every packable pair internally, so no fixpoint wrapper.
    ("tupleRange", denseTupleRangePass),
    ("bytePackLate", denseByteCheckPackPass),
    ("monicScale", denseMonicScalePass),
    ("constFoldEnd", denseConstantFoldPass),
    -- After `monicScale`, where the seqz cluster reaches its recognised form.
    ("seqzCollapse", denseSeqzCollapsePass) ]

/-! ## The dense pipeline

Runs over the dense `VarId` representation: prelude chain, cleanup fixpoint, coda chain, wrapped
between a single encode at entry and a single decode at output (no decode between passes). -/

/-- Every pass of a `guardAll`-built stage list respects the degree bound — one lemma covering all
    three stage lists, with no per-entry case analysis. -/
theorem guardAll_chain_respectsDeg (b : DegreeBound) (l : List (String × DenseVerifiedPassW p)) :
    DenseRespectsDeg b (denseChain ((guardAll b l).map (·.2))) := by
  apply denseChain_respectsDeg
  intro f hf
  simp only [guardAll, List.map_map, List.mem_map] at hf
  obtain ⟨⟨n, g⟩, -, rfl⟩ := hf
  exact DenseVerifiedPassW.guardDegree_respectsDeg _

/-- The dense pipeline body: prelude chain, then the cleanup cycle to a fixpoint
    (`denseIterateToFixpoint`, no budget — runs until the lexicographic dense size key stops
    shrinking), then the coda chain. -/
def densePipeline (b : DegreeBound) : DenseVerifiedPassW p :=
  DenseVerifiedPassW.andThen (denseChain ((preludePasses b).map (·.2)))
    (DenseVerifiedPassW.andThen
      (denseIterateToFixpoint (denseChain ((cleanupPasses b).map (·.2))))
      (denseChain ((codaPasses b).map (·.2))))

theorem densePipeline_respectsDeg (b : DegreeBound) :
    DenseRespectsDeg b (densePipeline (p := p) b) := by
  unfold densePipeline preludePasses cleanupPasses codaPasses
  exact DenseVerifiedPassW.andThen_respectsDeg (guardAll_chain_respectsDeg b _)
    (DenseVerifiedPassW.andThen_respectsDeg
      (denseIterateToFixpoint_respectsDeg (guardAll_chain_respectsDeg b _))
      (guardAll_chain_respectsDeg b _))

/-- The circuit optimizer: encode once into the dense `VarId` representation, run `densePipeline`,
    then decode the result and its derivations once. `decode ∘ encode = id` turns the dense
    pipeline's `PassCorrect` into one against the original system. -/
def pipeline (b : DegreeBound) : VerifiedPassW p := fun cs bs facts =>
  let e := VarRegistry.empty.encodeCS cs
  let r := densePipeline b e.1 e.2 (VarRegistry.empty.encodeCS_covered cs) bs facts
  ⟨r.reg'.decodeCS r.out, r.reg'.decodeDerivs r.derivs, by
    have hc := r.correct
    rw [(VarRegistry.empty.decodeCS_encodeCS cs : e.1.decodeCS e.2 = cs)] at hc
    exact hc⟩

theorem pipeline_respectsDeg (b : DegreeBound) : RespectsDeg b (pipeline (p := p) b) := by
  intro cs bs facts hin
  exact densePipeline_respectsDeg b (VarRegistry.empty.encodeCS cs).1
    (VarRegistry.empty.encodeCS cs).2 (VarRegistry.empty.encodeCS_covered cs) bs facts
    (by rw [VarRegistry.empty.decodeCS_encodeCS cs]; exact hin)

/-- Use `ds`'s method for `v` when it reads only `inputVars`; otherwise use a constant fallback. -/
def Derivations.safeMethod (ds : Derivations p) (inputVars : List Variable) (v : Variable) :
    ComputationMethod p :=
  match ds.methodFor v with
  | some cm => if ∀ x ∈ cm.vars, x ∈ inputVars then cm else .const 0
  | none => .const 0

/-- Keep one structurally safe derivation for each no-ID output variable. -/
def Derivations.forOutput (ds : Derivations p) (inputVars outputVars : List Variable) :
    Derivations p :=
  (outputVars.filter (fun v => v.powdrId?.isNone)).eraseDups.map
    (fun v => (v, ds.safeMethod inputVars v))

/-- The fact-aware circuit optimizer: given proven `BusFacts` (which fixes the implicit `bs`), run
    the pipeline and return the output system with the `Derivations` for its new variables. -/
def optimizerWithBusFacts {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : Circuit p) : Circuit p × Derivations p :=
  let r := pipeline b cs bs facts
  (r.out, r.derivs.forOutput cs.vars r.out.vars)

/-! ## Evaluation depends only on a system's variables

Two assignments agreeing on `cs.vars` are interchangeable for `satisfies`/`admissible`/`sideEffects`.
The completeness proof below uses these to swap the abstract per-pass witness for `witgen`'s output. -/

theorem Circuit.busEval_congr {cs : Circuit p} {f g : Variable → ZMod p}
    (h : ∀ x ∈ cs.vars, f x = g x) {bi : BusInteraction (Expression p)}
    (hbi : bi ∈ cs.busInteractions) : bi.eval f = bi.eval g :=
  BusInteraction.eval_congr bi f g (fun x hx => by
    simp only [BusInteraction.vars, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨e, he, hx⟩
    · exact h x (Circuit.mem_vars_of_mult hbi hx)
    · exact h x (Circuit.mem_vars_of_payload hbi he hx))

theorem Circuit.satisfies_congr {cs : Circuit p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.satisfies bs f ↔ cs.satisfies bs g := by
  have imp : ∀ e1 e2 : Variable → ZMod p, (∀ x ∈ cs.vars, e1 x = e2 x) →
      cs.satisfies bs e1 → cs.satisfies bs e2 := by
    intro e1 e2 hh hsat
    refine ⟨fun c hc => ?_, fun bi hbi => ?_⟩
    · rw [← Expression.eval_congr c e1 e2
        (fun x hx => hh x (Circuit.mem_vars_of_constraint hc hx))]
      exact hsat.1 c hc
    · have hbe : bi.eval e1 = bi.eval e2 := Circuit.busEval_congr hh hbi
      show (bi.eval e2).multiplicity ≠ 0 → bs.violatesConstraint (bi.eval e2) = false
      rw [← hbe]
      exact hsat.2 bi hbi
  exact ⟨imp f g h, imp g f (fun x hx => (h x hx).symm)⟩

theorem Circuit.admissible_congr {cs : Circuit p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.admissible bs f ↔ cs.admissible bs g := by
  have hmap : (cs.busInteractions.map (fun bi => bi.eval f))
      = (cs.busInteractions.map (fun bi => bi.eval g)) :=
    List.map_congr_left (fun bi hbi => Circuit.busEval_congr h hbi)
  unfold Circuit.admissible
  rw [hmap]

theorem Circuit.sideEffects_congr {cs : Circuit p} {bs : BusSemantics p}
    {f g : Variable → ZMod p} (h : ∀ x ∈ cs.vars, f x = g x) :
    cs.sideEffects bs f = cs.sideEffects bs g := by
  unfold Circuit.sideEffects
  refine List.map_congr_left (fun bi hbi => ?_)
  simp only [Circuit.busEval_congr h (List.mem_of_mem_filter hbi)]

theorem Derivations.methodFor_map_same (vs : List Variable)
    (f : Variable → ComputationMethod p) (v : Variable) :
    Derivations.methodFor (vs.map (fun u => (u, f u))) v =
      if v ∈ vs then some (f v) else none := by
  induction vs with
  | nil => rfl
  | cons u rest ih =>
      simp only [List.map_cons, Derivations.methodFor, ih, List.mem_cons]
      by_cases hvrest : v ∈ rest
      · simp [hvrest]
      · by_cases huv : u = v
        · subst u
          simp [hvrest]
        · have hvu : ¬v = u := fun h => huv h.symm
          simp [hvrest, huv, hvu]

theorem Derivations.forOutput_methodFor {ds : Derivations p} {inputVars outputVars : List Variable}
    {v : Variable} (hv : v ∈ outputVars) (hpw : v.powdrId? = none) :
    (ds.forOutput inputVars outputVars).methodFor v = some (ds.safeMethod inputVars v) := by
  unfold Derivations.forOutput
  rw [Derivations.methodFor_map_same, if_pos]
  simp [hv, hpw]

theorem Derivations.safeMethod_vars (ds : Derivations p) (inputVars : List Variable) (v : Variable) :
    ∀ x ∈ (ds.safeMethod inputVars v).vars, x ∈ inputVars := by
  cases hm : ds.methodFor v with
  | none =>
      intro x hx
      simp [Derivations.safeMethod, hm, ComputationMethod.vars] at hx
  | some cm =>
      simp only [Derivations.safeMethod, hm]
      by_cases hsafe : ∀ x ∈ cm.vars, x ∈ inputVars
      · rw [if_pos hsafe]
        exact hsafe
      · rw [if_neg hsafe]
        simp [ComputationMethod.vars]

theorem Derivations.safeMethod_eq {ds : Derivations p} {inputVars : List Variable}
    {v : Variable} {cm : ComputationMethod p} (hm : ds.methodFor v = some cm)
    (hvars : ∀ x ∈ cm.vars, x ∈ inputVars) :
    ds.safeMethod inputVars v = cm := by
  simp only [Derivations.safeMethod, hm]
  rw [if_pos hvars]

/-- The fact-aware optimizer is correct: its output soundly replaces the input and completely
    replaces the input's real-trace executions (`witgen` on any admissible input trace reproduces a
    valid witness) — the clauses `Optimizer.isCorrect` demands. -/
theorem optimizerWithBusFacts_correct {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : Circuit p) :
    (optimizerWithBusFacts b facts cs).1.isSoundReplacementOf cs bs ∧
      (optimizerWithBusFacts b facts cs).1.isCompleteReplacementOf cs bs (optimizerWithBusFacts b facts cs).2 := by
  refine ⟨(pipeline b cs bs facts).correct.toSound, ?_⟩
  intro hpow
  refine ⟨?_, ?_, ?_⟩
  · -- `forOutput` records only no-ID variables occurring in the output.
    intro d hd
    change d ∈ (pipeline b cs bs facts).derivs.forOutput cs.vars
      (pipeline b cs bs facts).out.vars at hd
    change d.1 ∈ (pipeline b cs bs facts).out.vars
    rw [Derivations.forOutput, List.mem_map] at hd
    obtain ⟨v, hv, rfl⟩ := hd
    exact List.mem_of_mem_filter (List.mem_eraseDups.mp hv)
  · -- Every output variable is either reused from the input or has a safe method.
    intro v hv
    cases hpw : v.powdrId? with
    | some w =>
        obtain ⟨_himpl, _hinv, hS, _hcomp⟩ := (pipeline b cs bs facts).correct
        exact hS v hv (by simp [hpw])
    | none =>
        exact ⟨(pipeline b cs bs facts).derivs.safeMethod cs.vars v,
          Derivations.forOutput_methodFor hv hpw,
          Derivations.safeMethod_vars _ _ _⟩
  intro env hadm hsat
  obtain ⟨_himpl, _hinv, hS, hcomp⟩ := (pipeline b cs bs facts).correct
  obtain ⟨env', hsat', hadm', hse, hA, hR⟩ := hcomp env hadm hsat
  have hrec : (pipeline b cs bs facts).out.reconstructs cs.vars
      (pipeline b cs bs facts).derivs env' := by
    have hrec0 : cs.reconstructs cs.vars [] env :=
      fun u hu hunone => absurd (hpow u hu) (by simp [hunone])
    simpa using hR cs.vars (fun v hv _ => hv) [] hrec0
  have hagree : ∀ v ∈ (pipeline b cs bs facts).out.vars,
      Derivations.witgen ((pipeline b cs bs facts).derivs.forOutput cs.vars
        (pipeline b cs bs facts).out.vars) env v = env' v := by
    intro v hv
    cases hpw : v.powdrId? with
    | some w =>
        simp only [Derivations.witgen, hpw]
        exact (hA v (by simp [hpw])).symm
    | none =>
        obtain ⟨cm, hm, hxpow, hxinput, heq⟩ := hrec v hv hpw
        have hsafe : (pipeline b cs bs facts).derivs.safeMethod cs.vars v = cm :=
          Derivations.safeMethod_eq hm hxinput
        have hm' := Derivations.forOutput_methodFor
          (ds := (pipeline b cs bs facts).derivs) (inputVars := cs.vars)
          (outputVars := (pipeline b cs bs facts).out.vars) hv hpw
        rw [hsafe] at hm'
        simp only [Derivations.witgen, hpw, hm']
        rw [← heq]
        exact ComputationMethod.eval_congr cm env env' (fun x hx => (hA x (hxpow x hx)).symm)
  refine ⟨(Circuit.satisfies_congr hagree).mpr hsat',
    (Circuit.admissible_congr hagree).mpr hadm', ?_⟩
  · have hse' : cs.sideEffects bs env
          ≈ (pipeline b cs bs facts).out.sideEffects bs (Derivations.witgen
              ((pipeline b cs bs facts).derivs.forOutput cs.vars
                (pipeline b cs bs facts).out.vars) env) := by
        rw [Circuit.sideEffects_congr hagree]
        exact hse
    simpa only [optimizerWithBusFacts] using hse'

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (b : DegreeBound)
    (facts : BusFacts p bs) (cs : Circuit p)
    (h : cs.withinDegree b) :
    (optimizerWithBusFacts b facts cs).1.withinDegree b :=
  pipeline_respectsDeg b cs bs facts h
