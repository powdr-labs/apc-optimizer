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
import ApcOptimizer.Implementation.OptimizerPasses.HashedDedup
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.FlagFold
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusForward
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.ExecChain
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusSweep

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
    ("gauss", denseGaussElimFPass),
    ("normalize1", denseNormalizePass),
    ("constFold1", denseConstantFoldPass),
    ("domainBatch", dbDomainBatchPass pw),
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
    ("execChain", denseExecChainPass),
    ("busUnify", denseBusUnifyPass),
    ("busSweep", denseBusSweepPass),
    ("busForward", denseBusForwardPass),
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
  | some cm => if ∀ x ∈ cm.vars, x ∈ inputVars then cm else .const (zmodZeroP _)
  | none => .const (zmodZeroP _)

/-- `Derivations.safeMethod` with both of its scans served from indexes: `methods` is `ds` keyed by
    derived variable, `inputs` holds the input variables (`safeMethodIdx_eq`). -/
def Derivations.safeMethodIdx (methods : Std.HashMap Variable (ComputationMethod p))
    (inputs : Std.HashSet Variable) (v : Variable) : ComputationMethod p :=
  match methods[v]? with
  | some cm => if cm.vars.all (fun x => inputs.contains x) then cm else .const (zmodZeroP _)
  | none => .const (zmodZeroP _)

/-- Keep one structurally safe derivation for each no-ID output variable.

    Both `Circuit.vars` lists count variable *occurrences*, so every scan here is indexed:
    `methodFor` walks all of `ds` on each lookup, and the input-variable test would rescan
    `inputVars` per referenced variable. `forOutput_eq` is the index-free reading. -/
def Derivations.forOutput (ds : Derivations p) (inputVars outputVars : List Variable) :
    Derivations p :=
  let methods := Std.HashMap.ofList ds
  let inputs := Std.HashSet.ofList inputVars
  (HashedDedup.hashedEraseDups hash (outputVars.filter (fun v => v.powdrId?.isNone))).map
    (fun v => (v, Derivations.safeMethodIdx methods inputs v))

/-! ## Cloning the input

The pipeline traverses the input circuit many times, so its heap layout matters, and a circuit from
`JsonParser` is laid out badly: it was allocated while the whole `Lean.Json` graph was still live, so
its nodes sit scattered over an address range that is dead by the time the pipeline runs. Rebuilding
it then repacks them. `Circuit.clone_eq`: the rebuild is the identity, so only the timing changes. -/

/-- Rebuild an expression node by node, so the result is freshly allocated. -/
def Expression.clone : Expression p → Expression p
  | .const c => .const c
  | .var v => .var v
  | .add a b => .add a.clone b.clone
  | .mul a b => .mul a.clone b.clone

def Circuit.clone (cs : Circuit p) : Circuit p :=
  { algebraicConstraints := cs.algebraicConstraints.map (fun e => e.clone),
    busInteractions := cs.busInteractions.map (fun bi =>
      { bi with multiplicity := bi.multiplicity.clone,
                payload := bi.payload.map (fun e => e.clone) }) }

theorem Expression.clone_eq (e : Expression p) : e.clone = e := by
  induction e with
  | const n => rfl
  | var x => rfl
  | add a b iha ihb => simp [Expression.clone, iha, ihb]
  | mul a b iha ihb => simp [Expression.clone, iha, ihb]

theorem Circuit.clone_eq (cs : Circuit p) : cs.clone = cs := by
  simp [Circuit.clone, Expression.clone_eq]

/-- The optimizer proper; `optimizerWithBusFacts` runs it on a clone. The split is what gives
    `Circuit.clone_eq` a non-dependent boundary to rewrite at: `pipeline`'s result type mentions its
    input, so it cannot be rewritten under it. -/
def optimizerCore {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : Circuit p) : Circuit p × Derivations p :=
  let r := pipeline b cs bs facts
  (r.out, r.derivs.forOutput cs.vars r.out.vars)

/-- The fact-aware circuit optimizer: given proven `BusFacts` (which fixes the implicit `bs`), run
    the pipeline and return the output system with the `Derivations` for its new variables.

    `cs` stays live inside `optimizerCore` for `cs.vars`, which is what stops Lean reusing its nodes
    in place instead of cloning them. -/
def optimizerWithBusFacts {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : Circuit p) : Circuit p × Derivations p :=
  optimizerCore b facts cs.clone

/-! ## `witgen`'s two branches

So the completeness proof never unfolds the spec's `Derivations.witgen`. -/

/-- On an input variable, `witgen` passes the input assignment through. -/
theorem Derivations.witgen_powdrId {ds : Derivations p} {inputVars outputVars : List Variable}
    (h : ds.cover inputVars outputVars) (inputAssignment : Variable → ZMod p) {v : Variable}
    {w : Nat} (hv : v ∈ outputVars) (hp : v.powdrId? = some w) :
    ds.witgen h inputAssignment v hv = inputAssignment v := by
  unfold Derivations.witgen; split <;> simp_all

/-- On a derived variable, `witgen` evaluates the method `ds` records for it. -/
theorem Derivations.witgen_methodFor {ds : Derivations p} {inputVars outputVars : List Variable}
    (h : ds.cover inputVars outputVars) (inputAssignment : Variable → ZMod p) {v : Variable}
    {cm : ComputationMethod p} (hv : v ∈ outputVars) (hp : v.powdrId? = none)
    (hm : ds.methodFor v = some cm) :
    ds.witgen h inputAssignment v hv = cm.eval inputAssignment := by
  have hg : ∀ hs : (ds.methodFor v).isSome, (ds.methodFor v).get hs = cm :=
    fun hs => Option.get_of_mem hs (Option.mem_def.mpr hm)
  unfold Derivations.witgen; split <;> simp_all

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
      show (bi.eval e2).multiplicity ≠ 0 → bs.accepts (bi.eval e2)
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
  have hmap : cs.busInteractions.map (fun bi => bi.eval f)
      = cs.busInteractions.map (fun bi => bi.eval g) :=
    List.map_congr_left (fun bi hbi => Circuit.busEval_congr h hbi)
  unfold Circuit.sideEffects
  rw [hmap]

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

/-- `methodFor` is `findSomeRev?` with a keyed probe — the shape `Std.HashMap`'s `insertMany` lookup
    lemma reports, so the two agree in `getElem?_ofList`. -/
theorem Derivations.methodFor_eq_findSomeRev? (ds : Derivations p) (v : Variable) :
    ds.findSomeRev? (fun ⟨u, cm⟩ => if u == v then some cm else none) = ds.methodFor v := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
      obtain ⟨u, cm⟩ := d
      rw [List.findSomeRev?, ih, Derivations.methodFor]
      cases Derivations.methodFor rest v with
      | some later => rfl
      | none => simp

/-- Keying `ds` by variable preserves `methodFor`: `insertMany` keeps the last binding for a
    duplicated key, and so does `methodFor`. -/
theorem Derivations.getElem?_ofList (ds : Derivations p) (v : Variable) :
    (Std.HashMap.ofList ds)[v]? = ds.methodFor v := by
  rw [Std.HashMap.ofList_eq_insertMany_empty, Std.HashMap.getElem?_insertMany_list,
    Std.HashMap.getElem?_empty, Derivations.methodFor_eq_findSomeRev?]
  cases ds.methodFor v <;> rfl

theorem Derivations.safeMethodIdx_eq (ds : Derivations p) (inputVars : List Variable)
    (v : Variable) :
    Derivations.safeMethodIdx (Std.HashMap.ofList ds) (Std.HashSet.ofList inputVars) v
      = ds.safeMethod inputVars v := by
  rw [Derivations.safeMethodIdx, Derivations.safeMethod, Derivations.getElem?_ofList]
  cases ds.methodFor v with
  | none => rfl
  | some cm =>
      exact if_congr (by simp [List.all_eq_true, Std.HashSet.contains_ofList]) rfl rfl

theorem Derivations.forOutput_eq (ds : Derivations p) (inputVars outputVars : List Variable) :
    ds.forOutput inputVars outputVars
      = (outputVars.filter (fun v => v.powdrId?.isNone)).eraseDups.map
          (fun v => (v, ds.safeMethod inputVars v)) := by
  simp only [Derivations.forOutput, HashedDedup.hashedEraseDups_eq]
  exact List.map_congr_left fun v _ => by rw [Derivations.safeMethodIdx_eq]

theorem Derivations.forOutput_methodFor {ds : Derivations p} {inputVars outputVars : List Variable}
    {v : Variable} (hv : v ∈ outputVars) (hpw : v.powdrId? = none) :
    (ds.forOutput inputVars outputVars).methodFor v = some (ds.safeMethod inputVars v) := by
  rw [Derivations.forOutput_eq]
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
    valid witness) — the clauses `Optimizer.isCorrect` demands, for the circuit the pipeline is
    handed (`optimizerWithBusFacts_correct` transports this across the clone). -/
theorem optimizerCore_correct {bs : BusSemantics p} (b : DegreeBound) (facts : BusFacts p bs)
    (cs : Circuit p) :
    (optimizerCore b facts cs).1.isSoundReplacementOf cs bs ∧
      (optimizerCore b facts cs).1.isCompleteReplacementOf cs bs (optimizerCore b facts cs).2 := by
  refine ⟨(pipeline b cs bs facts).correct.toSound, ?_⟩
  intro hpow
  -- Phrase the goal in `pipeline` terms up front: the coverage proof is one of its components, so
  -- `refine` would otherwise have to bridge the `optimizerCore` projections by `whnf`.
  simp only [optimizerCore]
  -- `PassCorrect` components (`Basic.lean`): no new powdr-ID column, and real-trace completeness.
  have hS := (pipeline b cs bs facts).correct.2.2.1
  have hcomp := (pipeline b cs bs facts).correct.2.2.2
  -- Every output variable is either reused from the input or has a safe method.
  have hcover : ((pipeline b cs bs facts).derivs.forOutput cs.vars
      (pipeline b cs bs facts).out.vars).cover cs.vars (pipeline b cs bs facts).out.vars := by
    intro v hv
    cases hpw : v.powdrId? with
    | some w => exact hS v hv (by simp [hpw])
    | none =>
        exact ⟨(pipeline b cs bs facts).derivs.safeMethod cs.vars v,
          Derivations.forOutput_methodFor hv hpw,
          Derivations.safeMethod_vars _ _ _⟩
  refine ⟨?_, hcover, ?_⟩
  · -- `forOutput` records only no-ID variables occurring in the output.
    intro d hd
    rw [Derivations.forOutput_eq, List.mem_map] at hd
    obtain ⟨v, hv, rfl⟩ := hd
    exact List.mem_of_mem_filter (List.mem_eraseDups.mp hv)
  intro env hadm hsat f hf
  obtain ⟨env', hsat', hadm', hse, hA, hR⟩ := hcomp env hadm hsat
  have hrec : (pipeline b cs bs facts).out.reconstructs cs.vars
      (pipeline b cs bs facts).derivs env' := by
    have hrec0 : cs.reconstructs cs.vars [] env :=
      fun u hu hunone => absurd (hpow u hu) (by simp [hunone])
    simpa using hR cs.vars (fun v hv _ => hv) [] hrec0
  have hagree : ∀ v ∈ (pipeline b cs bs facts).out.vars, f v = env' v := by
    intro v hv
    -- Case first, rewrite second: `witgen`'s implicit `outputVars` is the pipeline output, so a
    -- goal mentioning the application makes `cases` reduce it — i.e. run the optimizer in `whnf`.
    cases hpw : v.powdrId? with
    | some w =>
        rw [hf v hv, Derivations.witgen_powdrId hcover env hv hpw]
        exact (hA v (by simp [hpw])).symm
    | none =>
        obtain ⟨cm, hm, hxpow, hxinput, heq⟩ := hrec v hv hpw
        have hsafe : (pipeline b cs bs facts).derivs.safeMethod cs.vars v = cm :=
          Derivations.safeMethod_eq hm hxinput
        have hm' := Derivations.forOutput_methodFor
          (ds := (pipeline b cs bs facts).derivs) (inputVars := cs.vars)
          (outputVars := (pipeline b cs bs facts).out.vars) hv hpw
        rw [hsafe] at hm'
        rw [hf v hv, Derivations.witgen_methodFor hcover env hv hpw hm', ← heq]
        exact ComputationMethod.eval_congr cm env env' (fun x hx => (hA x (hxpow x hx)).symm)
  exact ⟨(Circuit.satisfies_congr hagree).mpr hsat',
    (Circuit.admissible_congr hagree).mpr hadm',
    hse.trans (Circuit.sideEffects_congr hagree).symm⟩

/-- The optimizer never pushes a within-bound circuit past the zkVM's degree bound (every pass is
    degree-guarded). -/
theorem optimizerCore_respectsDegree {bs : BusSemantics p} (b : DegreeBound)
    (facts : BusFacts p bs) (cs : Circuit p)
    (h : cs.withinDegree b) :
    (optimizerCore b facts cs).1.withinDegree b :=
  pipeline_respectsDeg b cs bs facts h

/-- The fact-aware optimizer is correct: its output soundly replaces the input and completely
    replaces the input's real-trace executions (`witgen` on any admissible input trace reproduces a
    valid witness) — the clauses `Optimizer.isCorrect` demands. -/
theorem optimizerWithBusFacts_correct {bs : BusSemantics p} (b : DegreeBound)
    (facts : BusFacts p bs) (cs : Circuit p) :
    (optimizerWithBusFacts b facts cs).1.isSoundReplacementOf cs bs ∧
      (optimizerWithBusFacts b facts cs).1.isCompleteReplacementOf cs bs
        (optimizerWithBusFacts b facts cs).2 := by
  simp only [optimizerWithBusFacts, Circuit.clone_eq]
  exact optimizerCore_correct b facts cs

/-- The fact-aware optimizer never pushes a within-bound circuit past the zkVM's degree
    bound (every pass is degree-guarded). -/
theorem optimizerWithBusFacts_respectsDegree {bs : BusSemantics p} (b : DegreeBound)
    (facts : BusFacts p bs) (cs : Circuit p)
    (h : cs.withinDegree b) :
    (optimizerWithBusFacts b facts cs).1.withinDegree b := by
  simp only [optimizerWithBusFacts, Circuit.clone_eq]
  exact optimizerCore_respectsDegree b facts cs h
