import ApcOptimizer.Implementation.OptimizerPasses.Measure

set_option autoImplicit false

/-! # Dense pass results, composition, degree guard, and fixpoint

Implementation-only dense analogue of the `VerifiedPass`/`PassResult` framework: a dense pass maps
a registry + covered dense system to an extended registry, dense output, and dense derivations,
bundled with an extension proof, coverage, and a `PassCorrect` on the decoded systems. Composition
threads the registry and concatenates derivations; the degree guard and fixpoint use the dense
measures (`Measure.lean`), which equal the spec measures on the decode. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

theorem DenseComputationMethod.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r')
    {cm : DenseComputationMethod p} (hc : cm.CoveredBy r) : cm.CoveredBy r' := by
  induction cm with
  | const c => exact True.intro
  | quotientOrZero num den =>
      exact ⟨hc.1.mono h, hc.2.mono h⟩
  | ifEqZero cond thenM elseM iht ihe =>
      exact ⟨hc.1.mono h, iht hc.2.1, ihe hc.2.2⟩

theorem DenseDerivations.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r')
    {dd : DenseDerivations p} (hc : dd.CoveredBy r) : dd.CoveredBy r' :=
  fun x hx => ⟨h.valid (hc x hx).1, (hc x hx).2.mono h⟩

theorem DenseDerivations.coveredBy_append {r : VarRegistry} {a b : DenseDerivations p}
    (ha : a.CoveredBy r) (hb : b.CoveredBy r) : (a ++ b).CoveredBy r := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

/-- The result of a dense pass: extended registry, dense output and derivations, with extension,
    coverage, and `PassCorrect`-on-decode evidence (all `Prop`, erased at runtime). -/
structure DensePassResult (reg : VarRegistry) (d : DenseConstraintSystem p) (bs : BusSemantics p) where
  reg' : VarRegistry
  out : DenseConstraintSystem p
  derivs : DenseDerivations p
  ext : reg.Extends reg'
  covered : out.CoveredBy reg'
  dcovered : derivs.CoveredBy reg'
  correct : PassCorrect (reg.decodeCS d) (reg'.decodeCS out) (reg'.decodeDerivs derivs) bs

/-- A proof-carrying dense pass that may consult proven `BusFacts`. Takes the input coverage as an
    (erased) hypothesis so the framework can thread it through composition. -/
abbrev DenseVerifiedPassW (p : ℕ) :=
  (reg : VarRegistry) → (d : DenseConstraintSystem p) → d.CoveredBy reg →
    (bs : BusSemantics p) → (facts : BusFacts p bs) → DensePassResult reg d bs

def DenseVerifiedPassW.id : DenseVerifiedPassW p :=
  fun reg d hcov bs _ =>
    { reg' := reg, out := d, derivs := [], ext := VarRegistry.Extends.refl reg, covered := hcov,
      dcovered := by intro x hx; simp at hx,
      correct := PassCorrect.refl (reg.decodeCS d) bs }

/-- Sequential composition: run `f`, then `g` on its output; concatenate dense derivations (the
    `PassCorrect`s compose via registry-stability). -/
def DenseVerifiedPassW.andThen (f g : DenseVerifiedPassW p) : DenseVerifiedPassW p :=
  fun reg d hcov bs facts =>
    let r1 := f reg d hcov bs facts
    let r2 := g r1.reg' r1.out r1.covered bs facts
    { reg' := r2.reg'
      out := r2.out
      derivs := r1.derivs ++ r2.derivs
      ext := r1.ext.trans r2.ext
      covered := r2.covered
      dcovered := DenseDerivations.coveredBy_append (DenseDerivations.CoveredBy.mono r2.ext r1.dcovered) r2.dcovered
      correct := by
        have h := r1.correct.andThen r2.correct
        rwa [r2.reg'.decodeDerivs_append, r2.ext.decodeDerivs_eq r1.dcovered] }

/-- Fold a list of dense passes into one (left to right; identity on `[]`). -/
def denseChain (l : List (DenseVerifiedPassW p)) : DenseVerifiedPassW p :=
  l.foldl DenseVerifiedPassW.andThen DenseVerifiedPassW.id

/-! ## Degree guarding -/

/-- A dense pass never pushes a within-bound decoded system past the degree bound `b`. -/
def DenseRespectsDeg (b : DegreeBound) (f : DenseVerifiedPassW p) : Prop :=
  ∀ (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (bs : BusSemantics p) (facts : BusFacts p bs),
    (reg.decodeCS d).withinDegree b →
    ((f reg d hcov bs facts).reg'.decodeCS (f reg d hcov bs facts).out).withinDegree b

/-! ### The lockstep degree check

The guard's degree walk runs against the pass *input* in lockstep: an output item that *is* the
aligned input item (the same object, `withPtrEq`) is skipped without walking either tree. What each
paired position checks is `outOk || !inOk` — `true` whenever the two items are equal
(`bool_or_not_self`, which is exactly `withPtrEq`'s contract) and equal to the plain check whenever
the input side is within the bound, which the guarded pipeline maintains
(`denseWithinDegreeLK_sound`). Unpaired output items (appends, length changes) get the plain
check. -/

private theorem bool_or_not_self (b : Bool) : (b || !b) = true := by cases b <;> rfl

/-- One lockstep item check: `outOk || !inOk`, with the identity shortcut. -/
def denseDegItemLK (bnd : Nat) (cIn cOut : DenseExpr p) : Bool :=
  withPtrEq cOut cIn
    (fun _ => decide (cOut.degree ≤ bnd) || !decide (cIn.degree ≤ bnd))
    (fun h => by subst h; exact bool_or_not_self _)

private theorem denseDegItemLK_eq (bnd : Nat) (cIn cOut : DenseExpr p) :
    denseDegItemLK bnd cIn cOut
      = (decide (cOut.degree ≤ bnd) || !decide (cIn.degree ≤ bnd)) := rfl

/-- The payload degree check without the closure `List.all` allocates per interaction. -/
def denseDegExprsOk (bnd : Nat) : List (DenseExpr p) → Bool
  | [] => true
  | e :: rest => decide (e.degree ≤ bnd) && denseDegExprsOk bnd rest

private theorem denseDegExprsOk_eq (bnd : Nat) (l : List (DenseExpr p)) :
    denseDegExprsOk bnd l = l.all (fun e => decide (e.degree ≤ bnd)) := by
  induction l with
  | nil => rfl
  | cons e rest ih => rw [denseDegExprsOk, ih, List.all_cons]

/-- One lockstep interaction check (multiplicity and payload together); see `denseDegItemLK`. -/
def denseDegBiLK (bnd : Nat) (bIn bOut : BusInteraction (DenseExpr p)) : Bool :=
  withPtrEq bOut bIn
    (fun _ =>
      (decide (bOut.multiplicity.degree ≤ bnd) && denseDegExprsOk bnd bOut.payload)
        || !(decide (bIn.multiplicity.degree ≤ bnd) && denseDegExprsOk bnd bIn.payload))
    (fun h => by subst h; exact bool_or_not_self _)

private theorem denseDegBiLK_eq (bnd : Nat) (bIn bOut : BusInteraction (DenseExpr p)) :
    denseDegBiLK bnd bIn bOut
      = ((decide (bOut.multiplicity.degree ≤ bnd)
            && bOut.payload.all (fun e => decide (e.degree ≤ bnd)))
          || !(decide (bIn.multiplicity.degree ≤ bnd)
            && bIn.payload.all (fun e => decide (e.degree ≤ bnd)))) := by
  show ((decide (bOut.multiplicity.degree ≤ bnd) && denseDegExprsOk bnd bOut.payload)
      || !(decide (bIn.multiplicity.degree ≤ bnd) && denseDegExprsOk bnd bIn.payload)) = _
  rw [denseDegExprsOk_eq, denseDegExprsOk_eq]

def denseDegItemsLK (bnd : Nat) : List (DenseExpr p) → List (DenseExpr p) → Bool
  | cIn :: din, cOut :: dout => denseDegItemLK bnd cIn cOut && denseDegItemsLK bnd din dout
  | _, dout => dout.all (fun c => decide (c.degree ≤ bnd))

def denseDegBisLK (bnd : Nat) :
    List (BusInteraction (DenseExpr p)) → List (BusInteraction (DenseExpr p)) → Bool
  | bIn :: din, bOut :: dout => denseDegBiLK bnd bIn bOut && denseDegBisLK bnd din dout
  | _, dout =>
      dout.all (fun bi => decide (bi.multiplicity.degree ≤ bnd)
        && bi.payload.all (fun e => decide (e.degree ≤ bnd)))

private theorem denseDegItemsLK_self (bnd : Nat) (l : List (DenseExpr p)) :
    denseDegItemsLK bnd l l = true := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
      show (denseDegItemLK bnd c c && denseDegItemsLK bnd rest rest) = true
      rw [denseDegItemLK_eq, bool_or_not_self, ih, Bool.and_self]

private theorem denseDegBisLK_self (bnd : Nat) (l : List (BusInteraction (DenseExpr p))) :
    denseDegBisLK bnd l l = true := by
  induction l with
  | nil => rfl
  | cons bi rest ih =>
      show (denseDegBiLK bnd bi bi && denseDegBisLK bnd rest rest) = true
      rw [denseDegBiLK_eq, bool_or_not_self, ih, Bool.and_self]

/-- `denseDegItemsLK` with a remaining-list identity shortcut at every step: a shared tail is
    retired by one pointer compare (`denseDegItemsLK_self` is `withPtrEq`'s obligation there).
    The `Subtype` carries the walk's own specification so that obligation can be discharged while
    the recursion is elaborated; its only runtime field is the `Bool`. -/
def denseDegItemsFast (bnd : Nat) : (din dout : List (DenseExpr p)) →
    { r : Bool // r = denseDegItemsLK bnd din dout }
  | cIn :: din, cOut :: dout =>
      have hval : (denseDegItemLK bnd cIn cOut && (denseDegItemsFast bnd din dout).1)
          = denseDegItemsLK bnd (cIn :: din) (cOut :: dout) := by
        rw [(denseDegItemsFast bnd din dout).2]; rfl
      ⟨withPtrEq (cOut :: dout) (cIn :: din)
        (fun _ => denseDegItemLK bnd cIn cOut && (denseDegItemsFast bnd din dout).1)
        (fun h => by
          rw [hval, show cIn :: din = cOut :: dout from h.symm]
          exact denseDegItemsLK_self bnd _),
       hval⟩
  | din, dout => ⟨denseDegItemsLK bnd din dout, rfl⟩

/-- `denseDegItemsFast` for the interaction lists. -/
def denseDegBisFast (bnd : Nat) : (din dout : List (BusInteraction (DenseExpr p))) →
    { r : Bool // r = denseDegBisLK bnd din dout }
  | bIn :: din, bOut :: dout =>
      have hval : (denseDegBiLK bnd bIn bOut && (denseDegBisFast bnd din dout).1)
          = denseDegBisLK bnd (bIn :: din) (bOut :: dout) := by
        rw [(denseDegBisFast bnd din dout).2]; rfl
      ⟨withPtrEq (bOut :: dout) (bIn :: din)
        (fun _ => denseDegBiLK bnd bIn bOut && (denseDegBisFast bnd din dout).1)
        (fun h => by
          rw [hval, show bIn :: din = bOut :: dout from h.symm]
          exact denseDegBisLK_self bnd _),
       hval⟩
  | din, dout => ⟨denseDegBisLK bnd din dout, rfl⟩

private theorem denseDegItemsLK_sound (bnd : Nat) (din dout : List (DenseExpr p))
    (hin : din.all (fun c => decide (c.degree ≤ bnd)) = true)
    (h : denseDegItemsLK bnd din dout = true) :
    dout.all (fun c => decide (c.degree ≤ bnd)) = true := by
  induction dout generalizing din with
  | nil => rfl
  | cons c rest ih =>
      cases din with
      | nil => exact h
      | cons i irest =>
          rw [List.all_cons, Bool.and_eq_true] at hin
          have h' : (denseDegItemLK bnd i c && denseDegItemsLK bnd irest rest) = true := h
          rw [Bool.and_eq_true, denseDegItemLK_eq] at h'
          rw [List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih irest hin.2 h'.2⟩
          have hc := h'.1
          rw [hin.1] at hc
          simpa using hc

private theorem denseDegBisLK_sound (bnd : Nat) (din dout : List (BusInteraction (DenseExpr p)))
    (hin : din.all (fun bi => decide (bi.multiplicity.degree ≤ bnd)
        && bi.payload.all (fun e => decide (e.degree ≤ bnd))) = true)
    (h : denseDegBisLK bnd din dout = true) :
    dout.all (fun bi => decide (bi.multiplicity.degree ≤ bnd)
      && bi.payload.all (fun e => decide (e.degree ≤ bnd))) = true := by
  induction dout generalizing din with
  | nil => rfl
  | cons bi rest ih =>
      cases din with
      | nil => exact h
      | cons i irest =>
          rw [List.all_cons, Bool.and_eq_true] at hin
          have h' : (denseDegBiLK bnd i bi && denseDegBisLK bnd irest rest) = true := h
          rw [Bool.and_eq_true, denseDegBiLK_eq] at h'
          rw [List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih irest hin.2 h'.2⟩
          have hc := h'.1
          rw [hin.1] at hc
          simpa using hc

/-- The guard's degree check: the lockstep walks with a whole-system identity shortcut. On a
    within-bound input this decides exactly `dOut.withinDegreeB b`
    (`denseWithinDegreeLK_sound` / `denseWithinDegreeLK_complete`). -/
def denseWithinDegreeLK (dIn dOut : DenseConstraintSystem p) (b : DegreeBound) : Bool :=
  withPtrEq dOut dIn
    (fun _ =>
      (denseDegItemsFast b.identities dIn.algebraicConstraints dOut.algebraicConstraints).1
        && (denseDegBisFast b.busInteractions dIn.busInteractions dOut.busInteractions).1)
    (fun h => by
      subst h
      rw [(denseDegItemsFast ..).2, (denseDegBisFast ..).2,
        denseDegItemsLK_self, denseDegBisLK_self, Bool.and_self])

private theorem denseWithinDegreeLK_def (dIn dOut : DenseConstraintSystem p) (b : DegreeBound) :
    denseWithinDegreeLK dIn dOut b
      = (denseDegItemsLK b.identities dIn.algebraicConstraints dOut.algebraicConstraints
          && denseDegBisLK b.busInteractions dIn.busInteractions dOut.busInteractions) := by
  show ((denseDegItemsFast b.identities dIn.algebraicConstraints dOut.algebraicConstraints).1
      && (denseDegBisFast b.busInteractions dIn.busInteractions dOut.busInteractions).1) = _
  rw [(denseDegItemsFast ..).2, (denseDegBisFast ..).2]

/-- A `true` lockstep verdict on a within-bound input puts the output within the bound. -/
private theorem denseWithinDegreeLK_sound (dIn dOut : DenseConstraintSystem p) (b : DegreeBound)
    (hin : dIn.withinDegreeB b = true) (h : denseWithinDegreeLK dIn dOut b = true) :
    dOut.withinDegreeB b = true := by
  rw [denseWithinDegreeLK_def, Bool.and_eq_true] at h
  rw [DenseConstraintSystem.withinDegreeB, Bool.and_eq_true] at hin
  rw [DenseConstraintSystem.withinDegreeB, Bool.and_eq_true]
  exact ⟨denseDegItemsLK_sound _ _ _ hin.1 h.1, denseDegBisLK_sound _ _ _ hin.2 h.2⟩

attribute [irreducible] denseWithinDegreeLK

/-- Degree guard on the dense system (no decode): if the output would exceed `b`, keep the input.
    The check runs in lockstep with the input (`denseWithinDegreeLK`), so an unchanged output —
    whole-system or item-wise — skips the degree walk; per item it tests `outOk || !inOk`, which
    never rejects a within-bound output (`outOk` alone suffices) and, on the within-bound inputs
    the guarded pipeline maintains, accepts exactly the within-bound outputs
    (`denseWithinDegreeLK_sound`, used by `guardDegree_respectsDeg`). -/
def DenseVerifiedPassW.guardDegree (b : DegreeBound) (f : DenseVerifiedPassW p) :
    DenseVerifiedPassW p :=
  fun reg d hcov bs facts =>
    let r := f reg d hcov bs facts
    if denseWithinDegreeLK d r.out b then r
    else { reg' := reg, out := d, derivs := [], ext := VarRegistry.Extends.refl reg,
           covered := hcov, dcovered := by intro x hx; simp at hx,
           correct := PassCorrect.refl (reg.decodeCS d) bs }

theorem DenseVerifiedPassW.guardDegree_respectsDeg {b : DegreeBound} (f : DenseVerifiedPassW p) :
    DenseRespectsDeg b (f.guardDegree b) := by
  intro reg d hcov bs facts hin
  have hdIn : d.withinDegreeB b = true := by
    rw [← reg.decodeCS_withinDegreeB]
    exact (Circuit.withinDegreeB_iff _ _).2 hin
  simp only [DenseVerifiedPassW.guardDegree]
  by_cases hok : denseWithinDegreeLK d (f reg d hcov bs facts).out b = true
  · rw [if_pos hok]
    refine (Circuit.withinDegreeB_iff _ _).1 ?_
    rw [(f reg d hcov bs facts).reg'.decodeCS_withinDegreeB]
    exact denseWithinDegreeLK_sound d _ b hdIn hok
  · rw [if_neg hok]
    exact hin

theorem DenseVerifiedPassW.andThen_respectsDeg {b : DegreeBound} {f g : DenseVerifiedPassW p}
    (hf : DenseRespectsDeg b f) (hg : DenseRespectsDeg b g) : DenseRespectsDeg b (f.andThen g) := by
  intro reg d hcov bs facts hin
  exact hg _ _ _ bs facts (hf reg d hcov bs facts hin)

theorem denseChain_respectsDeg {b : DegreeBound} {l : List (DenseVerifiedPassW p)}
    (h : ∀ f ∈ l, DenseRespectsDeg b f) : DenseRespectsDeg b (denseChain l) := by
  unfold denseChain
  suffices H : ∀ (l : List (DenseVerifiedPassW p)) (init : DenseVerifiedPassW p),
      DenseRespectsDeg b init → (∀ f ∈ l, DenseRespectsDeg b f) →
      DenseRespectsDeg b (l.foldl DenseVerifiedPassW.andThen init) by
    exact H l DenseVerifiedPassW.id (fun _ _ _ _ _ h => h) h
  intro l
  induction l with
  | nil => intro init hinit _; simpa using hinit
  | cons g rest ih =>
      intro init hinit hall
      rw [List.foldl_cons]
      exact ih (init.andThen g)
        (DenseVerifiedPassW.andThen_respectsDeg hinit (hall g (List.mem_cons_self ..)))
        (fun f hf => hall f (List.mem_cons_of_mem _ hf))

/-! ## Dense fixpoint

The dense size key is well-founded, so iterating to a fixpoint terminates with no budget. Because
it equals the spec size key on the decode, the stopping decision matches the spec loop's. -/

theorem denseSizeKey_wf :
    WellFounded (fun a b : DenseConstraintSystem p => a.sizeKey < b.sizeKey) :=
  InvImage.wf DenseConstraintSystem.sizeKey wellFounded_lt

/-- The dense fixpoint worker. `_hk` threads in the input's already-computed size key so each cycle
    only recomputes the output's. Correct by construction. -/
def denseIterateToFixpointFrom (f : DenseVerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) (k : Nat ×ₗ Nat ×ₗ Nat) (_hk : d.sizeKey = k) :
    DensePassResult reg d bs :=
  let r := f reg d hcov bs facts
  let k' := r.out.sizeKey
  if h : k' < k then
    let r2 := denseIterateToFixpointFrom f r.reg' r.out r.covered bs facts k' rfl
    { reg' := r2.reg'
      out := r2.out
      derivs := r.derivs ++ r2.derivs
      ext := r.ext.trans r2.ext
      covered := r2.covered
      dcovered := DenseDerivations.coveredBy_append (DenseDerivations.CoveredBy.mono r2.ext r.dcovered) r2.dcovered
      correct := by
        have hc := r.correct.andThen r2.correct
        rwa [r2.reg'.decodeDerivs_append, r2.ext.decodeDerivs_eq r.dcovered] }
  else
    { reg' := reg, out := d, derivs := [], ext := VarRegistry.Extends.refl reg, covered := hcov,
      dcovered := by intro x hx; simp at hx,
      correct := PassCorrect.refl (reg.decodeCS d) bs }
  termination_by d.sizeKey
  decreasing_by rw [_hk]; exact h

/-- Iterate a dense pass to a fixpoint on the dense size key; correct by construction. -/
def denseIterateToFixpoint (f : DenseVerifiedPassW p) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) (bs : BusSemantics p)
    (facts : BusFacts p bs) : DensePassResult reg d bs :=
  denseIterateToFixpointFrom f reg d hcov bs facts d.sizeKey rfl

/-- `denseIterateToFixpointFrom` preserves the degree bound (strong induction on the `sizeKey`
    measure, registry and threaded key generalized). -/
theorem denseIterateToFixpointFrom_respectsDeg {b : DegreeBound} {f : DenseVerifiedPassW p}
    (hf : DenseRespectsDeg b f) (reg : VarRegistry) (d : DenseConstraintSystem p) :
    ∀ (hcov : d.CoveredBy reg) (bs : BusSemantics p) (facts : BusFacts p bs)
      (k : Nat ×ₗ Nat ×ₗ Nat) (hk : d.sizeKey = k),
      (reg.decodeCS d).withinDegree b →
      ((denseIterateToFixpointFrom f reg d hcov bs facts k hk).reg'.decodeCS
        (denseIterateToFixpointFrom f reg d hcov bs facts k hk).out).withinDegree b := by
  induction d using denseSizeKey_wf.induction generalizing reg with
  | _ d ih =>
    intro hcov bs facts k hk hin
    rw [denseIterateToFixpointFrom]
    split
    · rename_i h
      exact ih _ (by rw [hk]; exact h) _ (f reg d hcov bs facts).covered bs facts _ rfl
        (hf reg d hcov bs facts hin)
    · exact hin

theorem denseIterateToFixpoint_respectsDeg {b : DegreeBound} {f : DenseVerifiedPassW p}
    (hf : DenseRespectsDeg b f) : DenseRespectsDeg b (denseIterateToFixpoint f) := by
  intro reg d hcov bs facts hin
  exact denseIterateToFixpointFrom_respectsDeg hf reg d hcov bs facts d.sizeKey rfl hin

end ApcOptimizer.Dense
