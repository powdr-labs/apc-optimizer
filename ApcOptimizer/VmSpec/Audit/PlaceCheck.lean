import ApcOptimizer.VmSpec.Audit.BridgeCheck

set_option autoImplicit false

/-! **A static check for `StepLayout`'s placement and ordering.**

    `StepLayout.tOffset` maps each interaction to an integer offset from the step's `tStart`, and it
    depends on the assignment: a memory *receive* names the record an earlier instruction left, so
    its offset is `k - n` where `n` is whatever distance the lt gadget's range checks allow. A
    checker is a `Bool` on the circuit alone, so it cannot name `place`.

    What it names instead is a **recipe** per interaction: how to *compute* the offset from an
    assignment, and — read off the same constructor, so the two cannot disagree — the interval that
    computation stays inside. `placed` then follows from the interval lying in the step's window,
    and `ordered` from two intervals not overlapping.

    The `lookback` case is where a VM's own gadget enters: this file checks everything except the
    bound `n < maxLookback`, which it takes as a hypothesis for the caller's recognizer to
    discharge. -/

variable {p : ℕ}

--------- Recipes ---------

/-- How to compute one interaction's offset from an assignment. -/
inductive Recipe (p : ℕ) where
  /-- A fixed tick of the step. Every *send*, and the bridge receive. -/
  | fixed (k : ℤ)
  /-- A reach back from tick `k` by `loE + radix * hiE`, the two limbs a lt gadget range-checks.
      Every memory *receive*. -/
  | lookback (k : ℤ) (radix : ℕ) (loE hiE : Expression p)

/-- The offset a recipe computes. -/
def Recipe.place (asg : ChipAssignment p) : Recipe p → ℤ
  | .fixed k => k
  | .lookback k radix loE hiE =>
    k - (((loE.eval asg).val + radix * (hiE.eval asg).val : ℕ) : ℤ)

/-- How far back a recipe reaches. Zero for a fixed tick. -/
def Recipe.back (asg : ChipAssignment p) : Recipe p → ℕ
  | .fixed _ => 0
  | .lookback _ radix loE hiE => (loE.eval asg).val + radix * (hiE.eval asg).val

/-- The largest offset a recipe can compute. -/
def Recipe.ub : Recipe p → ℤ
  | .fixed k => k
  | .lookback k _ _ _ => k

/-- The smallest, given the lookback bound. The `+ 1` is the gadget's `n < maxLookback` — and a
    real APC sits exactly on it, its first read being at `-1 - n`. -/
def Recipe.lb (maxLookback : ℕ) : Recipe p → ℤ
  | .fixed k => k
  | .lookback k _ _ _ => k - (maxLookback : ℤ) + 1

/-- Whether every offset a recipe can compute lies in the step's window `[-maxLookback, d]`. -/
def Recipe.fits (maxLookback d : ℕ) (rc : Recipe p) : Bool :=
  decide (-(maxLookback : ℤ) ≤ rc.lb maxLookback ∧ rc.ub ≤ (d : ℤ))

/-- Whether one recipe's offsets all lie strictly below another's. -/
def Recipe.below (maxLookback : ℕ) (a b : Recipe p) : Bool :=
  decide (a.ub < b.lb maxLookback)

theorem Recipe.place_mem {asg : ChipAssignment p} {maxLookback : ℕ} (rc : Recipe p)
    (hback : rc.back asg < maxLookback) :
    rc.lb maxLookback ≤ rc.place asg ∧ rc.place asg ≤ rc.ub := by
  cases rc with
  | fixed k => exact ⟨le_refl _, le_refl _⟩
  | lookback k radix loE hiE =>
    simp only [Recipe.lb, Recipe.ub, Recipe.place, Recipe.back] at *
    omega

/-- The offset a recipe computes, spelled as `k` minus its reach. -/
theorem Recipe.place_eq {asg : ChipAssignment p} (rc : Recipe p) :
    rc.place asg = rc.ub - (rc.back asg : ℤ) := by
  cases rc <;> simp [Recipe.place, Recipe.ub, Recipe.back]

--------- Where a bus keeps its timestamp ---------

/-- Which payload position carries the timestamp, per bus. -/
abbrev TimestampPos := Nat → Option ℕ

/-- The rules read the timestamp off that position. For OpenVM: index `6` on the memory bus,
    index `1` on the execution bridge. -/
def ReadsTimestampAt (r : GuestBusRules p) (tsPos : TimestampPos) : Prop :=
  ∀ m : BusMessage p, ∀ j, tsPos m.1 = some j → r.getTimestamp m = m.2.getD j 0

--------- The check ---------

/-- Whether a multiplicity expression folds to the literal `0` — the interaction never happens,
    whatever the assignment. A fused APC has these: an operand slot the block does not use pins its
    address space to `0`, and the memory access it would have made is dead. -/
def multIsZero (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => v == 0
  | none => false

/-- Check one interaction against its recipe. A `fixed k` is decided here — the timestamp form must
    be the base form shifted by `k`. A `lookback` is not: its content is the gadget bound, which
    this file takes as a hypothesis. A dead interaction is asked nothing. -/
def placeCheckOne (vs : List Variable) (rules : List (PinRule p)) (isStateful : Nat → Bool)
    (tsPos : TimestampPos) (baseF : LinForm p) (bi : BusInteraction (Expression p))
    (rc : Recipe p) : Bool :=
  if isStateful bi.busId then
    multIsZero rules bi ||
    match tsPos bi.busId with
    | none => false
    | some j =>
      -- Only the timestamp field is normalized. Normalizing the whole payload would reject a
      -- record this clause never reads into — a load's *address* can be non-linear (a byte load's
      -- pointer is quadratic in its selector flags) while its timestamp is not.
      match bi.payload[j]? with
      | none => false
      | some e =>
        match Expression.toLin vs rules e with
        | none => false
        | some f =>
          match rc with
          | .fixed k => linShiftedBy baseF f ((k : ℤ) : ZMod p)
          | .lookback _ _ _ _ => true
  else true

/-- Check every interaction against its recipe, pairwise down the two lists. -/
def placeCheckAll (vs : List Variable) (rules : List (PinRule p)) (isStateful : Nat → Bool)
    (tsPos : TimestampPos) (baseF : LinForm p) :
    List (BusInteraction (Expression p)) → List (Recipe p) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | bi :: bt, rc :: rt =>
    placeCheckOne vs rules isStateful tsPos baseF bi rc
      && placeCheckAll vs rules isStateful tsPos baseF bt rt

theorem placeCheckAll_get {vs : List Variable} {rules : List (PinRule p)}
    {isStateful : Nat → Bool} {tsPos : TimestampPos} {baseF : LinForm p} :
    ∀ {L : List (BusInteraction (Expression p))} {R : List (Recipe p)},
      placeCheckAll vs rules isStateful tsPos baseF L R = true →
      ∀ i : Fin L.length,
        placeCheckOne vs rules isStateful tsPos baseF (L.get i) (R.getD i.val (.fixed 0)) = true := by
  intro L
  induction L with
  | nil => intro R _ i; exact absurd i.isLt (by simp)
  | cons bi bt ih =>
    intro R h i
    match R with
    | [] => simp only [placeCheckAll] at h; cases h
    | rc :: rt =>
      simp only [placeCheckAll, Bool.and_eq_true] at h
      match i with
      | ⟨0, _⟩ => exact h.1
      | ⟨j + 1, hj⟩ => exact ih h.2 ⟨j, by simpa using hj⟩

/-- **Soundness of the placement check.** A `fixed` recipe's offset is where its interaction's
    timestamp sits; a `lookback` recipe's is too, given the caller's gadget fact. -/
theorem placeCheckOne_sound {vs : List Variable} {rules : List (PinRule p)}
    {isStateful : Nat → Bool} {tsPos : TimestampPos} {baseE : Expression p} {baseF : LinForm p}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hbase : Expression.toLin vs rules baseE = some baseF)
    {bi : BusInteraction (Expression p)} {rc : Recipe p}
    (h : placeCheckOne vs rules isStateful tsPos baseF bi rc = true)
    (hst : isStateful bi.busId = true) (hact : (bi.eval asg).multiplicity ≠ 0)
    {r : GuestBusRules p} (hts : ReadsTimestampAt r tsPos)
    (hlook : ∀ (k : ℤ) (radix : ℕ) (loE hiE : Expression p), rc = .lookback k radix loE hiE →
      r.getTimestamp ((bi.eval asg).busId, (bi.eval asg).payload)
        = baseE.eval asg + ((rc.place asg : ℤ) : ZMod p)) :
    r.getTimestamp ((bi.eval asg).busId, (bi.eval asg).payload)
      = baseE.eval asg + ((rc.place asg : ℤ) : ZMod p) := by
  cases hrc : rc with
  | lookback k radix loE hiE => exact hrc ▸ hlook k radix loE hiE hrc
  | fixed k =>
    subst hrc
    simp only [placeCheckOne, hst, if_pos, Bool.or_eq_true] at h
    rcases h with h | h
    · exfalso
      simp only [multIsZero] at h
      cases hm : bi.multiplicity.foldConstWith rules with
      | none => rw [hm] at h; cases h
      | some v =>
        rw [hm] at h
        simp only [beq_iff_eq] at h
        exact hact ((Expression.foldConstWith_eq hrules hm).trans h)
    cases hj : tsPos bi.busId with
    | none => rw [hj] at h; cases h
    | some j =>
      rw [hj] at h
      dsimp only at h
      cases he : bi.payload[j]? with
      | none => rw [he] at h; cases h
      | some e =>
        rw [he] at h
        dsimp only at h
        cases hf : Expression.toLin vs rules e with
        | none => rw [hf] at h; cases h
        | some f =>
          rw [hf] at h
          have hbus : (bi.eval asg).busId = bi.busId := rfl
          rw [hts _ j (by rw [hbus]; exact hj)]
          have : ((bi.eval asg).payload).getD j 0 = f.eval vs asg := by
            show ((bi.payload.map (fun g => g.eval asg)).getD j 0) = f.eval vs asg
            rw [List.getD_eq_getElem?_getD, List.getElem?_map, he]
            exact Expression.toLin_eval hrules hf
          rw [this, eval_of_linShiftedBy h, Expression.toLin_eval hrules hbase]
          simp [Recipe.place]

--------- The two clauses ---------

theorem recipe_placed {maxLookback d : ℕ} {rc : Recipe p} {asg : ChipAssignment p}
    (hf : rc.fits maxLookback d = true) (hbk : rc.back asg < maxLookback) :
    -(maxLookback : ℤ) ≤ rc.place asg ∧ rc.place asg ≤ (d : ℤ) := by
  obtain ⟨hlo, hhi⟩ := rc.place_mem hbk
  have hd := of_decide_eq_true hf
  exact ⟨le_trans hd.1 hlo, le_trans hhi hd.2⟩

theorem recipe_ordered {maxLookback : ℕ} {a b : Recipe p} {asg : ChipAssignment p}
    (hb : Recipe.below maxLookback a b = true)
    (ha : a.back asg < maxLookback) (hbk : b.back asg < maxLookback) :
    a.place asg < b.place asg :=
  lt_of_le_of_lt (a.place_mem ha).2 (lt_of_lt_of_le (of_decide_eq_true hb) (b.place_mem hbk).1)

/-- **`StepLayout.tOffsetMatch`, from the recipes.** -/
theorem placeCheck_placed {vs : List Variable} {rules : List (PinRule p)}
    {isStateful : Nat → Bool} {tsPos : TimestampPos} {baseE : Expression p} {baseF : LinForm p}
    {asg : ChipAssignment p} {maxLookback d : ℕ} {r : GuestBusRules p} {c : Circuit p}
    {R : List (Recipe p)}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hbase : Expression.toLin vs rules baseE = some baseF)
    (hts : ReadsTimestampAt r tsPos) (hstEq : r.isStateful = isStateful)
    (hall : placeCheckAll vs rules isStateful tsPos baseF c.busInteractions R = true)
    (i : Fin c.busInteractions.length) (hi : c.activeStateful r asg i)
    (hf : (R.getD i.val (.fixed 0)).fits maxLookback d = true)
    (hbk : (R.getD i.val (.fixed 0)).back asg < maxLookback)
    (hlook : ∀ (k : ℤ) (radix : ℕ) (loE hiE : Expression p),
      R.getD i.val (.fixed 0) = .lookback k radix loE hiE →
        r.getTimestamp (c.msgAt asg i)
          = baseE.eval asg + (((R.getD i.val (.fixed 0)).place asg : ℤ) : ZMod p)) :
    -(maxLookback : ℤ) ≤ (R.getD i.val (.fixed 0)).place asg ∧
      (R.getD i.val (.fixed 0)).place asg ≤ (d : ℤ) ∧
      r.getTimestamp (c.msgAt asg i)
        = baseE.eval asg + (((R.getD i.val (.fixed 0)).place asg : ℤ) : ZMod p) := by
  obtain ⟨hlo, hhi⟩ := recipe_placed (d := d) hf hbk
  refine ⟨hlo, hhi, ?_⟩
  exact placeCheckOne_sound hrules hbase (placeCheckAll_get hall i)
    (by rw [← hstEq]; exact hi.1) hi.2 hts hlook

--------- The memory ordering ---------

/-- Whether a multiplicity expression folds to something other than `1`. -/
def multNotOne (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => !(v == 1)
  | none => false

/-- Whether it folds to something other than `0`. -/
def multNotZero (rules : List (PinRule p)) (bi : BusInteraction (Expression p)) : Bool :=
  match bi.multiplicity.foldConstWith rules with
  | some v => !(v == 0)
  | none => false

/-- One ordered pair `j < i` of the interaction list. Nothing is asked unless both sit on the
    memory bus and `i` cannot be ruled out as a *send*; then `j`'s recipe must place strictly below
    `i`'s, whatever the assignment. -/
def memOrderPairOk (rules : List (PinRule p)) (memBusId maxLookback : ℕ)
    (L : List (BusInteraction (Expression p))) (R : List (Recipe p)) (j i : ℕ) : Bool :=
  match L[j]?, L[i]? with
  | some bj, some bi =>
    !(bj.busId == memBusId) || !(bi.busId == memBusId) || multNotOne rules bi ||
      Recipe.below maxLookback (R.getD j (.fixed 0)) (R.getD i (.fixed 0))
  | _, _ => true

/-- **The ordering `StepLayout.memSendsOk` inducts along, decided.** `memSendsOk` hands a memory
    send every *earlier in time* memory interaction; `byteCheck_sendsOk` wants every *earlier in
    the list* one. This closes that gap for a whole circuit at once: it is `Recipe.below` over
    every pair, skipped wherever the recipes cannot both be memory or `i` cannot be a send. -/
def memOrderCheck (rules : List (PinRule p)) (memBusId maxLookback : ℕ)
    (L : List (BusInteraction (Expression p))) (R : List (Recipe p)) : Bool :=
  (List.range L.length).all fun i =>
    (List.range i).all fun j => memOrderPairOk rules memBusId maxLookback L R j i

theorem memOrderCheck_get {rules : List (PinRule p)} {memBusId maxLookback : ℕ}
    {L : List (BusInteraction (Expression p))} {R : List (Recipe p)}
    (h : memOrderCheck rules memBusId maxLookback L R = true)
    {i : ℕ} (hi : i < L.length) {j : ℕ} (hj : j < i) :
    memOrderPairOk rules memBusId maxLookback L R j i = true :=
  List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)

/-- **Soundness of the ordering check.** A `true` turns index order into offset order for the one
    pair the byte induction needs it for. -/
theorem memOrderCheck_sound {rules : List (PinRule p)} {memBusId maxLookback : ℕ}
    {L : List (BusInteraction (Expression p))} {R : List (Recipe p)}
    (h : memOrderCheck rules memBusId maxLookback L R = true)
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {i j : Fin L.length} (hji : j.val < i.val)
    (hmj : (L.get j).busId = memBusId) (hmi : (L.get i).busId = memBusId)
    (hsend : ((L.get i).eval asg).multiplicity = 1)
    (hbj : (R.getD j.val (.fixed 0)).back asg < maxLookback)
    (hbi : (R.getD i.val (.fixed 0)).back asg < maxLookback) :
    (R.getD j.val (.fixed 0)).place asg < (R.getD i.val (.fixed 0)).place asg := by
  have hp := memOrderCheck_get h i.isLt hji
  rw [memOrderPairOk, List.getElem?_eq_getElem j.isLt, List.getElem?_eq_getElem i.isLt] at hp
  simp only [List.get_eq_getElem] at hmj hmi hsend
  simp only [hmj, hmi, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hp
  rcases hp with hp | hp
  · exfalso
    simp only [multNotOne] at hp
    cases hm : (L[i.val]).multiplicity.foldConstWith rules with
    | none => rw [hm] at hp; cases hp
    | some v =>
      rw [hm] at hp
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hp
      exact hp ((Expression.foldConstWith_eq hrules hm).symm.trans hsend)
  · exact recipe_ordered hp hbj hbi

--------- The lt gadget's arithmetic ---------

/-- Payload component `j` of a circuit's `i`th interaction, as an expression. Naming a gadget's
    limbs this way rather than transcribing them is what lets the identity check below be about the
    circuit powdr emitted, rather than about a shape restated by hand. -/
def payloadOf (c : Circuit p) (i j : ℕ) : Expression p :=
  ((c.busInteractions.getD i ⟨0, .const 0, []⟩).payload).getD j (.const 0)

/-- Whether `hiE` is the high limb of a lt gadget that places a timestamp `tsE` at `base + k - n`:
    the gadget writes `n` as `lo + radix * hi`, and its range-check payload is
    `coef * (ts + lo - base - k)`. A linear identity, so `LinForm` decides it.

    What this does *not* check is that the two limbs are range-checked at all — that is a lookup,
    not arithmetic, and the caller supplies it. -/
def gadgetIdentity (vs : List Variable) (rules : List (PinRule p)) (coef : ZMod p)
    (baseF : LinForm p) (k : ℤ) (tsE loE hiE : Expression p) : Bool :=
  match Expression.toLin vs rules tsE, Expression.toLin vs rules loE,
      Expression.toLin vs rules hiE with
  | some ft, some fl, some fh =>
    fh == LinForm.smul coef (LinForm.add (LinForm.add ft fl)
      (LinForm.smul (-1) (LinForm.add baseF (LinForm.constF vs.length ((k : ℤ) : ZMod p)))))
  | _, _, _ => false

theorem gadgetIdentity_sound {vs : List Variable} {rules : List (PinRule p)} {coef : ZMod p}
    {baseE : Expression p} {baseF : LinForm p} {k : ℤ} {tsE loE hiE : Expression p}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hbase : Expression.toLin vs rules baseE = some baseF)
    (h : gadgetIdentity vs rules coef baseF k tsE loE hiE = true) :
    hiE.eval asg
      = coef * (tsE.eval asg + loE.eval asg - baseE.eval asg - ((k : ℤ) : ZMod p)) := by
  simp only [gadgetIdentity] at h
  cases ht : Expression.toLin vs rules tsE with
  | none => rw [ht] at h; cases h
  | some ft =>
    cases hl : Expression.toLin vs rules loE with
    | none => rw [ht, hl] at h; cases h
    | some fl =>
      cases hh : Expression.toLin vs rules hiE with
      | none => rw [ht, hl, hh] at h; cases h
      | some fh =>
        rw [ht, hl, hh] at h
        simp only [beq_iff_eq] at h
        have hszt := Expression.toLin_sized ht
        have hszl := Expression.toLin_sized hl
        have hszb := Expression.toLin_sized hbase
        rw [Expression.toLin_eval hrules hh, h,
          LinForm.eval_smul, LinForm.eval_add vs _ _ asg
            (LinForm.sized_add hszt hszl)
            (LinForm.sized_smul (LinForm.sized_add hszb (LinForm.sized_constF _ _))),
          LinForm.eval_add vs ft fl asg hszt hszl,
          LinForm.eval_smul, LinForm.eval_add vs _ _ asg hszb (LinForm.sized_constF _ _),
          LinForm.eval_constF, ← Expression.toLin_eval hrules ht,
          ← Expression.toLin_eval hrules hl, ← Expression.toLin_eval hrules hbase]
        ring
