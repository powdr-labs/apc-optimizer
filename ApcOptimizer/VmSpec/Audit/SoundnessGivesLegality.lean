import ApcOptimizer.VmSpec.OpenVm
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! **How much of `Circuit.legalGuest` a chip-level soundness proof already gives — and what is
    left over.**

    `openVm_vmSoundReplacement` assumes legality of the guest chips (`hLegal`, `hPreserve`) on top
    of the per-chip `Circuit.isSoundReplacementOf` an optimizer pass proves. This file says exactly
    how much of that assumption is redundant.

    The redundant part is *not* zero, and it is not visible from `Spec.lean` alone: it comes from
    OpenVM's `maintainsInvariants` (`OpenVmSemantics.lean`), which pins a message's multiplicity
    (`= 1` on every lookup bus, `= ±1` on the execution bridge and memory) and, on memory, carries
    exactly `openVmPayloadOk`. `Circuit.isSoundReplacementOf`'s second conjunct transports
    `Circuit.guaranteesInvariants` from the original chip to the optimized one, so all three of
    `Circuit.legalGuest`'s bus-shape clauses come for free — *on assignments the semantics
    accepts*. That is `Circuit.legalOnAccepted`, and
    `legalOnAccepted_of_isSoundReplacementOf` is the transport.

    The residue is the quantifier. `Circuit.legalGuest`'s clauses are stated over
    `Circuit.satisfiesAlgebraic` — acceptance dropped — because that is where the VM-level proof
    consumes them: `satisfiesStateless_of_sinks` and `maintains_of_stateful_active` are what
    *derive* acceptance from bus balance, and `VmSat` hands their guest instances nothing but
    algebraic satisfaction. Assuming acceptance there would be circular.

    `legalOnAccepted_not_statelessSendOnly` shows the residue is real under the *actual* OpenVM
    semantics: a chip sending an out-of-table range check with an unconstrained multiplicity is a
    sound replacement of a legal chip, satisfies everything soundness transports, and still
    violates `Circuit.statelessSendOnly` — sharper than the general fact that
    `isSoundReplacementOf` transports no legality at all on a toy semantics with no invariants of
    its own; this shows what survives for OpenVM specifically and where it stops.

    That witness invites two objections, and `openVm_sound_but_illegal` gives up neither: it is
    vacuous (its lookup is in no table on every assignment, so the chip has no satisfying
    assignment at all), and the chip it replaces is not itself a `Circuit.legalGuest`. The
    sharpened form is a satisfiable chip, a sound replacement of one legal in full, whose offending
    interaction carries a payload the range checker *accepts*.
    `looseTabled_not_isSoundReplacementOf` says why any such witness must route through an
    assignment the semantics rejects: the same free-multiplicity move, transplanted onto a real
    OpenVM lookup bus — multiplicity free, payload in-table — is *not* a sound replacement,
    because `ApcOptimizer.OpenVM.maintainsInvariants` pins that multiplicity and the second
    conjunct rejects the change.

    `zeroMultiplicity_replaceable_by_receive` sharpens the same hole into a statement about
    `Circuit.isSoundReplacementOf` itself, with no free variable in sight: a bus interaction at
    multiplicity `0` may be replaced by one at multiplicity `-1`. Both literals; the replacement is
    sound. The mechanism is vacuity — a message in no table has no satisfying assignment to
    constrain, so both conjuncts hold for want of a witness — and it is confined to exactly that
    case: for an *acceptable* payload, `maintainsInvariants` pins the multiplicity and the second
    conjunct rejects the change. This is a real gap in the per-chip contract, not merely a missing
    convenience: two chips holding `+1` and `-1` of the same unacceptable message cancel, so bus
    balance never sees them, and `Host.forcesAccepts` fails for that run. Closing it means adding
    a multiplicity discipline over `Circuit.satisfiesAlgebraic` to `Spec.lean` — which is the same
    residue, stated where it belongs.

    So, of `openVm_vmSoundReplacement`'s legality assumptions, what genuinely has to be
    established per pass is: the three bus-shape clauses on algebraically-satisfying assignments
    that the semantics need not accept, and all of `StepLayout`, which has no analogue anywhere in
    `Spec.lean`. -/

variable {p : ℕ}

/-- `Circuit.legalGuest`'s three bus-shape clauses, weakened to the assignments the bus semantics
    already accepts (`Circuit.satisfies` in place of `Circuit.satisfiesAlgebraic`).

    Not a hypothesis of anything: this is the *conclusion* of
    `ApcOptimizer.OpenVM.legalOnAccepted_of_isSoundReplacementOf`, stating what an optimizer gets
    without asking for it. `StepLayout` has no counterpart here — nothing in `Spec.lean` mentions
    the execution bridge's shape at all.

    The third clause is stated for every active stateful message rather than only for sends, and
    without `StepLayout.sendsOk`'s ordering hypotheses: on an accepted assignment a receive
    gets its payload invariant from `accepts` itself, so the weakening in the quantifier buys back
    strength elsewhere. -/
structure Circuit.legalOnAccepted (c : Circuit p) (bs : BusSemantics p) (r : GuestBusRules p) :
    Prop where
  /-- `Circuit.statelessSendOnly`, on accepted assignments. -/
  sendOnly : ∀ asg, c.satisfies bs asg → ∀ bi ∈ c.busInteractions,
    r.isStateful bi.busId = false →
      (bi.eval asg).multiplicity = 0 ∨ (bi.eval asg).multiplicity = 1
  /-- `Circuit.statefulPolarity`, on accepted assignments. -/
  polarity : ∀ asg, c.satisfies bs asg → ∀ bi ∈ c.busInteractions,
    r.isStateful bi.busId = true →
      (bi.eval asg).multiplicity = 0 ∨ (bi.eval asg).multiplicity = 1 ∨
        (bi.eval asg).multiplicity = -1
  /-- `StepLayout.sendsOk`'s conclusion, on accepted assignments — and unconditionally, for
      receives as well as sends. -/
  payloadOk : ∀ asg, c.satisfies bs asg → ∀ bi ∈ c.busInteractions,
    r.isStateful bi.busId = true → (bi.eval asg).multiplicity ≠ 0 →
      r.payloadOk ((bi.eval asg).busId, (bi.eval asg).payload)

namespace ApcOptimizer.OpenVM

--------- What soundness transports ---------

/-- **OpenVM's bus invariants *are* the bus-shape half of legality.** Every clause of
    `Circuit.legalOnAccepted` is a case of `ApcOptimizer.OpenVM.maintainsInvariants`, read off the
    bus type: `= 1` on the four lookup buses, `= ±1` on the execution bridge and memory, and
    memory's byte conjunct is `openVmPayloadOk` verbatim. -/
theorem legalOnAccepted_of_guaranteesInvariants {busMap : BusMap} {memBusId : Nat} {c : Circuit p}
    (hmem : ∀ b, busMap b = some .memory → b = memBusId)
    (h : c.guaranteesInvariants (openVmBusSemantics p busMap)) :
    c.legalOnAccepted (openVmBusSemantics p busMap) (openVmGuestRules busMap memBusId hmem) := by
  have key : ∀ asg, c.satisfies (openVmBusSemantics p busMap) asg →
      ∀ bi ∈ c.busInteractions, bi.multiplicity.eval asg ≠ 0 →
        maintainsInvariants busMap (bi.eval asg) :=
    fun asg hsat bi hbi hmult => h asg hsat bi hbi hmult
  refine ⟨fun asg hsat bi hbi hst => ?_, fun asg hsat bi hbi hst => ?_,
    fun asg hsat bi hbi hst hmult => ?_⟩
  · simp only [BusInteraction.eval]
    simp only [openVmGuestRules, openVmIsStateful] at hst
    by_cases hmult : bi.multiplicity.eval asg = 0
    · exact Or.inl hmult
    have hmi := key asg hsat bi hbi hmult
    simp only [maintainsInvariants, BusInteraction.eval] at hmi
    cases hbm : busMap bi.busId with
    | none => rw [hbm] at hmi; exact hmi.elim
    | some t =>
      rw [hbm] at hst hmi
      cases t with
      | executionBridge | memory => simp [OpenVmBusType.isStateful] at hst
      | pcLookup | variableRangeChecker | bitwiseLookup | tupleRangeChecker =>
        exact Or.inr hmi
  · simp only [BusInteraction.eval]
    simp only [openVmGuestRules, openVmIsStateful] at hst
    by_cases hmult : bi.multiplicity.eval asg = 0
    · exact Or.inl hmult
    have hmi := key asg hsat bi hbi hmult
    simp only [maintainsInvariants, BusInteraction.eval] at hmi
    cases hbm : busMap bi.busId with
    | none => rw [hbm] at hmi; exact hmi.elim
    | some t =>
      rw [hbm] at hst hmi
      cases t with
      | executionBridge => exact Or.inr hmi
      | memory => exact Or.inr hmi.1
      | pcLookup | variableRangeChecker | bitwiseLookup | tupleRangeChecker =>
        simp [OpenVmBusType.isStateful] at hst
  · simp only [openVmGuestRules, openVmIsStateful] at hst
    have hmi := key asg hsat bi hbi hmult
    simp only [maintainsInvariants, BusInteraction.eval] at hmi
    show openVmPayloadOk busMap (bi.busId, bi.payload.map (fun e => e.eval asg))
    simp only [openVmPayloadOk]
    cases hbm : busMap bi.busId with
    | none => rw [hbm] at hmi; exact hmi.elim
    | some t =>
      rw [hbm] at hst hmi
      cases t with
      | executionBridge => trivial
      | memory => exact hmi.2
      | pcLookup | variableRangeChecker | bitwiseLookup | tupleRangeChecker =>
        simp [OpenVmBusType.isStateful] at hst

/-- **The transport.** A sound replacement of a chip that guarantees OpenVM's bus invariants
    inherits every bus-shape clause of legality on accepted assignments — no per-pass argument
    needed, it is `Circuit.isSoundReplacementOf`'s second conjunct. -/
theorem legalOnAccepted_of_isSoundReplacementOf {busMap : BusMap} {memBusId : Nat}
    (hmem : ∀ b, busMap b = some .memory → b = memBusId)
    {c c' : Circuit p} (hGI : c.guaranteesInvariants (openVmBusSemantics p busMap))
    (hSound : c'.isSoundReplacementOf c (openVmBusSemantics p busMap)) :
    c'.legalOnAccepted (openVmBusSemantics p busMap) (openVmGuestRules busMap memBusId hmem) :=
  legalOnAccepted_of_guaranteesInvariants hmem (hSound.2 hGI)

--------- What it does not transport ---------

/-- `defaultBusMap`'s variable range checker. -/
private abbrev rangeBusId : Nat := 3

/-- A lookup no table can contain: the variable range checker rejects any width above `17`
    (`ApcOptimizer.OpenVM.accepts`), so `bits = 18` is out of range whatever the value. -/
private abbrev outOfTablePayload (p : ℕ) : List (Expression p) :=
  [.const 0, .const ((18 : ℕ) : ZMod p)]

/-- The original chip: the out-of-table range check, switched off by a literal `0` multiplicity.
    Legal — `statelessSendOnly` is forced by the constant — and it guarantees the bus invariants
    vacuously. -/
def deadRangeCheck (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [{ busId := rangeBusId, multiplicity := .const 0, payload := outOfTablePayload p }]

/-- The "optimized" chip: the same interaction with a fresh, unconstrained multiplicity. Its
    lookup can never be accepted, so no satisfying assignment activates it — which is exactly why
    everything stated over `Circuit.satisfies` still holds of it. -/
def looseRangeCheck (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [{ busId := rangeBusId, multiplicity := .var ⟨"y", none⟩, payload := outOfTablePayload p }]

/-- The same interaction turned into a *receive*: multiplicity `-1`, a literal. On a stateless bus
    this is what `Circuit.statelessSendOnly` exists to forbid, and it is the shape two chips need
    to cancel an unacceptable lookup between them. -/
def receivingRangeCheck (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [{ busId := rangeBusId, multiplicity := .const (-1), payload := outOfTablePayload p }]

/-- The out-of-table lookup is in no table, at any multiplicity. -/
private theorem not_accepts_outOfTable [Fact p.Prime] (hp : 18 < p) (mult : ZMod p) :
    ¬ accepts defaultBusMap
      ⟨rangeBusId, mult, (outOfTablePayload p).map (fun e => e.eval (fun _ => 0))⟩ := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  intro hacc
  simp only [accepts, defaultBusMap, Expression.eval, List.map] at hacc
  exact absurd (ZMod.val_cast_of_lt hp ▸ hacc.1) (by omega)

/-- On any assignment, both chips have the same (identically zero) side effects: bus
    `rangeBusId` is stateless, so `Circuit.sideEffects` never looks at it. -/
private theorem sideEffects_eq (asg asg' : Variable → ZMod p) :
    (looseRangeCheck p).sideEffects (openVmBusSemantics p defaultBusMap) asg =
      (deadRangeCheck p).sideEffects (openVmBusSemantics p defaultBusMap) asg' := by
  funext m
  simp [Circuit.sideEffects, looseRangeCheck, deadRangeCheck, BusInteraction.eval,
    openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful]

/-- **The multiplicity of an interaction that can never be accepted is unconstrained by
    `Circuit.isSoundReplacementOf`** — even between two literals, and even in the direction that
    turns an *inactive* interaction into a *receive*.

    Both obligations are discharged by vacuity: `receivingRangeCheck` has no satisfying assignment
    at all (its message is active on every assignment and in no table), so the first conjunct
    quantifies over nothing and `Circuit.guaranteesInvariants` holds for want of a witness. The
    same move is unavailable for an *acceptable* payload — there
    `ApcOptimizer.OpenVM.maintainsInvariants` pins the multiplicity to `1` and the second conjunct
    rejects the replacement. So the hole is precisely: **a message that is never accepted makes
    every per-chip obligation vacuous.**

    Why the VM layer cannot absorb this: two guest chips holding `+1` and `-1` of the same
    unacceptable message cancel, so bus balance never notices, `VmSat` holds, and
    `Host.forcesAccepts` is false for that run. `Circuit.statelessSendOnly` is what rules the pair
    out, and it is assumed (`hLegal`/`hPreserve`), not derived. -/
theorem zeroMultiplicity_replaceable_by_receive [Fact p.Prime] (hp : 18 < p) :
    (receivingRangeCheck p).isSoundReplacementOf (deadRangeCheck p)
      (openVmBusSemantics p defaultBusMap) ∧
    ¬ (receivingRangeCheck p).statelessSendOnly (openVmGuestRules defaultBusMap openVmMemBusId) := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  -- The receive is active on every assignment, and in no table: nothing satisfies this chip.
  have hNoSat : ∀ asg,
      ¬ (receivingRangeCheck p).satisfies (openVmBusSemantics p defaultBusMap) asg := by
    intro asg hsat
    have hbi : (⟨rangeBusId, .const (-1), outOfTablePayload p⟩ : BusInteraction (Expression p)) ∈
        (receivingRangeCheck p).busInteractions := by simp [receivingRangeCheck]
    exact not_accepts_outOfTable hp _ (by
      simpa [openVmBusSemantics, BusInteraction.eval, outOfTablePayload, Expression.eval]
        using hsat.2 _ hbi (by simp [BusInteraction.eval, Expression.eval]))
  refine ⟨⟨fun asg hsat => absurd hsat (hNoSat asg),
    fun _ asg hsat => absurd hsat (hNoSat asg)⟩, fun hlegal => ?_⟩
  have hforced := hlegal (fun _ => 0) (by simp [Circuit.satisfiesAlgebraic, receivingRangeCheck])
    { busId := rangeBusId, multiplicity := .const (-1), payload := outOfTablePayload p }
    (by simp [receivingRangeCheck]) rfl
  simp only [BusInteraction.eval, Expression.eval] at hforced
  rcases hforced with h0 | h1
  · exact absurd h0 hne
  · -- `-1 = 1` would make `2 = 0`.
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -h1
    have := congrArg ZMod.val h2
    rw [ZMod.val_cast_of_lt (by omega), ZMod.val_zero] at this
    omega

/-- **The residue, under the real OpenVM semantics.** `looseRangeCheck` is a sound replacement of
    a chip whose multiplicity shape is legal and which guarantees the bus invariants; it therefore
    inherits every clause of `Circuit.legalOnAccepted` (via
    `legalOnAccepted_of_isSoundReplacementOf`) — and it is still not
    `Circuit.statelessSendOnly`, because that clause quantifies over assignments the semantics
    does not accept, where `Circuit.guaranteesInvariants` says nothing.

    `18 < p` only makes the out-of-table width and the offending multiplicity `2` distinct field
    elements; every field this development targets is far larger. -/
theorem legalOnAccepted_not_statelessSendOnly [Fact p.Prime] (hp : 18 < p) :
    (deadRangeCheck p).guaranteesInvariants (openVmBusSemantics p defaultBusMap) ∧
    (deadRangeCheck p).statelessSendOnly (openVmGuestRules defaultBusMap openVmMemBusId) ∧
    (looseRangeCheck p).isSoundReplacementOf (deadRangeCheck p)
      (openVmBusSemantics p defaultBusMap) ∧
    (looseRangeCheck p).legalOnAccepted (openVmBusSemantics p defaultBusMap)
      (openVmGuestRules defaultBusMap openVmMemBusId) ∧
    ¬ (looseRangeCheck p).statelessSendOnly (openVmGuestRules defaultBusMap openVmMemBusId) := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  -- The dead chip's only interaction is inactive, so both invariant claims are vacuous.
  have hdeadPassive : ∀ (asg : Variable → ZMod p), ∀ bi ∈ (deadRangeCheck p).busInteractions,
      (bi.eval asg).multiplicity = 0 := by
    intro asg bi hbi
    simp only [deadRangeCheck, List.mem_singleton] at hbi
    subst hbi
    rfl
  have hdeadGI : (deadRangeCheck p).guaranteesInvariants (openVmBusSemantics p defaultBusMap) :=
    fun asg _ bi hbi hmult => absurd (hdeadPassive asg bi hbi) hmult
  have hdeadSat : ∀ asg, (deadRangeCheck p).satisfies (openVmBusSemantics p defaultBusMap) asg :=
    fun asg => ⟨fun e he => absurd he (by simp [deadRangeCheck]),
      fun bi hbi hmult => absurd (hdeadPassive asg bi hbi) hmult⟩
  -- The loose chip's only interaction can never be accepted, so it is inactive on every
  -- *satisfying* assignment — and it has no satisfying assignment that activates it.
  have hloosePassive : ∀ asg, (looseRangeCheck p).satisfies (openVmBusSemantics p defaultBusMap) asg →
      ∀ bi ∈ (looseRangeCheck p).busInteractions, (bi.eval asg).multiplicity = 0 := by
    intro asg hsat bi hbi
    by_contra hmult
    have hacc := hsat.2 bi hbi hmult
    simp only [looseRangeCheck, List.mem_singleton] at hbi
    subst hbi
    exact not_accepts_outOfTable hp _ (by
      simpa [openVmBusSemantics, BusInteraction.eval, outOfTablePayload, Expression.eval]
        using hacc)
  have hlooseGI : (looseRangeCheck p).guaranteesInvariants
      (openVmBusSemantics p defaultBusMap) :=
    fun asg hsat bi hbi hmult => absurd (hloosePassive asg hsat bi hbi) hmult
  have hSound : (looseRangeCheck p).isSoundReplacementOf (deadRangeCheck p)
      (openVmBusSemantics p defaultBusMap) :=
    ⟨fun asg _ => ⟨asg, hdeadSat asg, sideEffects_eq asg asg⟩, fun _ => hlooseGI⟩
  refine ⟨hdeadGI, ?_, hSound,
    legalOnAccepted_of_isSoundReplacementOf defaultBusMap_mem_unique hdeadGI hSound, ?_⟩
  · intro asg _ bi hbi _
    simp only [deadRangeCheck, List.mem_singleton] at hbi
    exact Or.inl (hbi ▸ rfl)
  · intro hlegal
    have hforced := hlegal (fun _ => ((2 : ℕ) : ZMod p))
      (by simp [Circuit.satisfiesAlgebraic, looseRangeCheck])
      { busId := rangeBusId, multiplicity := .var ⟨"y", none⟩, payload := outOfTablePayload p }
      (by simp [looseRangeCheck]) rfl
    simp only [BusInteraction.eval, Expression.eval] at hforced
    have hv2 : (((2 : ℕ) : ZMod p)).val = 2 := ZMod.val_cast_of_lt (by omega)
    rcases hforced with h0 | h1
    · have := congrArg ZMod.val h0
      rw [hv2, ZMod.val_zero] at this
      omega
    · have := congrArg ZMod.val h1
      rw [hv2, ZMod.val_one] at this
      omega

--------- What it does not transport, against a chip the VM would run ---------

/-- The replacement's free multiplicity. -/
private abbrev multVar : Variable := ⟨"y", none⟩

/-- The replacement's free range-check width. -/
private abbrev widthVar : Variable := ⟨"b", none⟩

/-- An in-table range check — `0 < 2 ^ 0` — at the literal multiplicity `1`. -/
def tabledRangeCheck (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [{ busId := rangeBusId, multiplicity := .const 1, payload := [.const 0, .const 0] }]

/-- The same interaction with a fresh, unconstrained multiplicity — the naive free-multiplicity
    witness, transplanted onto a real OpenVM lookup bus. -/
def looseTabledRangeCheck (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [{ busId := rangeBusId, multiplicity := .var multVar, payload := [.const 0, .const 0] }]

/-- **The naive free-multiplicity witness does not lift verbatim.** Freeing a stateless
    multiplicity works on a semantics whose `maintainsInvariants` is `True`, since
    `ApcOptimizer.OpenVM.accepts` likewise never reads a lookup's multiplicity. That is true and
    not enough: OpenVM's `maintainsInvariants` *does* read it, pinning it to `1` on every lookup
    bus, and `Circuit.isSoundReplacementOf`'s second conjunct transports that. Freeing the
    multiplicity of a lookup that stays in-table is therefore not a sound replacement here —
    `y := 2` satisfies the chip and breaks the invariant.

    So an OpenVM witness has to reach an assignment the semantics does *not* accept; which one is
    what `openVm_sound_but_illegal` chooses, and it is the acceptance gate rather than
    multiplicity-blindness that opens the hole. -/
theorem looseTabled_not_isSoundReplacementOf [Fact p.Prime] (hp : 2 < p) :
    ¬ (looseTabledRangeCheck p).isSoundReplacementOf (tabledRangeCheck p)
      (openVmBusSemantics p defaultBusMap) := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h2ne0 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_cast_of_lt (by omega), ZMod.val_zero] at this; omega
  have h2ne1 : ((2 : ℕ) : ZMod p) ≠ 1 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_cast_of_lt (by omega), ZMod.val_one] at this; omega
  intro hSound
  have hGI : (tabledRangeCheck p).guaranteesInvariants (openVmBusSemantics p defaultBusMap) := by
    refine fun asg _ bi hbi _ => ?_
    simp only [tabledRangeCheck, List.mem_singleton] at hbi
    subst hbi
    simp [openVmBusSemantics, maintainsInvariants, defaultBusMap, BusInteraction.eval,
      Expression.eval]
  have hsat : (looseTabledRangeCheck p).satisfies (openVmBusSemantics p defaultBusMap)
      (fun _ => ((2 : ℕ) : ZMod p)) := by
    refine ⟨fun e he => ?_, fun bi hbi _ => ?_⟩
    · simp [looseTabledRangeCheck] at he
    · simp only [looseTabledRangeCheck, List.mem_singleton] at hbi
      subst hbi
      simp [openVmBusSemantics, accepts, defaultBusMap, BusInteraction.eval, Expression.eval]
  have hGI' : ∀ bi ∈ (looseTabledRangeCheck p).busInteractions,
      bi.multiplicity.eval (fun _ => ((2 : ℕ) : ZMod p)) ≠ 0 →
        maintainsInvariants defaultBusMap (bi.eval (fun _ => ((2 : ℕ) : ZMod p))) :=
    fun bi hbi hmult => hSound.2 hGI _ hsat bi hbi hmult
  have hbad := hGI'
    ⟨rangeBusId, .var multVar, [.const 0, .const 0]⟩ (by simp [looseTabledRangeCheck]) h2ne0
  simp only [maintainsInvariants, defaultBusMap, BusInteraction.eval, Expression.eval] at hbad
  exact h2ne1 hbad

/-- One instruction step (`StepLayout`: receive `(0, 0)`, send `(0, 1)`) carrying an
    in-table range check at the literal multiplicity `1`. A genuine `Circuit.legalGuest`
    (`checkedStepChip_legalGuest`) — the chip `openVm_sound_but_illegal` replaces. -/
def checkedStepChip (p : ℕ) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [ ⟨openVmExecBusId, .const (-1), [.const 0, .const 0]⟩,
      ⟨openVmExecBusId, .const 1, [.const 0, .const 1]⟩,
      ⟨rangeBusId, .const 1, [.const 0, .const 0]⟩ ]

/-- The "optimized" chip: the same step, but both its range checks — one of free width, one at the
    in-table payload `(0, 0)` — go out at one free multiplicity, tied to the width by
    `(y - 1) (b - 18) = 0`.

    The free width is the poison. On `b = 18` the first check is in no table
    (`ApcOptimizer.OpenVM.accepts` caps the variable range checker at `17` bits), so no assignment
    extending it is `Circuit.satisfies`, and everything soundness transports switches off for the
    *whole* chip — leaving the second, perfectly acceptable check free to go out at `y = 2`. -/
def poisonedStepChip (p : ℕ) : Circuit p where
  algebraicConstraints :=
    [.mul (.add (.var multVar) (.const (-1)))
      (.add (.var widthVar) (.const (-((18 : ℕ) : ZMod p))))]
  busInteractions :=
    [ ⟨openVmExecBusId, .const (-1), [.const 0, .const 0]⟩,
      ⟨openVmExecBusId, .const 1, [.const 0, .const 1]⟩,
      ⟨rangeBusId, .var multVar, [.const 0, .var widthVar]⟩,
      ⟨rangeBusId, .var multVar, [.const 0, .const 0]⟩ ]

/-- `checkedStepChip` is a chip `openVmHost` will run: every clause of `Circuit.legalGuest`,
    step layout included, at any window above one tick. -/
private theorem checkedStepChip_legalGuest [Fact p.Prime] (hp : 18 < p)
    {maxWindow maxLookback maxInteractions : ℕ} (hw : 1 < maxWindow) (hi : 3 ≤ maxInteractions) :
    (checkedStepChip p).legalGuest (openVmGuestRules defaultBusMap openVmMemBusId)
      maxWindow maxLookback maxInteractions := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  refine ⟨?_, ?_, ?_, by simp [checkedStepChip]; omega⟩
  · intro asg _ bi hbi hst
    simp only [checkedStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl | rfl <;>
      simp_all [openVmGuestRules, openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful,
        BusInteraction.eval, Expression.eval, openVmExecBusId]
  · intro asg _ bi hbi hst
    simp only [checkedStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl | rfl <;>
      simp_all [openVmGuestRules, openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful,
        BusInteraction.eval, Expression.eval, openVmExecBusId]
  · -- One step, `(0, 0) → (0, 1)`, with each interaction's offset its own position in the list.
    intro asg _ _
    refine ⟨⟨0, 0, 0, 1, by norm_num, hw, ?_, ?_, ?_, fun i => (i.val : ℤ), ?_, ?_⟩⟩
    · simp [Circuit.allEffects, checkedStepChip, BusInteraction.eval, Expression.eval,
        openVmGuestRules, openVmExecBusId]
    · simp [Circuit.allEffects, checkedStepChip, BusInteraction.eval, Expression.eval,
        openVmGuestRules, openVmExecBusId]
    · intro m hm h1 h2
      simp only [openVmGuestRules] at hm h1 h2
      have e1 : ¬ ((openVmExecBusId, [(0 : ZMod p), 0]) = m) := fun h => h1 h.symm
      have e2 : ¬ ((openVmExecBusId, [(0 : ZMod p), 1]) = m) := by
        intro h; exact h2 (by simpa using h.symm)
      have e3 : ¬ ((rangeBusId, [(0 : ZMod p), 0]) = m) := by
        intro h; rw [← h] at hm; simp [rangeBusId] at hm
      simp [Circuit.allEffects, checkedStepChip, BusInteraction.eval, Expression.eval, e1, e2, e3]
    · rintro i ⟨hst, -⟩
      fin_cases i
      · exact ⟨by push_cast; omega, by norm_num, by
          simp [checkedStepChip, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
            BusInteraction.eval, Expression.eval, openVmExecBusId, openVmMemBusId]⟩
      · exact ⟨by push_cast; omega, by norm_num, by
          simp [checkedStepChip, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
            BusInteraction.eval, Expression.eval, openVmExecBusId, openVmMemBusId]⟩
      · simp [checkedStepChip, openVmGuestRules, openVmIsStateful, defaultBusMap,
          OpenVmBusType.isStateful, rangeBusId] at hst
    · -- `checkedStepChip` never touches the memory bus, so `memSendsOk` is vacuous.
      exact fun i ⟨_, hbmem⟩ _ => by
        fin_cases i <;>
          simp [checkedStepChip, openVmGuestRules, openVmExecBusId, openVmMemBusId,
            rangeBusId] at hbmem

/-- **The residue, against a chip OpenVM would actually run.** `looseRangeCheck` leaves two ways
    out: its lookup is in no table on *any* assignment, so the chip has no satisfying assignment at
    all, and `deadRangeCheck` is not a `Circuit.legalGuest` (nothing on the execution bridge, so no
    `StepLayout`). Neither survives here.

    `poisonedStepChip` is a sound replacement of a chip that is legal in full; it is satisfiable,
    so nothing below is vacuous; it is not `Circuit.statelessSendOnly`; and the interaction that
    breaks it carries a payload the variable range checker *accepts*. That last point is what makes
    the residue bite: the multiplicity discipline exists to stop a lookup being counted a number of
    times that wraps the characteristic (whitepaper §2.2.4), and this is a legitimate message
    counted twice — not a message no table would answer.

    The mechanism is the quantifier, in the one form soundness cannot reach. Everything
    `legalOnAccepted_of_isSoundReplacementOf` transports is gated on `Circuit.satisfies`, which is
    a property of the *whole* chip: one unacceptable interaction anywhere in it — the free-width
    check at `b = 18` — voids the gate for every other interaction on that assignment.

    `18 < p` only keeps the out-of-table width, the offending multiplicity `2`, `0` and `1`
    distinct field elements. -/
theorem openVm_sound_but_illegal [Fact p.Prime] (hp : 18 < p)
    {maxWindow maxLookback maxInteractions : ℕ} (hw : 1 < maxWindow) (hi : 3 ≤ maxInteractions) :
    (checkedStepChip p).legalGuest (openVmGuestRules defaultBusMap openVmMemBusId)
        maxWindow maxLookback maxInteractions ∧
      (poisonedStepChip p).isSoundReplacementOf (checkedStepChip p)
        (openVmBusSemantics p defaultBusMap) ∧
      (∃ asg, (poisonedStepChip p).satisfies (openVmBusSemantics p defaultBusMap) asg) ∧
      ¬ (poisonedStepChip p).statelessSendOnly (openVmGuestRules defaultBusMap openVmMemBusId) ∧
      accepts defaultBusMap ⟨rangeBusId, ((2 : ℕ) : ZMod p), [0, 0]⟩ := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have h18 : (((18 : ℕ) : ZMod p)).val = 18 := ZMod.val_cast_of_lt (by omega)
  have h2v : (((2 : ℕ) : ZMod p)).val = 2 := ZMod.val_cast_of_lt (by omega)
  have hcheckedSat : ∀ asg,
      (checkedStepChip p).satisfies (openVmBusSemantics p defaultBusMap) asg := by
    refine fun asg => ⟨fun e he => ?_, fun bi hbi _ => ?_⟩
    · simp [checkedStepChip] at he
    · simp only [checkedStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
      rcases hbi with rfl | rfl | rfl <;>
        simp [openVmBusSemantics, accepts, defaultBusMap, BusInteraction.eval, Expression.eval,
          openVmExecBusId, rangeBusId]
  -- Only the execution bridge is stateful, and both chips carry the same two literal bridge
  -- interactions.
  have hSideEffects : ∀ asg asg',
      (poisonedStepChip p).sideEffects (openVmBusSemantics p defaultBusMap) asg =
        (checkedStepChip p).sideEffects (openVmBusSemantics p defaultBusMap) asg' := by
    intro asg asg'
    funext m
    simp [Circuit.sideEffects, poisonedStepChip, checkedStepChip, BusInteraction.eval,
      Expression.eval, openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful,
      List.filter_cons, openVmExecBusId, rangeBusId]
  -- On an accepted assignment the width is in range, so `b - 18 ≠ 0` and the constraint pins `y`.
  have hpin : ∀ asg, (poisonedStepChip p).satisfies (openVmBusSemantics p defaultBusMap) asg →
      asg multVar ≠ 0 → asg multVar = 1 := by
    intro asg hsat hy
    have hwidth := hsat.2 ⟨rangeBusId, .var multVar, [.const 0, .var widthVar]⟩
      (by simp [poisonedStepChip]) (by simpa [BusInteraction.eval, Expression.eval] using hy)
    have hb : (asg widthVar).val ≤ 17 := by
      simpa [openVmBusSemantics, accepts, defaultBusMap, BusInteraction.eval, Expression.eval,
        rangeBusId] using hwidth.1
    have hbne : asg widthVar + -((18 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have hbeq : asg widthVar = ((18 : ℕ) : ZMod p) := by linear_combination h
      rw [hbeq, h18] at hb; omega
    have hc := hsat.1
      (.mul (.add (.var multVar) (.const (-1)))
        (.add (.var widthVar) (.const (-((18 : ℕ) : ZMod p)))))
      (by simp [poisonedStepChip])
    simp only [Expression.eval] at hc
    rcases mul_eq_zero.mp hc with h | h
    · linear_combination h
    · exact absurd h hbne
  have hpoisonedGI :
      (poisonedStepChip p).guaranteesInvariants (openVmBusSemantics p defaultBusMap) := by
    refine fun asg hsat bi hbi hmult => ?_
    simp only [poisonedStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl | rfl | rfl
    · simp [openVmBusSemantics, maintainsInvariants, defaultBusMap, BusInteraction.eval,
        Expression.eval, openVmExecBusId]
    · simp [openVmBusSemantics, maintainsInvariants, defaultBusMap, BusInteraction.eval,
        Expression.eval, openVmExecBusId]
    · have := hpin asg hsat (by simpa [BusInteraction.eval, Expression.eval] using hmult)
      simp [openVmBusSemantics, maintainsInvariants, defaultBusMap, BusInteraction.eval,
        Expression.eval, rangeBusId, this]
    · have := hpin asg hsat (by simpa [BusInteraction.eval, Expression.eval] using hmult)
      simp [openVmBusSemantics, maintainsInvariants, defaultBusMap, BusInteraction.eval,
        Expression.eval, rangeBusId, this]
  refine ⟨checkedStepChip_legalGuest hp hw hi,
    ⟨fun asg _ => ⟨asg, hcheckedSat asg, hSideEffects asg asg⟩, fun _ => hpoisonedGI⟩,
    ⟨?_, ?_, ?_⟩⟩
  -- `y = 1`, `b = 0` is an honest run of the chip: the hole below is not vacuity.
  · refine ⟨fun v => if v = widthVar then 0 else 1, ?_, ?_⟩
    · intro e he
      simp only [poisonedStepChip, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      simp [Expression.eval]
    · refine fun bi hbi _ => ?_
      simp only [poisonedStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
      rcases hbi with rfl | rfl | rfl | rfl <;>
        simp [openVmBusSemantics, accepts, defaultBusMap, BusInteraction.eval, Expression.eval,
          openVmExecBusId, rangeBusId]
  -- `y = 2`, `b = 18` satisfies the constraint, and sends an in-table check twice.
  · intro hlegal
    have hforced := hlegal
      (fun v => if v = widthVar then ((18 : ℕ) : ZMod p) else ((2 : ℕ) : ZMod p))
      (by
        intro e he
        simp only [poisonedStepChip, List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        simp [Expression.eval])
      ⟨rangeBusId, .var multVar, [.const 0, .const 0]⟩ (by simp [poisonedStepChip]) rfl
    simp only [BusInteraction.eval, Expression.eval] at hforced
    rw [if_neg (by decide)] at hforced
    rcases hforced with h | h
    · have := congrArg ZMod.val h; rw [h2v, ZMod.val_zero] at this; omega
    · have := congrArg ZMod.val h; rw [h2v, ZMod.val_one] at this; omega
  · simp [accepts, defaultBusMap, rangeBusId]

end ApcOptimizer.OpenVM
