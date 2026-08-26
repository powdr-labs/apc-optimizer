import ApcOptimizer.VmSpec.Implementation.Connection
import ApcOptimizer.VmSpec.OpenVm

set_option autoImplicit false

/-! Discharging `Realizes.lean`'s host-side conditions for the concrete `openVmHost`.

    `Host.sinksAreTables` is the manuscript's "each table sink implements its bus's predicate",
    and for `openVmHost` it comes down to a case split over the nine host chips: the four lookup
    chips restate `OpenVM.accepts`'s own conditions, and the four memory-bus chips and the
    connector cannot touch a *stateless* message at all, so they are vacuous here.
    `BusSemantics.statefulAcceptsOfMaintains` is likewise discharged, by inspection of OpenVM's
    memory `accepts`/`maintainsInvariants` pair.

    `Host.statefulChipsMaintain` is another nine-way split: the lookup chips pin their bus id to
    a stateless bus and so cannot touch a stateful message at all, the four memory chips each
    carry byte-valued data limbs, and the connector sits on the execution bridge, whose invariant
    is polarity alone. `Host.absorbsStateless` pools each lookup chip's instances into the one
    its `instanceBound` allows, plus that chip's bus's slice of `δ` — a lookup predicate is closed
    under sums, so one instance nets what a whole list of them would have — which needs `δ`'s
    support confined to `{2,3,6,7}` (`defaultBusMap_stateless`).

    `openVmHost_realizes` collects all five into the single `Host.realizes`, with no hypotheses
    left over — so `openVm_vmSoundReplacement` assumes nothing about the VM, only about the
    optimization. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- The `RankModel` this argument runs on. Not a field of `openVmHost`: the ordering is the
    argument's device, not part of the VM (`Implementation/Rank.lean`). Its two components do still
    appear inside `openVmHost`'s audited `legalGuest`, which is where an auditor meets them. -/
def openVmRankModel (memBusId : Nat := openVmMemBusId) : RankModel p :=
  ⟨openVmRank memBusId, openVmRankBound⟩

/-- `memoryFinalizeHostChip`'s slot in `openVmHost.chips` — the one host chip
    `Host.statefulChipsMaintain` carves out as `Host.exemptChip` instead of assuming outright
    (`openVmHost_finalize_exempt`). -/
def openVmFinalizeIdx (P : OpenVmParams p) :
    Fin (openVmHost P).chips.length :=
  ⟨5, by simp [openVmHost]⟩

/-- A message `busStateOf` gives a nonzero net multiplicity is carried by one of its
    interactions. -/
theorem exists_of_busStateOf_ne_zero {msgs : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : busStateOf msgs m ≠ 0) : ∃ msg ∈ msgs, (msg.busId, msg.payload) = m := by
  by_contra hcon
  refine h (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  exact absurd ⟨y, hy1, of_decide_eq_true hy2⟩ hcon

theorem OutputRead.interactions_busId (r : OutputRead p) (memBusId : Nat) :
    ∀ msg ∈ r.interactions memBusId, msg.busId = memBusId := by
  intro msg hmsg
  obtain ⟨⟨i, w, t⟩, -, rfl⟩ := List.mem_map.mp hmsg
  rfl

theorem ConnectorBoundary.interactions_busId (r : ConnectorBoundary p) (execBusId : Nat) :
    ∀ msg ∈ r.interactions execBusId, msg.busId = execBusId := by
  intro msg hmsg
  simp only [ConnectorBoundary.interactions, List.mem_cons, List.not_mem_nil, or_false] at hmsg
  rcases hmsg with rfl | rfl <;> rfl

/-- Every message an `InputRead` describes is on the execution bridge (the two clock-step
    messages `InputRead.interactions` opens with) or the memory bus (everything else) — never
    anywhere else, mirroring `StepLayout.bridgeNoOther` for a guest instruction. -/
theorem InputRead.interactions_busId (r : InputRead p) (ptrReg execBusId memBusId : Nat) :
    ∀ msg ∈ r.interactions ptrReg execBusId memBusId,
      msg.busId = execBusId ∨ msg.busId = memBusId := by
  intro msg hmsg
  rw [InputRead.interactions] at hmsg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmsg
  rcases hmsg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  all_goals exact Or.inr rfl

/-- **`openVmHost`'s table sinks are honest.** Each of the four lookup chips restates its bus's
    case of `OpenVM.accepts`, and the four memory-bus chips cannot carry a stateless message at
    all, so they are vacuous.

    With `forcesAccepts_of_hostSound`, this feeds `Host.forcesAccepts` for a concrete OpenVM host
    — the condition that was outright false before `VmSat` gained its trace budget. -/
theorem openVmHost_sinksAreTables (P : OpenVmParams p) :
    (openVmHost P).sinksAreTables
      (openVmBusSemantics p defaultBusMap) := by
  rintro hA hlegal ⟨mb, ml⟩ hm hnet mult hmult
  obtain ⟨t, c, hc, hcm⟩ := exists_instance_of_hostNet_ne_zero hnet
  have hleg := hlegal.producible t c hc
  show ApcOptimizer.OpenVM.accepts defaultBusMap _
  fin_cases t
  -- PC lookup: arity only, exactly as `OpenVM.accepts` has it.
  · obtain ⟨hbus, hlen⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]; exact hlen
  -- The three remaining tables: the chip's payload predicate *is* `accepts`'s case for that bus,
  -- so once the payload is split to the right arity both sides are the same proposition.
  · obtain ⟨hbus, hacc⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]
    revert hacc
    rcases ml with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨op, _ | ⟨w, rest⟩⟩⟩⟩⟩ <;> exact id
  · obtain ⟨hbus, hacc⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]
    revert hacc
    rcases ml with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> exact id
  · obtain ⟨hbus, hacc⟩ := hleg (mb, ml) hcm
    subst hbus
    rw [ApcOptimizer.OpenVM.accepts]; simp only [defaultBusMap]
    revert hacc
    rcases ml with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> exact id
  -- Memory init/finalize pin the bus id directly; the message would have to be stateful.
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  -- Output/input are pinned to an exact witness, every interaction of which is on the memory bus.
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    have hbus : mb = 1 :=
      (congrArg Prod.fst heq).symm.trans (OutputRead.interactions_busId r 1 msg hmsg)
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    rcases InputRead.interactions_busId r P.ptrReg 0 1 msg hmsg with h0 | h1
    · have hbus : mb = 0 := (congrArg Prod.fst heq).symm.trans h0
      subst hbus
      simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
    · have hbus : mb = 1 := (congrArg Prod.fst heq).symm.trans h1
      subst hbus
      simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm
  -- The connector lives on the execution bridge, which is stateful.
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    have hbus : mb = 0 :=
      (congrArg Prod.fst heq).symm.trans (ConnectorBoundary.interactions_busId r 0 msg hmsg)
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hm

/-- **`BusSemantics.statefulAcceptsOfPayloadOk` for OpenVM.** On the memory bus, `accepts` asks
    that a *received* byte-checked word be byte-valued, and `maintainsInvariants` asks exactly
    that of any message carrying the payload — so a receive inherits acceptance from its sender.
    The execution bridge accepts everything.

    `payloadOk` hands over some multiplicity at which the payload maintains the invariants; which
    one is irrelevant, and the proof simply names it. -/
theorem openVmBusSemantics_statefulAcceptsOfPayloadOk (r0 : GuestBusRules p)
    (hmem : ∀ m : BusMessage p, (openVmBusSemantics p defaultBusMap).isStateful m.1 = true →
      m.1 ≠ r0.memBusId →
      ∃ mult : ZMod p, (openVmBusSemantics p defaultBusMap).maintainsInvariants ⟨m.1, mult, m.2⟩) :
    (openVmBusSemantics p defaultBusMap).statefulAcceptsOfPayloadOk r0 hmem := by
  rintro msg hst ⟨mult, hmaint⟩
  set msg' : BusInteraction (ZMod p) := ⟨msg.busId, mult, msg.payload⟩ with hmsg'
  have hbus : msg.busId = msg'.busId := rfl
  have hpay : msg.payload = msg'.payload := rfl
  have hm : ApcOptimizer.OpenVM.maintainsInvariants defaultBusMap msg' := hmaint
  unfold ApcOptimizer.OpenVM.maintainsInvariants at hm
  rw [← hbus] at hm
  show ApcOptimizer.OpenVM.accepts defaultBusMap msg
  rw [ApcOptimizer.OpenVM.accepts]
  cases hbm : defaultBusMap msg.busId with
  | none => simp [openVmBusSemantics, hbm, OpenVmBusType.isStateful] at hst
  | some t =>
    cases t with
    | pcLookup => simp [openVmBusSemantics, hbm, OpenVmBusType.isStateful] at hst
    | variableRangeChecker => simp [openVmBusSemantics, hbm, OpenVmBusType.isStateful] at hst
    | bitwiseLookup => simp [openVmBusSemantics, hbm, OpenVmBusType.isStateful] at hst
    | tupleRangeChecker s1 s2 =>
      simp [openVmBusSemantics, hbm, OpenVmBusType.isStateful] at hst
    | executionBridge => simp
    | memory =>
      rw [hbm] at hm
      replace hm : (msg'.multiplicity = 1 ∨ msg'.multiplicity = -1) ∧
        match memoryPayload? msg'.payload with
        | some f => f.isByteChecked → ∀ d ∈ f.data, isByte d
        | none => True := hm
      show match memoryPayload? msg.payload with
        | some f => msg.multiplicity = -1 → f.isByteChecked → ∀ d ∈ f.data, isByte d
        | none => True
      rw [hpay]
      cases hmp : memoryPayload? msg'.payload with
      | none => trivial
      | some f => rw [hmp] at hm; exact fun _ => hm.2

/-- Zero is a byte — the limbs memory initialization writes, and the padding limbs every
    single-value word carries. -/
theorem isByte_zero : isByte (0 : ZMod p) := by
  show (0 : ZMod p).val < 256
  simp [ZMod.val_zero]

/-- A memory payload laid out as `[addressSpace, pointer] ++ w.toList ++ [timestamp]` has exactly
    `w`'s entries as its data limbs. Every four-limb word an `InputRead` touches is of this
    shape — the two peeked registers and each overwritten cell. -/
theorem memoryPayload?_word {as ptr ts : ZMod p} {w : Vector (ZMod p) 4} {f : MemoryPayload p}
    (h : memoryPayload? ([as, ptr] ++ w.toList ++ [ts]) = some f) :
    ∀ d ∈ f.data, d ∈ w.toList := by
  obtain ⟨a1, a2, a3, a4, hl⟩ : ∃ a1 a2 a3 a4, w.toList = [a1, a2, a3, a4] := by
    have h4 : w.toList.length = 4 := by simp
    rcases hh : w.toList with _ | ⟨a1, t1⟩
    · rw [hh] at h4; simp at h4
    rcases t1 with _ | ⟨a2, t2⟩
    · rw [hh] at h4; simp at h4
    rcases t2 with _ | ⟨a3, t3⟩
    · rw [hh] at h4; simp at h4
    rcases t3 with _ | ⟨a4, t4⟩
    · rw [hh] at h4; simp at h4
    rcases t4 with _ | ⟨a5, t5⟩
    · exact ⟨a1, a2, a3, a4, rfl⟩
    · rw [hh] at h4; simp at h4
  rw [hl] at h ⊢
  simp only [List.cons_append, List.nil_append, memoryPayload?, Option.some.injEq] at h
  subst h
  intro d hd
  simp at hd ⊢
  tauto

/-- Every message an `OutputRead` describes carries byte-valued data limbs: the word itself by
    `OutputRead.wordsAreBytes`, the three padding limbs by `isByte_zero`. -/
theorem OutputRead.interactions_data (r : OutputRead p) (memBusId : Nat) :
    ∀ msg ∈ r.interactions memBusId, ∀ f : MemoryPayload p,
      memoryPayload? msg.payload = some f → ∀ d ∈ f.data, isByte d := by
  intro msg hmsg f hf d hd
  obtain ⟨⟨i, w, t⟩, hiw, rfl⟩ := List.mem_map.mp hmsg
  have hw : isByte w := r.wordsAreBytes w (List.of_mem_zip (List.of_mem_zip hiw).2).1
  simp only [memoryPayload?, Option.some.injEq] at hf
  subst hf
  simp at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact hw
  all_goals exact isByte_zero

/-- Every message an `InputRead` describes carries byte-valued data limbs — the peeked register
    value by `ptrLimbsAreBytes`, the overwritten word by `oldWordIsBytes`, the written value by
    `byteIsByte`. -/
theorem InputRead.interactions_data (r : InputRead p) (ptrReg execBusId memBusId : Nat) :
    ∀ msg ∈ r.interactions ptrReg execBusId memBusId, ∀ f : MemoryPayload p,
      memoryPayload? msg.payload = some f → ∀ d ∈ f.data, isByte d := by
  intro msg hmsg f hf d hd
  rw [InputRead.interactions] at hmsg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmsg
  rcases hmsg with rfl | rfl | rfl | rfl | rfl | rfl
  -- The two bridge messages carry a two-element payload, too short to be a memory record.
  · simp [memoryPayload?] at hf
  · simp [memoryPayload?] at hf
  · exact r.ptrLimbsAreBytes d (memoryPayload?_word hf d hd)
  · exact r.ptrLimbsAreBytes d (memoryPayload?_word hf d hd)
  · exact r.oldWordIsBytes d (memoryPayload?_word hf d hd)
  · simp only [memoryPayload?, Option.some.injEq] at hf
    subst hf
    simp at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact r.byteIsByte
    all_goals exact isByte_zero

/-- On the memory bus, a payload whose data limbs are bytes maintains OpenVM's invariants. This
    is the witness every memory-touching host chip supplies: multiplicity `1` satisfies the
    polarity clause, and the byte clause is the hypothesis. -/
theorem memory_maintains {payload : List (ZMod p)}
    (h : ∀ f : MemoryPayload p, memoryPayload? payload = some f → ∀ d ∈ f.data, isByte d) :
    ∃ msg : BusInteraction (ZMod p), msg.busId = 1 ∧ msg.payload = payload ∧
      (openVmBusSemantics p defaultBusMap).maintainsInvariants msg := by
  refine ⟨⟨1, 1, payload⟩, rfl, rfl, ?_⟩
  show ApcOptimizer.OpenVM.maintainsInvariants defaultBusMap
    (⟨1, 1, payload⟩ : BusInteraction (ZMod p))
  rw [ApcOptimizer.OpenVM.maintainsInvariants]
  show ((1 : ZMod p) = 1 ∨ (1 : ZMod p) = -1) ∧
    match memoryPayload? payload with
    | some f => f.isByteChecked → ∀ d ∈ f.data, isByte d
    | none => True
  refine ⟨Or.inl rfl, ?_⟩
  cases hmp : memoryPayload? payload with
  | none => trivial
  | some f => exact fun _ => h f hmp

/-- On the execution bridge, OpenVM's invariant is polarity alone, so any payload maintains it. -/
theorem bridge_maintains (payload : List (ZMod p)) :
    ∃ msg : BusInteraction (ZMod p), msg.busId = 0 ∧ msg.payload = payload ∧
      (openVmBusSemantics p defaultBusMap).maintainsInvariants msg := by
  refine ⟨⟨0, 1, payload⟩, rfl, rfl, ?_⟩
  show ApcOptimizer.OpenVM.maintainsInvariants defaultBusMap
    (⟨0, 1, payload⟩ : BusInteraction (ZMod p))
  rw [ApcOptimizer.OpenVM.maintainsInvariants]
  exact Or.inl rfl

/-- **Memory finalization is `openVmHost`'s exempt chip.** It runs at most once
    (`memoryFinalizeHostChip`'s `instanceBound`), and its own `canProduce` already pins every
    active touch to multiplicity `-1` — nothing else is needed, since `Host.exemptChip` doesn't ask
    for the byte fact `Realizes.lean`'s induction derives instead. -/
theorem openVmHost_finalize_exempt (P : OpenVmParams p) :
    (openVmHost P).exemptChip
      (openVmBusSemantics p defaultBusMap)
      (openVmFinalizeIdx P) where
  bound := Nat.le_refl 1
  uniform := by
    rintro hA hlegal c hc ⟨mb, ml⟩ hst hcm
    have hleg := hlegal.producible _ c hc
    exact (hleg (mb, ml) hcm).2.1

/-- **`openVmHost`'s stateful traffic maintains the bus invariants**, apart from memory
    finalization (`openVmHost_finalize_exempt`). An eight-way split: the four lookup chips pin
    their bus id to a stateless bus, so they cannot touch a stateful message at all; memory
    initialization and the output/input chips each carry byte-valued data limbs, by the
    predicates `OpenVm.lean` states for them; and the connector is on the execution bridge, whose
    invariant is polarity alone.

    Memory initialization is the one genuinely irreducible case: nothing precedes it on the rank
    order to derive it from, so it is still asserted directly. -/
theorem openVmHost_statefulChipsMaintain (P : OpenVmParams p) :
    (openVmHost P).statefulChipsMaintain
      (openVmBusSemantics p defaultBusMap)
      (openVmFinalizeIdx P) := by
  rintro hA hlegal t ht c hc ⟨mb, ml⟩ hst hcm
  have hleg := hlegal.producible t c hc
  fin_cases t
  -- The four lookup chips pin the bus id to a stateless bus.
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hst
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hst
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hst
  · have hbus := (hleg (mb, ml) hcm).1
    subst hbus
    simp [openVmBusSemantics, defaultBusMap, OpenVmBusType.isStateful] at hst
  -- Memory initialization: byte-valued by the chip's own predicate.
  · obtain ⟨hbus, -, f, hf, hbytes, -, -⟩ := hleg (mb, ml) hcm
    subst hbus
    refine memory_maintains (fun f' hf' => ?_)
    rw [hf] at hf'
    cases Option.some.inj hf'
    exact hbytes
  -- Memory finalization: excluded by `ht` — this is exactly the exempt chip.
  · exact absurd rfl ht
  -- Output chip: pinned to an `OutputRead`, whose words are bytes.
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    obtain ⟨hb, hpl⟩ := Prod.mk.injEq .. ▸ heq
    have hbus : mb = 1 := hb ▸ OutputRead.interactions_busId r 1 msg hmsg
    subst hbus
    exact hpl ▸ memory_maintains (hpl ▸ OutputRead.interactions_data r 1 msg hmsg)
  -- Input chip: on the execution bridge (polarity alone, like the connector) or pinned to an
  -- `InputRead`'s memory writes, whose bytes and old words are bytes.
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    obtain ⟨hb, hpl⟩ := Prod.mk.injEq .. ▸ heq
    rcases InputRead.interactions_busId r P.ptrReg 0 1 msg hmsg with h0 | h1
    · have hbus : mb = 0 := hb.symm.trans h0
      subst hbus
      exact hpl ▸ bridge_maintains ml
    · have hbus : mb = 1 := hb.symm.trans h1
      subst hbus
      exact hpl ▸ memory_maintains
        (hpl ▸ InputRead.interactions_data r P.ptrReg 0 1 msg hmsg)
  -- Connector: on the execution bridge, where polarity is the whole invariant.
  · obtain ⟨r, hr⟩ := hleg
    rw [hr] at hcm
    obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hcm
    obtain ⟨hb, -⟩ := Prod.mk.injEq .. ▸ heq
    have hbus : mb = 0 := hb ▸ ConnectorBoundary.interactions_busId r 0 msg hmsg
    subst hbus
    exact bridge_maintains ml

/-- Inverting `defaultBusMap`: the stateless bus ids are exactly the four lookup buses. This is
    what confines a legal `δ` to the buses the lookup chips can absorb. -/
theorem defaultBusMap_stateless {n : Nat} {t : OpenVmBusType}
    (h : defaultBusMap n = some t) (hst : t.isStateful = false) :
    n = 2 ∨ n = 3 ∨ n = 6 ∨ n = 7 := by
  match n with
  | 0 => simp only [defaultBusMap, Option.some.injEq] at h
         subst h; simp [OpenVmBusType.isStateful] at hst
  | 1 => simp only [defaultBusMap, Option.some.injEq] at h
         subst h; simp [OpenVmBusType.isStateful] at hst
  | 2 => tauto
  | 3 => tauto
  | 4 => simp [defaultBusMap] at h
  | 5 => simp [defaultBusMap] at h
  | 6 => tauto
  | 7 => tauto
  | (k+8) => simp [defaultBusMap] at h

/-- Restricting a `BusState` to one bus: a message it leaves nonzero is on that bus, and was
    nonzero to begin with. -/
theorem restrict_ne_zero {δ : BusState p} {b : Nat} {m : BusMessage p}
    (h : (if m.1 = b then δ m else 0) ≠ 0) : m.1 = b ∧ δ m ≠ 0 := by
  by_cases hb : m.1 = b
  · exact ⟨hb, by simpa [hb] using h⟩
  · simp [hb] at h

/-- **`openVmHost` can re-balance a stateless change.** `δ` lives on the four lookup buses, and
    each lookup chip absorbs its own bus's slice of it into what its instances already net: the
    chip's predicate constrains *which* payloads may carry a nonzero net, not what that net is, so
    it is closed under sums (`hadd`, `hsum`). The memory, input and output chips are left
    untouched, which is what carries the observed `VmEffect` across the rebuild. -/
theorem openVmHost_absorbsStateless (P : OpenVmParams p) :
    (openVmHost P).absorbsStateless
      (openVmBusSemantics p defaultBusMap) := by
  intro hA hlegal δ hδ
  -- δ lives on the four lookup buses.
  have hsupp : ∀ m : BusMessage p, δ m ≠ 0 → m.1 = 2 ∨ m.1 = 3 ∨ m.1 = 6 ∨ m.1 = 7 := by
    intro m hm
    obtain ⟨hst, mult, hmult, hacc⟩ := hδ m hm
    have hacc' : ApcOptimizer.OpenVM.accepts defaultBusMap
      (⟨m.1, mult, m.2⟩ : BusInteraction (ZMod p)) := hacc
    rw [ApcOptimizer.OpenVM.accepts] at hacc'
    have hst' : (match defaultBusMap m.1 with
      | some t => t.isStateful | none => false) = false := hst
    match hbm : defaultBusMap m.1 with
    | none => rw [hbm] at hacc'; exact absurd hacc' (by simp)
    | some t => rw [hbm] at hst'; exact defaultBusMap_stateless hbm hst'
  -- A lookup chip's predicate is closed under sums, so one instance can carry what a whole list
  -- of them netted, plus its bus's slice of `δ`.
  have hadd : ∀ (busId : Nat) (accept : List (ZMod p) → Prop) (c r : BusState p),
      (lookupTableHostChip busId accept).canProduce c →
      (lookupTableHostChip busId accept).canProduce r →
      (lookupTableHostChip busId accept).canProduce (c + r) := by
    intro busId accept c r hc hr m hm
    by_cases h : c m = 0
    · exact hr m (by simpa [h] using hm)
    · exact hc m h
  have hsum : ∀ (busId : Nat) (accept : List (ZMod p) → Prop) (l : List (BusState p)),
      (∀ c ∈ l, (lookupTableHostChip busId accept).canProduce c) →
      (lookupTableHostChip busId accept).canProduce l.sum := by
    intro busId accept l
    induction l with
    | nil => intro _ m hm; exact absurd rfl hm
    | cons c l ih =>
      intro hall
      exact hadd busId accept c l.sum (hall c (by simp))
        (ih fun d hd => hall d (by simp [hd]))
  have hsumApply : ∀ (l : List (BusState p)) (m : BusMessage p),
      l.sum m = (l.map (fun c => c m)).sum := by
    intro l m
    induction l with
    | nil => rfl
    | cons c l ih => simp [ih]
  set extra : HostAssignment p (openVmHost P) :=
    fun t =>
    match (t : ℕ) with
    | 0 => [fun m => if m.1 = 2 then δ m else 0]
    | 1 => [fun m => if m.1 = 6 then δ m else 0]
    | 2 => [fun m => if m.1 = 3 then δ m else 0]
    | 3 => [fun m => if m.1 = 7 then δ m else 0]
    | _ => [] with hextra
  -- Each lookup chip is a singleton, so the rebuild pools its instances into one that nets the
  -- same plus its slice; every other chip is left exactly as it was.
  set hA' : HostAssignment p (openVmHost P) :=
    fun t =>
    match (t : ℕ) with
    | 0 => [(hA t).sum + fun m => if m.1 = 2 then δ m else 0]
    | 1 => [(hA t).sum + fun m => if m.1 = 6 then δ m else 0]
    | 2 => [(hA t).sum + fun m => if m.1 = 3 then δ m else 0]
    | 3 => [(hA t).sum + fun m => if m.1 = 7 then δ m else 0]
    | _ => hA t with hA'def
  have key : ∀ b : Nat, ∀ m : BusMessage p,
      (if m.1 = b then δ m else 0) ≠ 0 →
        m.1 = b ∧ ∃ mult : ZMod p, ApcOptimizer.OpenVM.accepts defaultBusMap
          (⟨b, mult, m.2⟩ : BusInteraction (ZMod p)) := by
    intro b m hm
    obtain ⟨hb, hne⟩ := restrict_ne_zero hm
    obtain ⟨-, mult, -, hacc⟩ := hδ m hne
    refine ⟨hb, mult, ?_⟩
    have hacc' : ApcOptimizer.OpenVM.accepts defaultBusMap
      (⟨m.1, mult, m.2⟩ : BusInteraction (ZMod p)) := hacc
    rw [hb] at hacc'
    exact hacc'
  have hslice2 : (pcLookupHostChip (p := p) 2).canProduce
      (fun m => if m.1 = 2 then δ m else 0) := by
    intro m hm
    obtain ⟨hb, mult, hacc⟩ := key 2 m hm
    refine ⟨hb, ?_⟩
    rw [ApcOptimizer.OpenVM.accepts] at hacc
    simp only [defaultBusMap] at hacc
    exact hacc
  have hslice6 : (bitwiseLookupHostChip (p := p) 6).canProduce
      (fun m => if m.1 = 6 then δ m else 0) := by
    intro m hm
    obtain ⟨hb, mult, hacc⟩ := key 6 m hm
    refine ⟨hb, ?_⟩
    rw [ApcOptimizer.OpenVM.accepts] at hacc
    simp only [defaultBusMap] at hacc
    revert hacc
    rcases hml : m.2 with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨op, _ | ⟨w, rest⟩⟩⟩⟩⟩ <;> exact id
  have hslice3 : (variableRangeCheckerHostChip (p := p) 3).canProduce
      (fun m => if m.1 = 3 then δ m else 0) := by
    intro m hm
    obtain ⟨hb, mult, hacc⟩ := key 3 m hm
    refine ⟨hb, ?_⟩
    rw [ApcOptimizer.OpenVM.accepts] at hacc
    simp only [defaultBusMap] at hacc
    revert hacc
    rcases hml : m.2 with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> exact id
  have hslice7 : (tupleRangeCheckerHostChip (p := p) 7 256 2048).canProduce
      (fun m => if m.1 = 7 then δ m else 0) := by
    intro m hm
    obtain ⟨hb, mult, hacc⟩ := key 7 m hm
    refine ⟨hb, ?_⟩
    rw [ApcOptimizer.OpenVM.accepts] at hacc
    simp only [defaultBusMap] at hacc
    revert hacc
    rcases hml : m.2 with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> exact id
  refine ⟨hA', ⟨?_, ?_⟩, ?_, ?_, rfl⟩
  · intro t effect hmem
    fin_cases t <;> simp only [hA'def] at hmem
    · simp at hmem
      subst hmem
      show (pcLookupHostChip (p := p) 2).canProduce _
      exact hadd 2 _ _ _ (hsum 2 _ _ fun c hc => hlegal.producible _ c hc) hslice2
    · simp at hmem
      subst hmem
      show (bitwiseLookupHostChip (p := p) 6).canProduce _
      exact hadd 6 _ _ _ (hsum 6 _ _ fun c hc => hlegal.producible _ c hc) hslice6
    · simp at hmem
      subst hmem
      show (variableRangeCheckerHostChip (p := p) 3).canProduce _
      exact hadd 3 _ _ _ (hsum 3 _ _ fun c hc => hlegal.producible _ c hc) hslice3
    · simp at hmem
      subst hmem
      show (tupleRangeCheckerHostChip (p := p) 7 256 2048).canProduce _
      exact hadd 7 _ _ _ (hsum 7 _ _ fun c hc => hlegal.producible _ c hc) hslice7
    all_goals exact hlegal.producible _ effect hmem
  · -- The pooled lookup chips hold one instance each, which is their whole budget.
    intro t
    fin_cases t
    · exact Nat.le_refl 1
    · exact Nat.le_refl 1
    · exact Nat.le_refl 1
    · exact Nat.le_refl 1
    all_goals exact hlegal.withinBound _
  · funext m
    show (∑ t : Fin 9, ((hA' t).map (fun c => c m)).sum) = hA.busEffect m + δ m
    have hsplit : ∀ t : Fin 9, ((hA' t).map (fun c => c m)).sum
        = ((extra t).map (fun c => c m)).sum + ((hA t).map (fun c => c m)).sum := by
      intro t
      fin_cases t <;> simp [hA'def, hextra, hsumApply, add_comm]
    rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_add_distrib]
    have hhost : (∑ t : Fin 9, ((hA t).map (fun c => c m)).sum) = hA.busEffect m := rfl
    rw [hhost, add_comm ((∑ t : Fin 9, ((extra t).map (fun c => c m)).sum)), add_right_inj]
    -- `Fin.sum_univ_eight` is Mathlib's widest, so peel index `0` first.
    rw [Fin.sum_univ_succ, Fin.sum_univ_eight]
    show (if m.1 = 2 then δ m else 0) + 0
      + (((if m.1 = 6 then δ m else 0) + 0) + ((if m.1 = 3 then δ m else 0) + 0)
        + ((if m.1 = 7 then δ m else 0) + 0) + 0 + 0 + 0 + 0 + 0) = δ m
    by_cases hz : δ m = 0
    · simp [hz]
    · rcases hsupp m hz with h | h | h | h <;> simp [h]
  · -- The only input chip is index `7`, which `hA'` leaves alone.
    intro i hi
    simp only [openVmHost_inputChips, List.mem_singleton] at hi
    subst hi
    rfl

/-- **The rules `OpenVm.lean` writes out are the ones `openVmBusSemantics` induces.** This is the
    only place the two meet: `accepts` and `isStateful` agree definitionally (the former *is* the
    shared function), and `payloadOk` agrees up to naming a multiplicity — on memory, any works and
    the byte condition is the content; elsewhere, the polarity clause is satisfiable and so says
    nothing. -/
theorem openVmGuestRules_eq (busMap : BusMap) (memBusId : Nat)
    (hmem : ∀ b, busMap b = some .memory → b = memBusId := by exact defaultBusMap_mem_unique) :
    openVmGuestRules (p := p) busMap memBusId hmem
      = (openVmBusSemantics p busMap).toGuestRules (openVmGuestRules busMap memBusId hmem)
          (maintainsInvariants_off_mem hmem) := by
  have hpay : ∀ m : BusMessage p, openVmPayloadOk busMap m =
      ∃ mult : ZMod p, ApcOptimizer.OpenVM.maintainsInvariants busMap ⟨m.1, mult, m.2⟩ := by
    intro m
    refine propext ?_
    show openVmPayloadOk busMap m ↔ _
    rw [openVmPayloadOk]
    cases hbm : busMap m.1 with
    | none => simp [ApcOptimizer.OpenVM.maintainsInvariants, hbm]
    | some t =>
      cases t with
      | memory =>
        simp only [ApcOptimizer.OpenVM.maintainsInvariants, hbm]
        constructor
        · exact fun h => ⟨1, Or.inl rfl, h⟩
        · rintro ⟨_, -, h⟩; exact h
      | executionBridge =>
        simp only [ApcOptimizer.OpenVM.maintainsInvariants, hbm]
        exact ⟨fun _ => ⟨1, Or.inl rfl⟩, fun _ => trivial⟩
      | pcLookup | variableRangeChecker | bitwiseLookup | tupleRangeChecker _ _ =>
        simp only [ApcOptimizer.OpenVM.maintainsInvariants, hbm]
        exact ⟨fun _ => ⟨1, rfl⟩, fun _ => trivial⟩
  show GuestBusRules.mk _ _ _ _ _ _ _ = GuestBusRules.mk _ _ _ _ _ _ _
  congr 1
  funext m
  exact hpay m

/-- Off the memory bus, `openVmBusSemantics p defaultBusMap` always has some multiplicity
    maintaining its invariants — `openVmGuestRules_eq`'s own `toGuestRules` argument, named once
    so every downstream `toGuestRules`/`statefulAcceptsOfPayloadOk` call reuses it. -/
def openVmDefaultHmem : ∀ m : BusMessage p,
    (openVmBusSemantics p defaultBusMap).isStateful m.1 = true → m.1 ≠ openVmMemBusId →
      ∃ mult : ZMod p, (openVmBusSemantics p defaultBusMap).maintainsInvariants ⟨m.1, mult, m.2⟩ :=
  maintainsInvariants_off_mem defaultBusMap_mem_unique

/-- Guest legality on `openVmHost` is `Circuit.legalGuest` for OpenVM's bus semantics, with
    `openVmGuestRules defaultBusMap openVmMemBusId` itself as the clock template — so the step
    layout (needed by the rank-ordering argument, `openVmHost_stepLayout_unpack`) is just another
    field of the very same structure, not a separate conjunct to unpack. -/
theorem openVmHost_legalGuest_unpack (P : OpenVmParams p) (c : Circuit p) :
    (openVmHost P).legalGuest c →
      c.legalGuest ((openVmBusSemantics p defaultBusMap).toGuestRules
          (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem)
        (openVmHost P).maxWindow (openVmHost P).maxLookback (openVmHost P).maxInteractions :=
  fun h => openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ h

/-- The temporal contract, which the rank-ordering argument consumes — a field projection now,
    not a separate conjunct. -/
theorem openVmHost_stepLayout_unpack
    (P : OpenVmParams p) (c : Circuit p) :
    (openVmHost P).legalGuest c →
      Circuit.hasStepLayout c (openVmGuestRules defaultBusMap openVmMemBusId) P.maxWindow
        openVmTimestampBound :=
  fun h => h.stepLayout

/-- **`Host.forcesAccepts` for a concrete OpenVM host**, with no hypotheses: in any satisfying
    OpenVM run within the trace budget, every guest instance's assignment is
    `Circuit.satisfies`-good, not merely algebraically consistent. -/
theorem openVmHost_forcesAccepts [Fact p.Prime] (P : OpenVmParams p)
    (hOrd : (openVmHost P).ordersRanks (openVmRankModel openVmMemBusId)
      ((openVmBusSemantics p defaultBusMap).toGuestRules
        (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem)) :
    (openVmHost P).forcesAccepts
      (openVmBusSemantics p defaultBusMap) :=
  forcesAccepts_of_hostSound (openVmHost_legalGuest_unpack P)
    (openVmHost_sinksAreTables P)
    ⟨openVmFinalizeIdx P,
      openVmHost_finalize_exempt P,
      openVmHost_statefulChipsMaintain P⟩
    (openVmBusSemantics_statefulAcceptsOfPayloadOk
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem)
    hOrd

/-- **`openVmHost` realizes OpenVM's bus semantics** — unconditionally. This is the whole VM-side
    obligation of `vmSoundReplacement_of_forall₂`, discharged for a concrete host. -/
theorem openVmHost_realizes (P : OpenVmParams p)
    (hOrd : (openVmHost P).ordersRanks (openVmRankModel openVmMemBusId)
      ((openVmBusSemantics p defaultBusMap).toGuestRules
        (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem)) :
    (openVmHost P).realizes
      (openVmBusSemantics p defaultBusMap) (openVmRankModel openVmMemBusId)
      (openVmGuestRules defaultBusMap openVmMemBusId) where
  hmem := openVmDefaultHmem
  legalGuest := openVmHost_legalGuest_unpack P
  sinksAreTables := openVmHost_sinksAreTables P
  statefulChipsMaintain := ⟨openVmFinalizeIdx P,
    openVmHost_finalize_exempt P,
    openVmHost_statefulChipsMaintain P⟩
  statefulAcceptsOfPayloadOk :=
    openVmBusSemantics_statefulAcceptsOfPayloadOk
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem
  absorbsStateless := openVmHost_absorbsStateless P
  ordersRanks := hOrd

end ApcOptimizer.OpenVM
