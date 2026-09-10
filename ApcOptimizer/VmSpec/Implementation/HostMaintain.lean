import ApcOptimizer.VmSpec.Implementation.HostCounts

set_option autoImplicit false

/-! # What `openVmHost` leaves at a message whose payload might be bad

    `Host.statefulChipsMaintain` for the concrete OpenVM host: at every stateful message, either
    the payload maintains the bus invariants, or the host's whole net there is minus an honest
    count — the pile of receives `maintains_of_stateful_active`'s pigeonhole needs.

    Three things can put a memory record on the bus from the host side, and each is good for its
    own reason: the initial image (byte-valued by `memoryInitHostChip`'s own predicate), an
    input-chip instance's hinted word (`InputRead.byteIsByte`), and an input-chip instance's
    *read echo* — the peeked register written back one tick later. Everything else the host does
    there is a receive, which `openVmHost_memNet_or_sender` counts.

    The echo is why this obligation is stated with the smaller ranks already settled.
    `Rv32HintStoreAir` (`extensions/rv32im/circuit/src/hintstore/mod.rs`) range-checks `data`, the
    hint it writes, and nothing else: not `write_aux.prev_data`, the word it overwrites, and not
    `mem_ptr_limbs`, the pointer register it peeks — of which only the top limb is checked, scaled,
    to bound the pointer. So neither may be asserted of an `InputRead`; byte-ness there is a fact
    about the *run*, and the run supplies it the same way it does for a guest's memory send
    (`StepLayout.memSendsOk`) — the echoed record arrived on the bus at a strictly smaller rank
    (`InputRead.ptrOffsetOk`), where the induction hypothesis already vouches for it. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- The rules `openVmHost`'s soundness argument runs against, named once. -/
abbrev openVmHostRules (p : ℕ) : GuestBusRules p :=
  (openVmBusSemantics p defaultBusMap).toGuestRules
    (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem

--------- `payloadOk`, on the memory bus ---------

/-- **What `payloadOk` says about a memory message**: exactly OpenVM's byte invariant on its data
    limbs. Both directions are used — a send has to produce one, and a read echo moves one from
    the record it received to the record it re-sends. -/
theorem payloadOk_mem_iff {ml : List (ZMod p)} :
    (openVmHostRules p).payloadOk (openVmMemBusId, ml)
      ↔ ∀ f : MemoryPayload p, memoryPayload? ml = some f →
          f.isByteChecked → ∀ d ∈ f.data, isByte d := by
  constructor
  · rintro ⟨mult, hm⟩ f hf hbc d hd
    have hm' : (mult = 1 ∨ mult = -1) ∧
        (match memoryPayload? ml with
          | some f => f.isByteChecked → ∀ d ∈ f.data, isByte d
          | none => True) := hm
    rw [hf] at hm'
    exact hm'.2 hbc d hd
  · intro h
    refine ⟨1, ?_⟩
    show ApcOptimizer.OpenVM.maintainsInvariants defaultBusMap
      (⟨openVmMemBusId, 1, ml⟩ : BusInteraction (ZMod p))
    refine ⟨Or.inl rfl, ?_⟩
    cases hmp : memoryPayload? ml with
    | none => trivial
    | some f => exact fun hbc => h f hmp hbc

/-- **A read echo inherits its payload's goodness from the record it echoes.** `payloadOk` reads
    a memory record's address space and its four data limbs, and a re-send changes neither — only
    the timestamp, and (for a guest's `getPrevious`/`setNew` pair) the pointer never. -/
theorem payloadOk_mem_echo {as ptr ts ts' : ZMod p} {w : Vector (ZMod p) 4}
    (h : (openVmHostRules p).payloadOk (openVmMemBusId, [as, ptr] ++ w.toList ++ [ts])) :
    (openVmHostRules p).payloadOk (openVmMemBusId, [as, ptr] ++ w.toList ++ [ts']) := by
  obtain ⟨a0, a1, a2, a3, hl⟩ : ∃ a0 a1 a2 a3, w.toList = [a0, a1, a2, a3] := by
    have h4 : w.toList.length = 4 := by simp
    match hw : w.toList, h4 with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  rw [hl] at h ⊢
  rw [payloadOk_mem_iff] at h ⊢
  simpa only [List.cons_append, List.nil_append, memoryPayload?, Option.some.injEq,
    forall_eq'] using h

--------- Where an input-chip instance sits on the run's clock ---------

/-- **Every input-chip instance starts at an honest natural timestamp below OpenVM's ceiling**,
    with its witness family fixed alongside — the same chain walk `openVmHost_ordersRanks` runs
    for a guest step (`bridge_chain_bound_input`), and the same family
    `openVmHost_memNet_or_sender` counts with. -/
theorem openVmHost_inputPlaced [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    (hGuests : (openVmHost P).legalGuests G)
    {a : VmAssignment p ⟨openVmHost P, G⟩} (hsat : VmSat ⟨openVmHost P, G⟩ a) :
    ∃ iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p,
      (∀ i, (a.hostAssignment (openVmInputChip P)).get i
          = busStateOf ((iR i).interactions P.ptrReg 0 1)) ∧
      ∀ i, ∃ T : ℕ, (iR i).base = ((1 + T : ℕ) : ZMod p) ∧
        1 + T + inputStepWindow < openVmTimestampBound := by
  classical
  have hp := P.windowOk
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  have hNonempty : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      Nonempty (StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound) :=
    fun x => openVmHost_stepLayout_unpack P _ (hGuests _ (List.get_mem G x.1))
      _ (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
      (satisfiesStateless_of_sinks (openVmHost_legalGuest_unpack P) (openVmHost_sinksAreTables P)
        hGuests hsat x.1 _ (List.get_mem _ _))
  set S : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound :=
    fun x => Classical.choice (hNonempty x) with hS
  obtain ⟨r, iR, hiR, hrnet⟩ := openVmHost_bridge_isolated P hsat.satisfiesHost
  refine ⟨iR, hiR, fun i => ?_⟩
  have hbal : ∀ m : BusMessage p, m.1 = 0 →
      a.guestAssignments.busEffect m +
        (∑ j, busStateOf ((iR j).interactions P.ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0 := by
    intro m hm
    have hb := hsat.balances m
    rw [busEffect_apply, hrnet m hm] at hb
    linear_combination hb
  have hcount : (∑ s : Fin G.length, (a.guestAssignments s).length) ≤ P.maxInstances :=
    hsat.withinBudget
  have hcountI : (a.hostAssignment (openVmInputChip P)).length ≤ P.maxInputInstances :=
    hsat.satisfiesHost.withinBound (openVmInputChip P)
  obtain ⟨T, hbase, hfit⟩ :=
    bridge_chain_bound_input a.guestAssignments S iR P.ptrReg r (openVm_negOne_ne_one P) hbal
      P.inputWindowOk hcount hcountI hp i
  exact ⟨T, hbase, by have := r.finalTimestampBounded; omega⟩

--------- The read echo ---------

/-- The record an input-chip instance peeks the pointer register from. Its echo — the same word
    at `base + 1` — is `InputRead.interactions`' fourth entry. -/
def InputRead.ptrRecvMsg (r : InputRead p) (ptrReg : Nat) : BusMessage p :=
  ((1 : Nat), [1, (ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime])

/-- **An instance's own peek is a message it actively touches.** Its five other interactions miss
    it: two sit on the execution bridge, two carry address space `2`, and the echo carries the
    same word at `base + 1`, a timestamp `InputRead.ptrOffsetOk` keeps the peek strictly below. -/
theorem inputRead_ptrRecv_net [Fact p.Prime] (P : OpenVmParams p) (r : InputRead p) :
    busStateOf (r.interactions P.ptrReg 0 1) (r.ptrRecvMsg P.ptrReg) = -1 := by
  have hp2 : 2 < p := lt_trans (by norm_num [openVmRankBound, openVmRankShift,
    openVmTimestampBound, openVmTimestampBits]) (openVmRankBound_lt P)
  haveI : NeZero p := ⟨by omega⟩
  -- The word this instance overwrites lives in address space `2`, not the register's `1`.
  have has : ((2 : ZMod p)) ≠ 1 := fun h =>
    absurd (by linear_combination h : (1 : ZMod p) = 0) one_ne_zero
  -- The peek is strictly before the write-back that echoes it (`InputRead.ptrOffsetOk`).
  have hbnd : (openVmTimestampBound : ℤ) = 536870912 := by
    norm_num [openVmTimestampBound, openVmTimestampBits]
  have hlow := r.ptrOffsetOk.1
  have hhigh := r.ptrOffsetOk.2
  have htime : r.base + 1 ≠ r.ptrTime := by
    intro h
    have hcast : ((r.ptrOffset : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
      rw [r.ptrTimeMatch] at h
      push_cast
      linear_combination -h
    have := intCast_inj_window P hlow (by omega) (by omega) (by omega) hcast
    omega
  rw [InputRead.ptrRecvMsg, InputRead.interactions]
  simp only [busStateOf_cons, busStateOf_nil, Prod.mk.injEq, List.cons_append, List.nil_append,
    List.cons.injEq]
  rw [if_neg (by simp), if_neg (by simp), if_pos trivial, if_neg (by simp [htime]),
    if_neg (by simp [has]), if_neg (by simp [has])]
  ring

/-- **The peek sits at a strictly smaller rank than the echo it feeds.** Both timestamps are
    `base` plus a fixed offset, the chain puts `base` at an honest natural low enough that neither
    wraps, and `InputRead.ptrOffsetOk` is what makes the peek's offset the smaller one. -/
theorem inputRead_echo_rank_lt [Fact p.Prime] (P : OpenVmParams p) (r : InputRead p) {T : ℕ}
    (hbase : r.base = ((1 + T : ℕ) : ZMod p))
    (hfit : 1 + T + inputStepWindow < openVmTimestampBound) :
    openVmRank openVmMemBusId (r.ptrRecvMsg P.ptrReg)
      < openVmRank openVmMemBusId
          ((1 : Nat), [1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1]) := by
  have hlen : r.ptrLimbs.toList.length = 4 := by simp
  have hstep : inputStepWindow = 3 := rfl
  have hlow := r.ptrOffsetOk.1
  have hhigh := r.ptrOffsetOk.2
  have hrecv := rank_of_placed (p := p) (memBusId := openVmMemBusId)
    (m := r.ptrRecvMsg P.ptrReg) (T := T) (off := r.ptrOffset) (d := 1)
    (openVmRankBound_lt P) (Or.inl rfl) hlow (by omega) (by omega) (by
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime])[6]?.getD 0 = _
      rw [show ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.ptrTime])[6]?
        = some r.ptrTime by simp [hlen], Option.getD_some, r.ptrTimeMatch, hbase])
  have hsend := rank_of_placed (p := p) (memBusId := openVmMemBusId)
    (m := ((1 : Nat), [1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1]))
    (T := T) (off := 1) (d := 1) (openVmRankBound_lt P) (Or.inl rfl)
    (by norm_num [openVmTimestampBound, openVmTimestampBits]) (by norm_num) (by omega) (by
      show (if (1 : Nat) = openVmMemBusId then _ else _) = _
      rw [if_pos rfl]
      show ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[6]?.getD 0 = _
      rw [show ([1, (P.ptrReg : ZMod p)] ++ r.ptrLimbs.toList ++ [r.base + 1])[6]?
        = some (r.base + 1) by simp [hlen], Option.getD_some, hbase]
      push_cast
      ring)
  omega

--------- The obligation ---------

/-- **A record an input-chip instance sends carries byte-valued limbs.** Two sends
    (`InputRead.interactions`): the hinted word at `base + 2`, whose limbs are the range-checked
    hint and three zeros (`InputRead.byteIsByte` — the one byte check `Rv32HintStoreAir` makes),
    and the peeked register written back at `base + 1`, which is an *echo* of the record the
    instance received at `ptrTime`. Nothing constrains those limbs; what vouches for them is that
    record's own arrival on the bus, at a strictly smaller rank. -/
theorem openVmHost_inputSend_payloadOk [Fact p.Prime] (P : OpenVmParams p) {G : Guest p}
    {a : VmAssignment p ⟨openVmHost P, G⟩}
    {iR : Fin (a.hostAssignment (openVmInputChip P)).length → InputRead p}
    (hiR : ∀ i, (a.hostAssignment (openVmInputChip P)).get i
        = busStateOf ((iR i).interactions P.ptrReg 0 1))
    {i : Fin (a.hostAssignment (openVmInputChip P)).length} {T : ℕ}
    (hbase : (iR i).base = ((1 + T : ℕ) : ZMod p))
    (hfit : 1 + T + inputStepWindow < openVmTimestampBound)
    {m : BusMessage p} (hmb : m.1 = openVmMemBusId)
    (hIH : ∀ m' : BusMessage p, (openVmBusSemantics p defaultBusMap).isStateful m'.1 = true →
      (openVmRankModel openVmMemBusId).rank m' < (openVmRankModel openVmMemBusId).rank m →
      a.activeAt m' → (openVmHostRules p).payloadOk m')
    {e : BusInteraction (ZMod p)} (he : e ∈ (iR i).interactions P.ptrReg 0 1)
    (heq : (e.busId, e.payload) = m) (hmult : e.multiplicity = 1) :
    (openVmHostRules p).payloadOk m := by
  rw [InputRead.interactions] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hmult (openVm_negOne_ne_one P)
  · exact absurd (heq ▸ hmb : ((0 : Nat), _).1 = openVmMemBusId) (by simp [openVmMemBusId])
  · exact absurd hmult (openVm_negOne_ne_one P)
  · -- The pointer register's write-back: an echo of the peek, which precedes it.
    subst heq
    refine payloadOk_mem_echo (ts := (iR i).ptrTime) (hIH ((iR i).ptrRecvMsg P.ptrReg) rfl ?_ ?_)
    · exact inputRead_echo_rank_lt P (iR i) hbase hfit
    · exact Or.inr ⟨openVmInputChip P, (a.hostAssignment (openVmInputChip P)).get i,
        List.get_mem _ _, by
          rw [hiR i, inputRead_ptrRecv_net P (iR i)]
          exact neg_ne_zero.mpr one_ne_zero⟩
  · exact absurd hmult (openVm_negOne_ne_one P)
  · -- The hinted word: `Rv32HintStoreAir`'s own range check, plus three padding zeros.
    subst heq
    refine payloadOk_mem_iff.mpr (fun f hf _ d hd => ?_)
    simp only [memoryPayload?, Option.some.injEq] at hf
    subst hf
    simp at hd
    rcases hd with rfl | rfl
    · exact (iR i).byteIsByte
    · exact isByte_zero

/-- **`openVmHost` meets `Host.statefulChipsMaintain`.** Off the memory bus OpenVM's invariant is
    polarity alone. On it, three things can send: the initial image, whose records are byte-valued
    by `memoryInitHostChip`'s own predicate, and an input-chip instance's two sends
    (`openVmHost_inputSend_payloadOk`). Failing all three, every host touch is a receive, and
    `openVmHost_memNet_or_sender` names their count — at most one from memory finalization and six
    per input-chip instance, which `OpenVmParams.budgetOk` budgets alongside the guests' own. -/
theorem openVmHost_statefulChipsMaintain [Fact p.Prime] (P : OpenVmParams p) :
    (openVmHost P).statefulChipsMaintain (openVmBusSemantics p defaultBusMap)
      (openVmRankModel openVmMemBusId)
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem := by
  rintro G hGuests a hsat ⟨mb, ml⟩ hst hIH
  by_cases hmb : mb = openVmMemBusId
  case neg => exact Or.inl ((openVmHostRules p).memPayloadOnly (mb, ml) hst hmb)
  subst hmb
  obtain ⟨iR, hiR, hplaced⟩ := openVmHost_inputPlaced P hGuests hsat
  -- The initial memory image sends only byte-valued records.
  by_cases hinit : ∃ e ∈ a.hostAssignment (openVmMemInitChip P), e (openVmMemBusId, ml) ≠ 0
  · obtain ⟨e, he, hem⟩ := hinit
    obtain ⟨-, -, f, hf, hbytes, -, -⟩ :=
      (hsat.satisfiesHost.producible (openVmMemInitChip P) e he).1 (openVmMemBusId, ml) hem
    exact Or.inl (payloadOk_mem_iff.mpr (fun f' hf' _ => by
      rw [hf] at hf'; cases Option.some.inj hf'; exact hbytes))
  have hinit' : ∀ e ∈ a.hostAssignment (openVmMemInitChip P), e (openVmMemBusId, ml) = 0 := by
    intro e he
    by_contra hc
    exact hinit ⟨e, he, hc⟩
  rcases openVmHost_memNet_or_sender P hsat.satisfiesHost iR hiR (rfl : (openVmMemBusId, ml).1 = _)
    with ⟨e, he, hem⟩ | ⟨i, e, he, heq, hmult⟩ | ⟨kf, ki, hkf, hki, hnet, hz1, hz2, hz3⟩
  · exact absurd (hinit' e he) hem
  · obtain ⟨T, hbase, hfit⟩ := hplaced i
    exact Or.inl (openVmHost_inputSend_payloadOk P hiR hbase hfit rfl hIH he heq hmult)
  · refine Or.inr ⟨kf + ki, ?_, hnet, fun hk t c hc => ?_⟩
    · have := P.budgetOk
      show P.maxInteractions * P.maxInstances + (kf + ki) < p
      omega
    · by_cases h5 : (t : ℕ) = 5
      · exact hz1 (by omega) c (by rwa [show t = openVmMemFinalizeChip P from Fin.ext h5] at hc)
      by_cases h6 : (t : ℕ) = 6
      · have ht : t = openVmInputChip P := Fin.ext h6
        rw [ht] at hc
        obtain ⟨j, hj⟩ := List.get_of_mem hc
        rw [← hj, hiR j]
        by_contra hne
        obtain ⟨msg, hmsg, heq⟩ := exists_of_busStateOf_ne_zero hne
        exact hz2 (by omega) j msg hmsg heq
      · exact hz3 t h5 h6 c hc

/-- **`Host.forcesAccepts` for a concrete OpenVM host**, with no hypotheses: in any satisfying
    OpenVM run within the trace budget, every guest instance's assignment is
    `Circuit.satisfies`-good, not merely algebraically consistent. -/
theorem openVmHost_forcesAccepts [Fact p.Prime] (P : OpenVmParams p) :
    (openVmHost P).forcesAccepts (openVmBusSemantics p defaultBusMap) :=
  forcesAccepts_of_hostSound (openVmHost_legalGuest_unpack P)
    (openVmHost_sinksAreTables P)
    (openVmHost_statefulChipsMaintain P)
    (openVmBusSemantics_statefulAcceptsOfPayloadOk
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem)
    (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P)

end ApcOptimizer.OpenVM
