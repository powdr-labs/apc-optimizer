import ApcOptimizer.VmSpec.Implementation.Chain
import ApcOptimizer.VmSpec.Implementation.OpenVmConnection

set_option autoImplicit false

/-! **`Host.ordersRanks` for `openVmHost`**: every timestamp in a satisfying run is inside OpenVM's
    rank window. Nothing here is audited.

    The run's execution-bridge traffic is read as a `VmChain.Chain` (`Chain.lean`): one arc per
    realized guest instance, consuming the `(pc, t)` it receives and producing the `(pc', t + d)`
    it sends — `StepLayout`'s `bridgeRecv`/`bridgeSend`, which `openVmHost.legalGuest` requires; one arc per
    realized input-chip instance, doing exactly the same (`InputRead.pcFrom`/`pcTo` — the
    input chip is an instruction executor too, whitepaper §4.5); plus one arc for the connector,
    which produces `(pc₀, 1)` and consumes the segment's final state. Bus balance on bus `0` is
    exactly the chain's `balanced` field, once the multiplicities are counted as naturals rather
    than field elements.

    The chain then places every instance at a known distance before the connector, so its start
    timestamp is `1 + T` for an honest natural `T` and the whole instruction fits below the final
    timestamp — which `ConnectorBoundary.finalTimestampBounded` range-checks. Every memory access
    of a *guest* instance sits in its own step's window, `[-maxLookback, d]` (`StepLayout.tOffsetMatch`
    again), so it inherits the bound; nothing here claims the same for an input-chip instance's own
    memory accesses, since `Host.ordersRanks` only bounds guest ranks.

    The one arithmetic input is `OpenVmParams.windowOk` — a field of the host's own configuration,
    not a hypothesis of the theorem below: a run too long to fit in the field could wrap, and then
    "the timestamp went up" would stop meaning anything. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

--------- One instance's clock witness ---------

--------- Guest nets as sums over instances ---------

/-- `(l.map f).sum` as a `Finset` sum over positions — what turns `GuestAssignment.busEffect`'s
    lists into a sum over a `Fintype` of instances. -/
theorem list_map_sum_eq_sum_fin {α β : Type} [AddCommMonoid β] (l : List α) (f : α → β) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, ih]; simp [Fin.sum_univ_succ]

/-- The guests' net contribution to a message, indexed by instance rather than by chip type. -/
theorem guestNet_eq_sum_inst {G : Guest p} (gA : GuestAssignment p G)
    (m : BusMessage p) :
    gA.busEffect m = ∑ x : ((s : Fin G.length) × Fin (gA s).length),
      (G.get x.1).allEffects ((gA x.1).get x.2) m := by
  conv_rhs => rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  exact Finset.sum_congr rfl (fun s _ => list_map_sum_eq_sum_fin (gA s) _)

--------- The connector is alone on the execution bridge ---------

/-- The connector's contribution, message by message: it produces its initial state and consumes
    its final one. -/
theorem connector_busStateOf (r : ConnectorBoundary p) (m : BusMessage p) :
    busStateOf (r.interactions 0) m
      = (if ((0 : Nat), [r.initialPc, (1 : ZMod p)]) = m then (1 : ZMod p) else 0)
        - (if ((0 : Nat), [r.finalPc, r.finalTimestamp]) = m then (1 : ZMod p) else 0) := by
  simp only [busStateOf, ConnectorBoundary.interactions, List.filter_cons, List.filter_nil]
  by_cases h1 : ((0 : Nat), [r.initialPc, (1 : ZMod p)]) = m <;>
    by_cases h2 : ((0 : Nat), [r.finalPc, r.finalTimestamp]) = m <;>
    simp [h1, h2]

/-- `busStateOf` distributes over list append: filtering, mapping and summing all do. -/
theorem busStateOf_append (l1 l2 : List (BusInteraction (ZMod p))) (m : BusMessage p) :
    busStateOf (l1 ++ l2) m = busStateOf l1 m + busStateOf l2 m := by
  simp [busStateOf, List.filter_append, List.map_append, List.sum_append]

/-- A list none of whose entries carry `m`'s bus id contributes nothing to `m`. -/
theorem busStateOf_eq_zero_of_busId_ne {l : List (BusInteraction (ZMod p))} {m : BusMessage p}
    (h : ∀ e ∈ l, e.busId ≠ m.1) : busStateOf l m = 0 := by
  simp only [busStateOf]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  exact absurd (congrArg Prod.fst (of_decide_eq_true hy2)) (h y hy1)

/-- **An `InputRead`'s contribution, restricted to the execution bridge**: `-1` at the state it
    consumes, `1` at the one it produces, `0` elsewhere — every other interaction it describes is
    on the memory bus, never the bridge (`InputRead.interactions_busId`). Mirrors
    `connector_busStateOf`, since an input-chip instance shares that same bus
    (`InputRead.pcFrom`/`pcTo`, whitepaper §4.5). -/
theorem inputRead_busStateOf_execBus (r : InputRead p) (ptrReg : Nat) (m : BusMessage p)
    (hm : m.1 = 0) :
    busStateOf (r.interactions ptrReg 0 1) m
      = (if ((0 : Nat), [r.pcTo, r.base + (inputStepWindow : ZMod p)]) = m then (1 : ZMod p)
          else 0)
        - (if ((0 : Nat), [r.pcFrom, r.base]) = m then (1 : ZMod p) else 0) := by
  rw [InputRead.interactions]
  simp only [busStateOf, List.filter_cons, List.filter_nil]
  by_cases h1 : ((0 : Nat), [r.pcFrom, r.base]) = m <;>
    by_cases h2 : ((0 : Nat), [r.pcTo, r.base + (inputStepWindow : ZMod p)]) = m <;>
    simp [h1, h2, hm, Prod.ext_iff]

/-- **Only the connector and the input chip touch the execution bridge.** The four lookup chips
    pin their bus id to a lookup bus and the four other memory-bus chips to memory, so on bus `0`
    the host's whole net is the connector's plus every realized input-chip instance's own bridge
    step (`InputRead.pcFrom`/`pcTo`, `inputStepWindow`) — the input chip is an instruction executor like any
    other guest, just one the host runs instead of the trace's own program. The connector runs at
    most once, so there is a single witness to name; a segment that leaves it out nets nothing on
    the bridge, which is what the degenerate boundary (start and end state equal) describes, so
    the walk below need not know which case it is in. -/
theorem openVmHost_bridge_isolated (P : OpenVmParams p)
    {hA : HostAssignment p (openVmHost P)}
    (hlegal : hA.satisfies) :
    ∃ (r : ConnectorBoundary p) (iR : Fin (hA (openVmInputChip P)).length → InputRead p),
      (∀ i, (hA (openVmInputChip P)).get i
          = busStateOf ((iR i).interactions P.ptrReg 0 1)) ∧
      ∀ m : BusMessage p, m.1 = 0 →
        hA.busEffect m = busStateOf (r.interactions 0) m +
          ∑ i, busStateOf ((iR i).interactions P.ptrReg 0 1) m := by
  classical
  -- The connector's single instance.
  have hconnIdx : (openVmHost P).chips.length = 8 :=
    rfl
  set k : Fin (openVmHost P).chips.length :=
    ⟨7, by rw [hconnIdx]; omega⟩ with hk
  have hlen : (hA k).length ≤ 1 := hlegal.withinBound k
  obtain ⟨r, hr⟩ : ∃ r : ConnectorBoundary p, ∀ m : BusMessage p,
      ((hA k).map (fun effect => effect m)).sum = busStateOf (r.interactions 0) m := by
    match hc : hA k, hlen with
    | [], _ =>
      -- `windowOk` is what says the field is not the degenerate one, so `1` is a real timestamp.
      have hp1 : 1 < p :=
        lt_of_le_of_lt (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
          P.windowOk
      haveI : NeZero p := ⟨by omega⟩
      haveI : Fact (1 < p) := ⟨hp1⟩
      refine ⟨⟨0, 0, 1, ?_⟩, fun m => ?_⟩
      · rw [ZMod.val_one]
        norm_num [openVmTimestampBound, openVmTimestampBits]
      · simp [connector_busStateOf]
    | [c], _ =>
      obtain ⟨r, hr⟩ : (connectorHostChip (p := p) 0).canProduce c :=
        hlegal.producible k c (by rw [hc]; exact List.mem_singleton_self c)
      exact ⟨r, fun m => by rw [hr]; simp⟩
  -- The input chip's own instances, each pinned to an `InputRead` witness.
  set j : Fin (openVmHost P).chips.length := openVmInputChip P with hj
  have hchoice : ∀ i : Fin (hA j).length,
      ∃ r : InputRead p, (hA j).get i = busStateOf (r.interactions P.ptrReg 0 1) :=
    fun i => hlegal.producible j ((hA j).get i) (List.get_mem (hA j) i)
  set iR : Fin (hA j).length → InputRead p := fun i => (hchoice i).choose with hiRdef
  have hiReq : ∀ i, (hA j).get i = busStateOf ((iR i).interactions P.ptrReg 0 1) :=
    fun i => (hchoice i).choose_spec
  refine ⟨r, iR, hiReq, fun m hm => ?_⟩
  have hj_ne_k : j ≠ k := by
    intro h
    have hjv : (j : ℕ) = 6 := rfl
    have hkv : (k : ℕ) = 7 := by rw [hk]
    rw [h, hkv] at hjv
    omega
  -- Every other chip leaves bus `0` alone.
  have hzero :
      ∀ t : Fin (openVmHost P).chips.length,
      (t : ℕ) ≠ 7 → (t : ℕ) ≠ 6 → ∀ c' ∈ hA t, c' m = 0 := by
    intro t ht ht7 c' hc'
    have hleg := hlegal.producible t c' hc'
    by_contra hne
    fin_cases t
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; omega)
    · exact absurd (hleg.1 m hne).1 (by rw [hm]; simp only [openVmMemBusId]; omega)
    · exact absurd (hleg m hne).1 (by rw [hm]; simp only [openVmMemBusId]; omega)
    · exact absurd rfl ht7
    · exact absurd rfl ht
  have hz : ∀ t : Fin (openVmHost P).chips.length,
      (t : ℕ) ≠ 7 → (t : ℕ) ≠ 6 → ((hA t).map (fun effect => effect m)).sum = 0 := by
    intro t ht ht7
    refine List.sum_eq_zero (fun v hv => ?_)
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hv
    exact hzero t ht ht7 c' hc'
  have hnet : hA.busEffect m
      = ∑ t : Fin (openVmHost P).chips.length,
        ((hA t).map (fun effect => effect m)).sum := rfl
  have hsum9 : (∑ t : Fin (openVmHost P).chips.length, ((hA t).map (fun effect => effect m)).sum)
      = ∑ t ∈ ({j, k} : Finset (Fin (openVmHost P).chips.length)),
          ((hA t).map (fun effect => effect m)).sum := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro t _ ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact hz t (fun h => ht.2 (Fin.ext h)) (fun h => ht.1 (Fin.ext h))
  have hinput : ((hA j).map (fun effect => effect m)).sum
      = ∑ i : Fin (hA j).length, busStateOf ((iR i).interactions P.ptrReg 0 1) m := by
    rw [list_map_sum_eq_sum_fin]
    exact Finset.sum_congr rfl (fun i _ => by rw [hiReq i])
  rw [hnet, hsum9, Finset.sum_pair hj_ne_k, hinput, hr]
  ring

/-- `-1 ≠ 1` in `ZMod p`, from the rank window: `OpenVmParams.rankWindowOk` puts `2 ^ 30` below
    `p`. `StepLayout.net` needs it — a step whose two bridge endpoints coincided would have to net
    both `-1` and `1` there. -/
theorem openVm_negOne_ne_one (P : OpenVmParams p) : (-1 : ZMod p) ≠ 1 := by
  have hlt : 2 < p :=
    lt_trans (by norm_num [openVmRankBound, openVmRankShift, openVmTimestampBound,
      openVmTimestampBits]) P.rankWindowOk
  haveI : NeZero p := ⟨by omega⟩
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have h' := congrArg (fun x : ZMod p => x + 1) h
    simp only [neg_add_cancel] at h'
    rw [show (2 : ZMod p) = 1 + 1 by norm_num, ← h']
  have hval : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_cast_of_lt hlt
  rw [show ((2 : ℕ) : ZMod p) = (2 : ZMod p) by push_cast; ring, h2, ZMod.val_zero] at hval
  omega

/-- What a step puts on the execution bridge: `1` at the state it produces, `-1` at the state it
    consumes. Reads only `pcFrom`, `pcTo`, `base` and `d`, and is only ever used against
    `openVm_negOne_ne_one`'s `h2` below — it is not part of what `Circuit.legalGuest` means, only
    a convenience for restating `StepLayout.net` as one equation. -/
def _root_.StepLayout.effect {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
    {memAddress : BusMessage p → List (Option (ZMod p))} {maxWindow maxLookback : ℕ}
    (L : StepLayout c r asg memAddress maxWindow maxLookback)
    (m : BusMessage p) : ZMod p :=
  (if (r.execBusId, [L.pcTo, L.tStart + (L.tWindow : ZMod p)]) = m then (1 : ZMod p) else 0)
    - (if (r.execBusId, [L.pcFrom, L.tStart]) = m then (1 : ZMod p) else 0)

/-- A step's two bridge endpoints are distinct: were they equal, `recv` and `send` would make the
    same net both `-1` and `1`. -/
theorem _root_.StepLayout.endpoints_ne {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
    {memAddress : BusMessage p → List (Option (ZMod p))} {maxWindow maxLookback : ℕ}
    (L : StepLayout c r asg memAddress maxWindow maxLookback)
    (h2 : (-1 : ZMod p) ≠ 1) :
    ((r.execBusId, [L.pcFrom, L.tStart]) : BusMessage p)
      ≠ (r.execBusId, [L.pcTo, L.tStart + (L.tWindow : ZMod p)]) := by
  intro h
  have hr := L.bridgeRecv
  rw [h, L.bridgeSend] at hr
  exact h2 hr.symm

/-- **A step's bridge net is exactly what it puts there.** The `recv`/`send`/`other` triple
    repackaged as a single equation, which is the form the bridge-balance argument below
    consumes. -/
theorem _root_.StepLayout.net {c : Circuit p} {r : GuestBusRules p} {asg : ChipAssignment p}
    {memAddress : BusMessage p → List (Option (ZMod p))} {maxWindow maxLookback : ℕ}
    (L : StepLayout c r asg memAddress maxWindow maxLookback)
    (h2 : (-1 : ZMod p) ≠ 1) :
    ∀ m : BusMessage p, m.1 = r.execBusId → c.allEffects asg m = L.effect m := by
  intro m hm
  simp only [StepLayout.effect]
  by_cases hd : ((r.execBusId, [L.pcTo, L.tStart + (L.tWindow : ZMod p)]) : BusMessage p) = m <;>
    by_cases hs : ((r.execBusId, [L.pcFrom, L.tStart]) : BusMessage p) = m
  · exact absurd (hs.trans hd.symm) (L.endpoints_ne h2)
  · rw [if_pos hd, if_neg hs, sub_zero, ← hd]; exact L.bridgeSend
  · rw [if_neg hd, if_pos hs, zero_sub, ← hs]; exact L.bridgeRecv
  · rw [if_neg hd, if_neg hs, sub_zero]
    exact L.bridgeNoOther m hm (fun h => hs h.symm) (fun h => hd h.symm)

--------- The bridge as a chain ---------

section Bridge

variable {G : Guest p} {maxWindow : ℕ}

/-- A realized guest instance, which is one instruction step. -/
abbrev GuestArc (gA : GuestAssignment p G) : Type :=
  (s : Fin G.length) × Fin (gA s).length

/-- The arcs of a run's execution bridge: one per realized guest instance, one per realized
    input-chip instance — an input-chip instance is an instruction executor sharing the same bus
    (`InputRead.pcFrom`/`pcTo`, whitepaper §4.5) — plus the connector (`none`). -/
abbrev BridgeArc (gA : GuestAssignment p G) (n : ℕ) : Type :=
  Option (GuestArc gA ⊕ Fin n)

variable (gA : GuestAssignment p G) {n : ℕ}
  (S : ∀ x : ((s : Fin G.length) × Fin (gA s).length),
      StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((gA x.1).get x.2) openVmMemAddress maxWindow openVmTimestampBound)
  (iR : Fin n → InputRead p) (ptrReg : Nat)
  (r : ConnectorBoundary p)

/-- The bridge state an arc consumes: an instruction's incoming `(pc, t)` (guest or input-chip
    instance alike), or, for the connector, the segment's final state. -/
def bridgeSrc : BridgeArc gA n → BusMessage p
  | none => (0, [r.finalPc, r.finalTimestamp])
  | some (.inl y) => (0, [(S y).pcFrom, (S y).tStart])
  | some (.inr i) => (0, [(iR i).pcFrom, (iR i).base])

/-- The bridge state an arc produces: an instruction's outgoing `(pc, t + d)`, or, for the
    connector, the segment's initial state at timestamp `1`. -/
def bridgeDst : BridgeArc gA n → BusMessage p
  | none => (0, [r.initialPc, 1])
  | some (.inl y) =>
    (0, [(S y).pcTo, (S y).tStart + ((S y).tWindow : ZMod p)])
  | some (.inr i) => (0, [(iR i).pcTo, (iR i).base + (inputStepWindow : ZMod p)])

/-- How far an arc advances the clock; the connector does not. -/
def bridgeAdv : BridgeArc gA n → ℕ
  | none => 0
  | some (.inl y) => (S y).tWindow
  | some (.inr _) => inputStepWindow

theorem bridgeSrc_busId (e : BridgeArc gA n) : (bridgeSrc gA S iR r e).1 = 0 := by
  cases e with
  | none => rfl
  | some e' => cases e' <;> rfl

theorem bridgeDst_busId (e : BridgeArc gA n) : (bridgeDst gA S iR r e).1 = 0 := by
  cases e with
  | none => rfl
  | some e' => cases e' <;> rfl

/-- The arcs are the guest instances, the input-chip instances, and one. -/
theorem card_bridgeArc :
    Fintype.card (BridgeArc gA n) = (∑ s : Fin G.length, (gA s).length) + n + 1 := by
  rw [Fintype.card_option, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  simp

/-- **Bus balance on the execution bridge, counted honestly.** Every bridge state is consumed
    exactly as often as it is produced.

    `VmSat` only gives an equation in `ZMod p`; what makes it an equation between *counts* is the
    instance budget, which keeps both counts below `p`. Off bus `0` there is nothing to say: no arc
    touches another bus. -/
theorem bridge_balanced {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) (m : BusMessage p) :
    (Finset.univ.filter fun e => bridgeSrc gA S iR r e = m).card
      = (Finset.univ.filter fun e => bridgeDst gA S iR r e = m).card := by
  classical
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  by_cases hm : m.1 = 0
  swap
  · have h1 : (Finset.univ.filter fun e => bridgeSrc gA S iR r e = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun {e} _ h => hm ?_)
      rw [← h]; exact bridgeSrc_busId gA S iR r e
    have h2 : (Finset.univ.filter fun e => bridgeDst gA S iR r e = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun {e} _ h => hm ?_)
      rw [← h]; exact bridgeDst_busId gA S iR r e
    rw [h1, h2]
  -- The field equation, arc by arc.
  have hsplit : ∑ e : BridgeArc gA n,
      ((if bridgeDst gA S iR r e = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S iR r e = m then (1 : ZMod p) else 0)) = 0 := by
    -- One arc's indicator difference is literally its own effect.
    have hsome : ∀ y : GuestArc gA,
        (if bridgeDst gA S iR r (some (.inl y)) = m then (1 : ZMod p) else 0)
          - (if bridgeSrc gA S iR r (some (.inl y)) = m then (1 : ZMod p) else 0)
        = (S y).effect m := fun _ => rfl
    -- …and an instance's step is its net (`StepLayout.net`).
    have hguest : ∑ y : GuestArc gA, (S y).effect m
        = ∑ x : ((s : Fin G.length) × Fin (gA s).length),
            (G.get x.1).allEffects ((gA x.1).get x.2) m :=
      Finset.sum_congr rfl (fun x _ => ((S x).net h2 m hm).symm)
    have hsome_input : ∀ i : Fin n,
        (if bridgeDst gA S iR r (some (.inr i)) = m then (1 : ZMod p) else 0)
          - (if bridgeSrc gA S iR r (some (.inr i)) = m then (1 : ZMod p) else 0)
          = busStateOf ((iR i).interactions ptrReg 0 1) m :=
      fun i => (inputRead_busStateOf_execBus (iR i) ptrReg m hm).symm
    have hnone : (if bridgeDst gA S iR r none = m then (1 : ZMod p) else 0)
        - (if bridgeSrc gA S iR r none = m then (1 : ZMod p) else 0)
        = busStateOf (r.interactions 0) m := (connector_busStateOf r m).symm
    rw [Fintype.sum_option, Fintype.sum_sum_type, hnone,
      Finset.sum_congr rfl (fun y _ => hsome y), hguest,
      Finset.sum_congr rfl (fun i _ => hsome_input i), ← guestNet_eq_sum_inst]
    linear_combination hbal m hm
  -- Both counts are below `p`, so it is an equation between naturals.
  have hcard : ∀ f : BridgeArc gA n → BusMessage p,
      ((Finset.univ.filter fun e => f e = m).card : ZMod p)
        = ∑ e : BridgeArc gA n, (if f e = m then (1 : ZMod p) else 0) := by
    intro f
    rw [Finset.card_filter]
    push_cast
    simp
  have hbound : ∀ f : BridgeArc gA n → BusMessage p,
      (Finset.univ.filter fun e => f e = m).card < p := by
    intro f
    refine lt_of_le_of_lt (Finset.card_filter_le _ _) ?_
    rw [Finset.card_univ, card_bridgeArc]
    have hfit : maxInstances + maxInputInstances + 1
        ≤ (maxInstances + maxInputInstances + 1) * (maxWindow + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  have heq : ((Finset.univ.filter fun e => bridgeSrc gA S iR r e = m).card : ZMod p)
      = ((Finset.univ.filter fun e => bridgeDst gA S iR r e = m).card : ZMod p) := by
    rw [hcard, hcard, Finset.sum_sub_distrib] at *
    exact (sub_eq_zero.mp hsplit).symm
  have h1 := ZMod.val_cast_of_lt (hbound (bridgeSrc gA S iR r))
  rw [heq, ZMod.val_cast_of_lt (hbound (bridgeDst gA S iR r))] at h1
  exact h1.symm

theorem bridge_advPos : ∀ e : BridgeArc gA n, e ≠ none → 0 < bridgeAdv gA S e := by
  intro e h
  cases e with
  | none => exact absurd rfl h
  | some e' =>
    cases e' with
    | inl y => exact (S y).tWindowPos
    | inr _ => exact Nat.succ_pos _

theorem bridge_advTime : ∀ e : BridgeArc gA n, e ≠ none →
    openVmBridgeTimestamp (bridgeDst gA S iR r e)
      = openVmBridgeTimestamp (bridgeSrc gA S iR r e) + ((bridgeAdv gA S e : ℕ) : ZMod p) := by
  intro e h
  cases e with
  | none => exact absurd rfl h
  | some e' =>
    cases e' with
    | inl x => rfl
    | inr i => rfl

/-- The run advances the clock by at most one maxWindow per instance, guest or input-chip. -/
theorem bridge_total_le {maxInstances maxInputInstances : ℕ}
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances) :
    (∑ e : BridgeArc gA n, bridgeAdv gA S e) ≤ (maxInstances + maxInputInstances) * maxWindow := by
  set adv : BridgeArc gA n → ℕ := bridgeAdv gA S with hadv
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  have hnone : adv none = 0 := rfl
  have hsome : ∑ y : GuestArc gA, adv (some (.inl y))
      ≤ (∑ s : Fin G.length, (gA s).length) * maxWindow := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ maxWindow
      (fun y _ => le_of_lt (S y).tWindowLt)) ?_
    rw [smul_eq_mul, Finset.card_univ, Fintype.card_sigma]
    simp
  have hinput : ∑ i : Fin n, adv (some (.inr i)) ≤ n * maxWindow := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ maxWindow (fun _ _ => le_of_lt hIlt)) ?_
    rw [smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  calc adv none
        + (∑ y : GuestArc gA, adv (some (.inl y))
          + ∑ i : Fin n, adv (some (.inr i)))
      = (∑ y : GuestArc gA, adv (some (.inl y)))
          + ∑ i : Fin n, adv (some (.inr i)) := by rw [hnone]; ring
    _ ≤ (∑ s : Fin G.length, (gA s).length) * maxWindow + n * maxWindow :=
        Nat.add_le_add hsome hinput
    _ ≤ maxInstances * maxWindow + maxInputInstances * maxWindow :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hcount) (Nat.mul_le_mul_right _ hcountI)
    _ = (maxInstances + maxInputInstances) * maxWindow := by ring

theorem bridge_totalLt {maxInstances maxInputInstances : ℕ}
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) :
    (∑ e : BridgeArc gA n, bridgeAdv gA S e) < p := by
  have hring : (maxInstances + maxInputInstances + 1) * (maxWindow + 1)
      = (maxInstances + maxInputInstances) * maxWindow
        + (maxInstances + maxInputInstances + maxWindow + 1) := by ring
  refine lt_of_le_of_lt (bridge_total_le gA S hIlt hcount hcountI)
    (lt_of_lt_of_le ?_ (le_of_lt hp))
  rw [hring]
  exact Nat.lt_add_of_pos_right (by omega)

/-- **A run's execution bridge, read as a `VmChain.Chain`.** -/
def bridgeChain {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) :
    VmChain.Chain p (BridgeArc gA n) (BusMessage p) where
  src := bridgeSrc gA S iR r
  dst := bridgeDst gA S iR r
  time := openVmBridgeTimestamp
  conn := none
  adv := bridgeAdv gA S
  balanced := bridge_balanced gA S iR ptrReg r h2 hbal hcount hcountI hp
  advPos := bridge_advPos gA S
  advTime := bridge_advTime gA S iR r
  advConn := rfl
  totalLt := bridge_totalLt gA S hIlt hcount hcountI hp

/-- **Every instance starts at an honest natural timestamp, and finishes below the connector's.**
    The connector's final timestamp is the one OpenVM range-checks
    (`ConnectorBoundary.finalTimestampBounded`), so this is what carries that single check to every
    instruction in the run. -/
theorem bridge_chain_bound_arc {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p)
    (e : BridgeArc gA n) (he : e ≠ none) :
    ∃ T : ℕ, openVmBridgeTimestamp (bridgeSrc gA S iR r e) = ((1 + T : ℕ) : ZMod p) ∧
      1 + T + bridgeAdv gA S e ≤ r.finalTimestamp.val := by
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨N, hN⟩ : ∃ N, (∑ e : BridgeArc gA n, bridgeAdv gA S e) = N := ⟨_, rfl⟩
  have htot : N ≤ (maxInstances + maxInputInstances) * maxWindow :=
    hN ▸ bridge_total_le gA S hIlt hcount hcountI
  have h1N : 1 + N < p := by
    have hp' := hp
    rw [show (maxInstances + maxInputInstances + 1) * (maxWindow + 1)
      = (maxInstances + maxInputInstances) * maxWindow
        + (maxInstances + maxInputInstances + maxWindow + 1) from by ring] at hp'
    obtain ⟨M, hM⟩ : ∃ M, (maxInstances + maxInputInstances) * maxWindow = M := ⟨_, rfl⟩
    rw [hM] at hp' htot
    omega
  obtain ⟨T, hT1, hT2⟩ :=
    (bridgeChain gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp).arc_position e he
  have hT1' : T + bridgeAdv gA S e ≤ ∑ e : BridgeArc gA n, bridgeAdv gA S e := hT1
  rw [hN] at hT1'
  have hT2' : openVmBridgeTimestamp (bridgeSrc gA S iR r e) = 1 + (T : ZMod p) := hT2
  have hconn : r.finalTimestamp = 1 + ((N : ℕ) : ZMod p) := by
    have h' : r.finalTimestamp = 1 + ((∑ e : BridgeArc gA n, bridgeAdv gA S e : ℕ) : ZMod p) :=
      (bridgeChain gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp).time_conn
    rwa [hN] at h'
  have hcast : (1 : ZMod p) + ((N : ℕ) : ZMod p) = ((1 + N : ℕ) : ZMod p) := by push_cast; ring
  have hval : r.finalTimestamp.val = 1 + N := by
    rw [hconn, hcast, ZMod.val_cast_of_lt h1N]
  refine ⟨T, ?_, by omega⟩
  rw [hT2']
  push_cast
  ring

/-- **Every guest instance starts at an honest natural timestamp, and finishes below the
    connector's.** The connector's final timestamp is the one OpenVM range-checks
    (`ConnectorBoundary.finalTimestampBounded`), so this is what carries that single check to every
    instruction in the run. -/
theorem bridge_chain_bound {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p)
    (y : GuestArc gA) :
    ∃ T : ℕ, (S y).tStart = ((1 + T : ℕ) : ZMod p) ∧
      1 + T + (S y).tWindow ≤ r.finalTimestamp.val :=
  bridge_chain_bound_arc gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp
    (some (.inl y)) (Option.some_ne_none _)

include S in
/-- The same for an input-chip instance: `InputRead.base` is an honest natural, and its two memory
    accesses (at `base + 1` and `base + 2`) sit below the connector's range-checked ceiling. This
    is what makes an input-chip send a legitimate producer of a record a guest reads back. -/
theorem bridge_chain_bound_input {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p)
    (i : Fin n) :
    ∃ T : ℕ, (iR i).base = ((1 + T : ℕ) : ZMod p) ∧
      1 + T + inputStepWindow ≤ r.finalTimestamp.val :=
  bridge_chain_bound_arc gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp
    (some (.inr i)) (Option.some_ne_none _)

end Bridge

--------- The rank window ---------

/-- The two stateful buses of `defaultBusMap` are the ones `openVmRank` reads a timestamp from. -/
theorem openVmIsStateful_default {b : Nat} (h : openVmIsStateful defaultBusMap b = true) :
    b = openVmMemBusId ∨ b = openVmExecBusId := by
  match b with
  | 0 => exact Or.inr rfl
  | 1 => exact Or.inl rfl
  | 2 | 3 | 4 | 5 | 6 | 7 | _ + 8 =>
    simp [openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at h

/-- **A placed interaction's rank, read off the chain.** Its step's `base` is `1 + T` for an
    honest natural `T`, so the timestamp is `1 + T + off` as an integer — and shifting by the
    maximum lookback moves that into `[0, openVmRankBound)`, where no wraparound can spoof the
    order. -/
theorem rank_of_placed {memBusId : Nat} {m : BusMessage p} {T : ℕ} {off : ℤ} {d : ℕ}
    (hpp : openVmRankBound < p) (hstate : m.1 = memBusId ∨ m.1 = openVmExecBusId)
    (hlow : -(openVmTimestampBound : ℤ) ≤ off) (hhigh : off ≤ (d : ℤ))
    (hfit : 1 + T + d ≤ openVmTimestampBound)
    (hts : openVmTimestamp memBusId m = ((1 + T : ℕ) : ZMod p) + (off : ZMod p)) :
    (openVmRank memBusId m : ℤ) = 1 + T + off + openVmRankShift := by
  haveI : NeZero p := ⟨by have := hpp; omega⟩
  have hz : ((1 + T : ℕ) : ZMod p) + (off : ZMod p) + ((openVmRankShift : ℕ) : ZMod p)
      = (((1 + T + off + openVmRankShift : ℤ)) : ZMod p) := by push_cast; ring
  have hrange : 0 ≤ (1 + T + off + openVmRankShift : ℤ) ∧
      (1 + T + off + openVmRankShift : ℤ) < p := by
    have h1 : (openVmRankShift : ℤ) = (openVmTimestampBound : ℤ) := rfl
    have h2 : ((openVmRankBound : ℕ) : ℤ)
        = (openVmTimestampBound : ℤ) + (openVmRankShift : ℤ) := by
      simp [openVmRankBound]
    have h3 : ((openVmRankBound : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hpp
    constructor
    · omega
    · have : (1 : ℤ) + T + off ≤ (openVmTimestampBound : ℤ) := by
        have : ((1 + T + d : ℕ) : ℤ) ≤ (openVmTimestampBound : ℤ) := by exact_mod_cast hfit
        push_cast at this
        omega
      omega
  simp only [openVmRank, if_pos hstate, hts, hz]
  rw [ZMod.val_intCast, Int.emod_eq_of_lt hrange.1 hrange.2]

--------- The rank order ---------

/-- **`openVmHost` turns a step's offsets into a rank order** — with no hypotheses left.

    The last undischarged assumption of the VM-level soundness theorem. Two interactions of one
    instance placed in the same step sit at `1 + T + off` for the *same* `T` — the step's position
    on the bridge, which the chain walk pins — so the one with the smaller offset has the smaller
    rank, and `OpenVmParams.rankWindowOk` is what keeps both inside a window too narrow to wrap.

    The arithmetic it needs is `OpenVmParams.windowOk`, already discharged when `P` was built:
    `P.maxInstances` instances advancing the clock by less than `P.maxWindow` each cannot wrap
    `ZMod p`. Everything else comes from the VM — `Circuit.hasStepLayout`, required of every legal
    guest, and the connector's range-checked final timestamp. -/
theorem openVmHost_ordersRanks [Fact p.Prime] (P : OpenVmParams p) :
    (openVmHost P).ordersRanks (openVmRankModel openVmMemBusId)
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress := by
  classical
  have hp := P.windowOk
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  intro G hGuests a hsat t asg hasg L i₀ j₀ hActI hActJ hoff
  -- The instance we are ordering, as an index into the assignment.
  obtain ⟨jx, hjx⟩ := List.get_of_mem hasg
  subst hjx
  -- A layout for every instance, this one's being the very one we were handed.
  have hNonempty : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      Nonempty (StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound) :=
    fun x => openVmHost_stepLayout_unpack P _ (hGuests _ (List.get_mem G x.1))
      _ (hsat.satisfiesGuest x.1 _ (List.get_mem _ _))
      (satisfiesStateless_of_sinks (openVmHost_legalGuest_unpack P) (openVmHost_sinksAreTables P)
        hGuests hsat x.1 _ (List.get_mem _ _))
  let S : ∀ x : ((s : Fin G.length) × Fin (a.guestAssignments s).length),
      StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((a.guestAssignments x.1).get x.2) openVmMemAddress P.maxWindow openVmTimestampBound :=
    fun x => if h : x = ⟨t, jx⟩ then by subst h; exact L else Classical.choice (hNonempty x)
  have hSL : S ⟨t, jx⟩ = L := by simp only [S, dif_pos]
  -- The connector, the input-chip instances' own witnesses, and the bridge's balance equation.
  obtain ⟨r, iR, -, hrnet⟩ :=
    openVmHost_bridge_isolated P hsat.satisfiesHost
  have hbal : ∀ m : BusMessage p, m.1 = 0 →
      a.guestAssignments.busEffect m +
        (∑ i, busStateOf ((iR i).interactions P.ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0 := by
    intro m hm
    have hb := hsat.balances m
    rw [busEffect_apply, hrnet m hm] at hb
    linear_combination hb
  have hcount : (∑ s : Fin G.length, (a.guestAssignments s).length) ≤ P.maxInstances :=
    hsat.withinBudget
  have hcountI : (a.hostAssignment (openVmInputChip P)).length ≤ P.maxInputInstances :=
    hsat.satisfiesHost.withinBound (openVmInputChip P)
  -- Both interactions are placed in the one step, so they share its position on the bridge.
  obtain ⟨hlowI, hhighI, htsI⟩ := L.tOffsetMatch i₀ hActI
  obtain ⟨hlowJ, hhighJ, htsJ⟩ := L.tOffsetMatch j₀ hActJ
  obtain ⟨T, hbase, hfit⟩ :=
    bridge_chain_bound a.guestAssignments S iR P.ptrReg r (openVm_negOne_ne_one P) hbal
      P.inputWindowOk hcount hcountI hp ⟨t, jx⟩
  rw [hSL] at hbase hfit
  -- One step, one `T`: the offsets decide.
  have hfit' : 1 + T + L.tWindow ≤ openVmTimestampBound := by
    have := r.finalTimestampBounded
    omega
  have hbase' : ∀ (x : Fin (G.get t).busInteractions.length) (off : ℤ),
      openVmTimestamp openVmMemBusId ((G.get t).msgAt ((a.guestAssignments t).get jx) x)
          = L.tStart + (off : ZMod p) →
        openVmTimestamp openVmMemBusId ((G.get t).msgAt ((a.guestAssignments t).get jx) x)
          = ((1 + T : ℕ) : ZMod p) + (off : ZMod p) := by
    intro x off h
    rw [h, hbase]
  have hstate : ∀ x : Fin (G.get t).busInteractions.length,
      (G.get t).activeStateful (openVmGuestRules defaultBusMap openVmMemBusId)
          ((a.guestAssignments t).get jx) x →
        ((G.get t).msgAt ((a.guestAssignments t).get jx) x).1 = openVmMemBusId ∨
          ((G.get t).msgAt ((a.guestAssignments t).get jx) x).1 = openVmExecBusId :=
    fun x hx => openVmIsStateful_default hx.1
  have hI := rank_of_placed (memBusId := openVmMemBusId) P.rankWindowOk (hstate i₀ hActI)
    hlowI hhighI hfit' (hbase' i₀ _ htsI)
  have hJ := rank_of_placed (memBusId := openVmMemBusId) P.rankWindowOk (hstate j₀ hActJ)
    hlowJ hhighJ hfit' (hbase' j₀ _ htsJ)
  show (openVmRankModel (p := p) openVmMemBusId).rank _
    < (openVmRankModel (p := p) openVmMemBusId).rank _
  simp only [openVmRankModel]
  omega

end ApcOptimizer.OpenVM
