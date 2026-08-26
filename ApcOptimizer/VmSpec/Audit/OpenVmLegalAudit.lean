import ApcOptimizer.VmSpec.Theorems
import ApcOptimizer.VmSpec.Implementation.Validation

set_option autoImplicit false

/-! **Auditing `Circuit.legalGuest` against real OpenVM circuit shapes.**

    A memory send in OpenVM carries byte-valued limbs for exactly one of two reasons, and the file
    checks that `StepLayout` accepts both.

    **Read-echo.** Every OpenVM memory access receives the cell's previous record (multiplicity
    `-1`, `[address space, pointer, four data limbs, previous timestamp]`) and sends the *same
    data* back at a fresh timestamp (`+1`). The sent limbs are bytes only because the received ones
    were; no algebraic constraint and no lookup bounds them. `readEchoChip` is that shape in
    isolation, and it is where `StepLayout.memSendsOk` earns its keep — the send discharges its
    obligation from the receive, and only because `StepLayout.tOffset` puts the receive strictly
    before the send.

    That ordering is *derived here, not assumed*, and the derivation is the point. Legality here is
    stated against `openVmGuestRules`, so what a stateful send has to produce is `openVmPayloadOk`
    — the byte condition, written out — rather than anything about a `BusSemantics`.

    `MemoryOfflineChecker` does not constrain `prev_timestamp < timestamp` directly: it attaches an
    `AssertLtSubAir`, which range-checks the limbs of `timestamp - prev_timestamp - 1` — two limbs
    of 17 and 12 bits, at the default `timestamp_max_bits = 29`. `readEchoChip` carries exactly
    that gadget (`assertLtLoLookup`, `assertLtHiLookup`, `assertLtConstraint`), and the range check
    is what places the receive at a negative offset inside `stepChip`'s window rather than leaving
    it free. `earlyEchoChip_legalGuest` lists the echo *before* the read instead of after — the
    opposite of a real trace — while keeping the same real timestamps, and is legal all the same:
    `memSendsOk` reads off `tOffset`, not list position, so scrambling the constraint order (which no
    algebraic condition pins anyway) cannot be what legality depends on.

    **Fresh write.** A value the chip computes and writes is byte-valued because of a
    bitwise-lookup range check — OpenVM's own `op = 1, x = y` idiom, since `xor x x = 0` holds for
    any byte. `freshWriteChip` has no stateful traffic below its send's rank at all, so what
    carries it is `Circuit.satisfiesStateless` (`freshWriteChip_legalGuest`).

    Neither hypothesis is circular: the rank one is the induction hypothesis of
    `maintains_of_stateful_active`, and the lookup one is `satisfiesStateless_of_sinks`, which uses
    no stateful clause. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- `openVmPayloadOk` on a register record is exactly "the data limbs are bytes". Both directions
    are used below: a receive hands one over, a send has to produce one. -/
theorem openVmPayloadOk_mem_iff [Fact (1 < p)] (ptr d0 d1 d2 d3 ts : ZMod p) :
    openVmPayloadOk (p := p) defaultBusMap (1, [1, ptr, d0, d1, d2, d3, ts]) ↔
      (isByte d0 ∧ isByte d1 ∧ isByte d2 ∧ isByte d3) := by
  simp only [openVmPayloadOk, defaultBusMap, memoryPayload?]
  constructor
  · intro h
    have h' := h (Or.inl (ZMod.val_one p))
    exact ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩
  · rintro ⟨h0, h1, h2, h3⟩ - d hd
    simp at hd
    rcases hd with rfl | rfl | rfl | rfl <;> assumption

--------- The read-echo shape ---------

/-- The receive half of a memory access: the cell's previous record, at address space `1`
    (registers). The data limb `x` is a free variable — no algebraic constraint mentions it,
    exactly as for a register the circuit reads and passes on. -/
def readEchoRecv (x : Variable) (ptr t₀ : ZMod p) : BusInteraction (Expression p) where
  busId := 1
  multiplicity := .const (-1)
  payload := [.const 1, .const ptr, .var x, .const 0, .const 0, .const 0, .const t₀]

/-- The send half: the same data limbs, at a fresh timestamp. -/
def readEchoSend (x : Variable) (ptr t₁ : ZMod p) : BusInteraction (Expression p) where
  busId := 1
  multiplicity := .const 1
  payload := [.const 1, .const ptr, .var x, .const 0, .const 0, .const 0, .const t₁]

/-- `AssertLtSubAir`'s low limb, range-checked to the variable range checker's own
    `range_max_bits = 17`. The width is written as a `ℕ` cast because that is what
    `accepts` reads back out of the payload. -/
def assertLtLoLookup (lo : Variable) : BusInteraction (Expression p) where
  busId := 3
  multiplicity := .const 1
  payload := [.var lo, .const ((17 : ℕ) : ZMod p)]

/-- The high limb, carrying the remaining `29 - 17 = 12` bits of `openVmTimestampBits`. -/
def assertLtHiLookup (hi : Variable) : BusInteraction (Expression p) where
  busId := 3
  multiplicity := .const 1
  payload := [.var hi, .const ((12 : ℕ) : ZMod p)]

/-- `AssertLtSubAir`'s one algebraic constraint, `t₁ - t₀ - 1 = lo + 2 ^ 17 * hi`. Together with
    the two range checks this is *all* OpenVM says about the two timestamps. -/
def assertLtConstraint (lo hi : Variable) (t₀ t₁ : ZMod p) : Expression p :=
  .add (.const (t₁ - t₀ - 1))
    (.mul (.const (-1)) (.add (.var lo) (.mul (.const ((2 ^ 17 : ℕ) : ZMod p)) (.var hi))))

/-- The chip: one memory access, with the timestamp comparison OpenVM attaches to it. -/
def readEchoChip (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) : Circuit p where
  algebraicConstraints := [assertLtConstraint lo hi t₀ t₁]
  busInteractions :=
    [readEchoRecv x ptr t₀, readEchoSend x ptr t₁, assertLtLoLookup lo, assertLtHiLookup hi]

/-- Only the two range checks are stateless, and both are sent with multiplicity `1`. -/
theorem readEchoChip_statelessSendOnly (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) :
    (readEchoChip x lo hi ptr t₀ t₁).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [readEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl
  · simp [readEchoRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [readEchoSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- The two memory multiplicities are literally `-1` and `1`. -/
theorem readEchoChip_statefulPolarity (x lo hi : Variable) (ptr t₀ t₁ : ZMod p) :
    (readEchoChip x lo hi ptr t₀ t₁).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [readEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · simp [assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- The limb bounds the two range checks buy, read straight out of `accepts` — for *any* circuit
    `c` carrying the two lookups, not just `readEchoChip` itself, so `stepChip` (which wraps the
    same access in an execution-bridge step) can reuse it verbatim. -/
theorem readEcho_limbs [Fact (1 < p)] (hp : 17 < p) {c : Circuit p} (lo hi : Variable)
    (hmemLo : assertLtLoLookup lo ∈ c.busInteractions)
    (hmemHi : assertLtHiLookup hi ∈ c.busInteractions)
    {asg : ChipAssignment p}
    (hacc : c.satisfiesStateless (openVmGuestRules defaultBusMap openVmMemBusId) asg) :
    (asg lo).val < 2 ^ 17 ∧ (asg hi).val < 2 ^ 12 := by
  have hlo := hacc (assertLtLoLookup lo) hmemLo rfl one_ne_zero
  have hhi := hacc (assertLtHiLookup hi) hmemHi rfl one_ne_zero
  replace hlo : (((17 : ℕ) : ZMod p)).val ≤ 17 ∧ (asg lo).val < 2 ^ (((17 : ℕ) : ZMod p)).val := hlo
  replace hhi : (((12 : ℕ) : ZMod p)).val ≤ 17 ∧ (asg hi).val < 2 ^ (((12 : ℕ) : ZMod p)).val := hhi
  rw [ZMod.val_natCast_of_lt hp] at hlo
  rw [ZMod.val_natCast_of_lt (by omega)] at hhi
  exact ⟨hlo.2, hhi.2⟩

/-- The limb bounds, specialized to `readEchoChip` itself. -/
theorem readEchoChip_limbs [Fact (1 < p)] (hp : 17 < p) (x lo hi : Variable) (ptr t₀ t₁ : ZMod p)
    {asg : ChipAssignment p}
    (hacc : (readEchoChip x lo hi ptr t₀ t₁).satisfiesStateless
      (openVmGuestRules defaultBusMap openVmMemBusId) asg) :
    (asg lo).val < 2 ^ 17 ∧ (asg hi).val < 2 ^ 12 :=
  readEcho_limbs hp lo hi (by simp [readEchoChip]) (by simp [readEchoChip]) hacc

--------- The execution-bridge step ---------

/-- The execution-bridge receive: the instruction's incoming state `(pc, t)` (whitepaper §4.5,
    `ExecutionBus::execute` receives `prev_state`). -/
def bridgeRecv (pc t : ZMod p) : BusInteraction (Expression p) where
  busId := 0
  multiplicity := .const (-1)
  payload := [.const pc, .const t]

/-- The execution-bridge send: the outgoing state. -/
def bridgeSend (pc t : ZMod p) : BusInteraction (Expression p) where
  busId := 0
  multiplicity := .const 1
  payload := [.const pc, .const t]

/-- A whole instruction executor: `readEchoChip`'s memory access wrapped in the execution-bridge
    step it belongs to. Timestamps are laid out as OpenVM lays them out — the step runs from `base`
    to `base + 3`, and the access reads at `base + 1` and writes at `base + 2`, strictly inside
    (whitepaper §4.2). This is `StepLayout`'s shape, and the chip below is the check that the
    predicate is satisfiable by a realistic one. -/
def stepChip (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) : Circuit p where
  algebraicConstraints := [assertLtConstraint lo hi (base + 1) (base + 2)]
  busInteractions :=
    [bridgeRecv pcFrom base, readEchoRecv x ptr (base + 1), readEchoSend x ptr (base + 2),
      bridgeSend pcTo (base + 3), assertLtLoLookup lo, assertLtHiLookup hi]

/-- **`Circuit.hasStepLayout` accepts a realistic instruction executor.** One step, from `base` to
    `base + 3`, with each interaction's offset its own position in the list — which is exactly how
    OpenVM lays an executor out.

    `StepLayout.memSendsOk` is where the byte invariant is carried, and for the memory send it is
    carried by the *receive that precedes it in the same step*: nothing algebraic bounds `x`, and
    the send is byte-valued purely because the earlier receive was. No timestamp comparison is
    needed to see that — the offsets do it. -/
theorem stepChip_hasStepLayout (hp : 3 < p) {maxWindow maxLookback : ℕ} (hw : 3 < maxWindow)
    (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).hasStepLayout
      (openVmGuestRules defaultBusMap openVmMemBusId) maxWindow maxLookback := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hcast3 : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by push_cast; ring
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 3 < p by omega)
    rw [hcast3, h, ZMod.val_zero] at hv
    omega
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 2 < p by omega)
    rw [h, ZMod.val_zero] at hv
    omega
  have hneg : (-1 : ZMod p) ≠ 1 := fun hcon => h2 (by push_cast; linear_combination -hcon)
  have hnegz : (-1 : ZMod p) ≠ 0 := fun hcon => one_ne_zero (α := ZMod p) (by
    linear_combination -hcon)
  intro asg _ _
  refine ⟨⟨pcFrom, pcTo, base, 3, by norm_num, hw, ?_, ?_, ?_, fun i => (i.val : ℤ), ?_, ?_⟩⟩
  · simp [Circuit.allEffects, stepChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      assertLtLoLookup, assertLtHiLookup, BusInteraction.eval, Expression.eval,
      openVmGuestRules, h3]
  · simp [Circuit.allEffects, stepChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      assertLtLoLookup, assertLtHiLookup, BusInteraction.eval, Expression.eval,
      openVmGuestRules, h3]
  · rintro ⟨mb, ml⟩ hbus hr hs
    simp only [openVmGuestRules] at hbus
    subst hbus
    simp only [ne_eq, Prod.mk.injEq, true_and, hcast3, openVmGuestRules] at hr hs
    simp [Circuit.allEffects, stepChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      assertLtLoLookup, assertLtHiLookup, BusInteraction.eval, Expression.eval,
      Ne.symm hr, Ne.symm hs]
  · rintro i ⟨hst, -⟩
    fin_cases i
    · exact ⟨by push_cast; omega, by norm_num, by
        simp [stepChip, bridgeRecv, openVmGuestRules, openVmTimestamp, Circuit.msgAt, BusInteraction.eval,
          Expression.eval, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by push_cast; omega, by norm_num, by
        simp [stepChip, readEchoRecv, openVmGuestRules, openVmTimestamp, Circuit.msgAt, BusInteraction.eval,
          Expression.eval, openVmMemBusId]⟩
    · exact ⟨by push_cast; omega, by norm_num, by
        simp [stepChip, readEchoSend, openVmGuestRules, openVmTimestamp, Circuit.msgAt, BusInteraction.eval,
          Expression.eval, openVmMemBusId]⟩
    · exact ⟨by push_cast; omega, by norm_num, by
        simp [stepChip, bridgeSend, openVmGuestRules, openVmTimestamp, Circuit.msgAt, BusInteraction.eval,
          Expression.eval, openVmMemBusId, openVmExecBusId]⟩
    · simp [stepChip, assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [stepChip, assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · rintro i ⟨⟨hst, hmult⟩, hbmem⟩ hlow
    fin_cases i
    · exact absurd hmult hneg
    · exact absurd hmult hneg
    · -- The send echoes the receive one position earlier in the very same step; `tOffset` is list
      -- position here, so "earlier in the step" and "earlier in the list" coincide.
      have hrecv0 := hlow ⟨1, by simp [stepChip]⟩ (by norm_num) ⟨⟨rfl, hnegz⟩, rfl⟩
      replace hrecv0 : openVmPayloadOk defaultBusMap
        ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, base + 1]) := hrecv0
      have hrecv := hrecv0
      have hx : isByte (asg x) :=
        ((openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 1)).mp hrecv).1
      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, base + 2])
      exact (openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 2)).mpr
        ⟨hx, isByte_zero, isByte_zero, isByte_zero⟩
    · -- The bridge send is not on the memory bus at all, so `memSendsOk`'s own hypothesis rules
      -- this case out.
      simp [stepChip, bridgeSend, openVmGuestRules, openVmExecBusId, openVmMemBusId] at hbmem
    · simp [stepChip, assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [stepChip, assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst

/-- Only the two range checks are stateless; the bridge pair and the memory access are both
    stateful. -/
theorem stepChip_statelessSendOnly (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [stepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [bridgeRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [readEchoRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [readEchoSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [bridgeSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- The four stateful multiplicities are literally `±1`. -/
theorem stepChip_statefulPolarity (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [stepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · simp [assertLtLoLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · simp [assertLtHiLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- **The full example `Circuit.legalGuest` exists for: a realistic instruction executor.**
    `stepChip` is `readEchoChip`'s memory access wrapped in the execution-bridge step OpenVM
    requires around it, and it satisfies every condition — this is the file's answer to
    "is `Circuit.legalGuest` satisfiable by anything a real VM would actually run". -/
theorem stepChip_legalGuest (hp : 3 < p) {maxWindow maxLookback maxInteractions : ℕ}
    (hw : 3 < maxWindow) (hi6 : 6 ≤ maxInteractions)
    (x lo hi : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (stepChip x lo hi pcFrom pcTo ptr base).legalGuest
      (openVmGuestRules defaultBusMap openVmMemBusId) maxWindow maxLookback maxInteractions where
  sendOnly := stepChip_statelessSendOnly x lo hi pcFrom pcTo ptr base
  polarity := stepChip_statefulPolarity x lo hi pcFrom pcTo ptr base
  stepLayout := stepChip_hasStepLayout hp hw x lo hi pcFrom pcTo ptr base
  size := by simpa [stepChip] using hi6

/-- The same interactions with the echo *before* the read: the word is handed on at `base + 2`
    before it is read at `base + 1`. -/
def earlyEchoChip (x : Variable) (pcFrom pcTo ptr base : ZMod p) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [bridgeRecv pcFrom base, readEchoSend x ptr (base + 2), readEchoRecv x ptr (base + 1),
      bridgeSend pcTo (base + 3)]

/-- Only the two bridge interactions are stateful in the usual `stepChip` sense but here *every*
    interaction is stateful — `earlyEchoChip` carries no lookup at all — so this is vacuous. -/
theorem earlyEchoChip_statelessSendOnly (x : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (earlyEchoChip x pcFrom pcTo ptr base).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [earlyEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl <;>
    simp [bridgeRecv, bridgeSend, readEchoRecv, readEchoSend, openVmGuestRules,
      openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at hst

/-- The four multiplicities are literally `±1`. -/
theorem earlyEchoChip_statefulPolarity (x : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (earlyEchoChip x pcFrom pcTo ptr base).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [earlyEchoChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)

/-- **Scrambling the constraint list does not change legality.** Real timestamps are exactly
    `stepChip`'s — the receive at `base + 1`, the send at `base + 2` — only their position in
    `busInteractions` is swapped. `tOffset` tracks the timestamp, not the list position, so
    `memSendsOk`'s obligation on the send is discharged by the receive precisely as it was for
    `stepChip`: whether the constraint that computes a value comes before or after the constraint
    that uses it is not something a real VM's algebraic relations can see. -/
theorem earlyEchoChip_hasStepLayout (hp : 3 < p) {maxWindow maxLookback : ℕ} (hw : 3 < maxWindow)
    (x : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (earlyEchoChip x pcFrom pcTo ptr base).hasStepLayout
      (openVmGuestRules defaultBusMap openVmMemBusId) maxWindow maxLookback := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hcast3 : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by push_cast; ring
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 3 < p by omega)
    rw [hcast3, h, ZMod.val_zero] at hv
    omega
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 2 < p by omega)
    rw [h, ZMod.val_zero] at hv
    omega
  have hneg : (-1 : ZMod p) ≠ 1 := fun hcon => h2 (by push_cast; linear_combination -hcon)
  have hnegz : (-1 : ZMod p) ≠ 0 := fun hcon => one_ne_zero (α := ZMod p) (by
    linear_combination -hcon)
  intro asg _ _
  refine ⟨⟨pcFrom, pcTo, base, 3, by norm_num, hw, ?_, ?_, ?_,
    fun i => ([0, 2, 1, 3] : List ℤ).getD i.val 0, ?_, ?_⟩⟩
  · simp [Circuit.allEffects, earlyEchoChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      BusInteraction.eval, Expression.eval, openVmGuestRules, h3]
  · simp [Circuit.allEffects, earlyEchoChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      BusInteraction.eval, Expression.eval, openVmGuestRules, h3]
  · rintro ⟨mb, ml⟩ hbus hr hs
    simp only [openVmGuestRules] at hbus
    subst hbus
    simp only [ne_eq, Prod.mk.injEq, true_and, hcast3, openVmGuestRules] at hr hs
    simp [Circuit.allEffects, earlyEchoChip, bridgeRecv, bridgeSend, readEchoRecv, readEchoSend,
      BusInteraction.eval, Expression.eval, Ne.symm hr, Ne.symm hs]
  · rintro i ⟨hst, -⟩
    fin_cases i
    · exact ⟨by simp, by simp, by
        simp [earlyEchoChip, bridgeRecv, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          BusInteraction.eval, Expression.eval, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp, by simp, by
        simp [earlyEchoChip, readEchoSend, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          BusInteraction.eval, Expression.eval, openVmMemBusId]⟩
    · exact ⟨by simp, by simp, by
        simp [earlyEchoChip, readEchoRecv, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          BusInteraction.eval, Expression.eval, openVmMemBusId]⟩
    · exact ⟨by simp, by simp, by
        simp [earlyEchoChip, bridgeSend, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          BusInteraction.eval, Expression.eval, openVmMemBusId, openVmExecBusId]⟩
  · rintro i ⟨⟨hst, hmult⟩, hbmem⟩ hlow
    fin_cases i
    · exact absurd hmult hneg
    · -- The send: justified by the receive, which sits later in the list (index `2`) but earlier
      -- in `tOffset` (`1 < 2`).
      have hrecv0 := hlow ⟨2, by simp [earlyEchoChip]⟩ (by simp) ⟨⟨rfl, hnegz⟩, rfl⟩
      replace hrecv0 : openVmPayloadOk defaultBusMap
        ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, base + 1]) := hrecv0
      have hx : isByte (asg x) :=
        ((openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 1)).mp hrecv0).1
      show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, base + 2])
      exact (openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 2)).mpr
        ⟨hx, isByte_zero, isByte_zero, isByte_zero⟩
    · exact absurd hmult hneg
    · simp [earlyEchoChip, bridgeSend, openVmGuestRules, openVmExecBusId, openVmMemBusId] at hbmem

/-- **The full example: legality survives a scrambled constraint list.** -/
theorem earlyEchoChip_legalGuest (hp : 3 < p) {maxWindow maxLookback maxInteractions : ℕ}
    (hw : 3 < maxWindow) (hi4 : 4 ≤ maxInteractions)
    (x : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (earlyEchoChip x pcFrom pcTo ptr base).legalGuest
      (openVmGuestRules defaultBusMap openVmMemBusId) maxWindow maxLookback maxInteractions where
  sendOnly := earlyEchoChip_statelessSendOnly x pcFrom pcTo ptr base
  polarity := earlyEchoChip_statefulPolarity x pcFrom pcTo ptr base
  stepLayout := earlyEchoChip_hasStepLayout hp hw x pcFrom pcTo ptr base
  size := by simpa [earlyEchoChip] using hi4

--------- The remaining gap: values justified by a lookup ---------

/-- The range check: the bitwise bus with `op = 1` and `x = y` is OpenVM's own idiom for
    range-checking a single limb (`xor x x = 0` holds for any byte). -/
def freshWriteLookup (x : Variable) : BusInteraction (Expression p) where
  busId := 6
  multiplicity := .const 1
  payload := [.var x, .var x, .const 0, .const 1]

/-- The write itself. -/
def freshWriteSend (x : Variable) (ptr t : ZMod p) : BusInteraction (Expression p) where
  busId := 1
  multiplicity := .const 1
  payload := [.const 1, .const ptr, .var x, .const 0, .const 0, .const 0, .const t]

/-- The chip: range-check a limb, then write it. -/
def freshWriteChip (x : Variable) (ptr t : ZMod p) : Circuit p where
  algebraicConstraints := []
  busInteractions := [freshWriteLookup x, freshWriteSend x ptr t]

/-- Only the lookup is stateless, and it is sent with multiplicity `1`. -/
theorem freshWriteChip_statelessSendOnly (x : Variable) (ptr t : ZMod p) :
    (freshWriteChip x ptr t).statelessSendOnly
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [freshWriteChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl
  · exact Or.inr rfl
  · simp [freshWriteSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst

/-- Only the write is stateful, and it is sent with multiplicity `1`. -/
theorem freshWriteChip_statefulPolarity (x : Variable) (ptr t : ZMod p) :
    (freshWriteChip x ptr t).statefulPolarity
      (openVmGuestRules defaultBusMap openVmMemBusId) := by
  intro asg _ bi hbi hst
  simp only [freshWriteChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl
  · simp [freshWriteLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
      OpenVmBusType.isStateful] at hst
  · exact Or.inr (Or.inl rfl)

/-- The whole chip: an execution-bridge step that range-checks a limb and writes it. -/
def freshWriteStepChip (x : Variable) (pcFrom pcTo ptr base : ZMod p) : Circuit p where
  algebraicConstraints := []
  busInteractions :=
    [bridgeRecv pcFrom base, freshWriteLookup x, freshWriteSend x ptr (base + 2),
      bridgeSend pcTo (base + 3)]

/-- **The fresh write discharges its obligation from its own range check.** Nothing stateful
    precedes the send in its step but the bridge receive, of which `openVmPayloadOk` asks nothing;
    what carries the invariant is `Circuit.satisfiesStateless` — a hypothesis of
    `Circuit.hasStepLayout` — on the bitwise lookup, whose `op = 1` case is exactly `isByte x`.

    This is the second of the two shapes an OpenVM memory send has: byte-valued because it was
    read, or byte-valued because it was checked. -/
theorem freshWriteStepChip_legalGuest (hp : 256 < p) {maxWindow maxLookback maxInteractions : ℕ}
    (hw : 3 < maxWindow) (hi4 : 4 ≤ maxInteractions)
    (x : Variable) (pcFrom pcTo ptr base : ZMod p) :
    (freshWriteStepChip x pcFrom pcTo ptr base).legalGuest
      (openVmGuestRules defaultBusMap openVmMemBusId) maxWindow maxLookback maxInteractions := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hcast3 : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by push_cast; ring
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 3 < p by omega)
    rw [hcast3, h, ZMod.val_zero] at hv
    omega
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hv := ZMod.val_natCast_of_lt (show 2 < p by omega)
    rw [h, ZMod.val_zero] at hv
    omega
  have hneg : (-1 : ZMod p) ≠ 1 := fun hcon => h2 (by push_cast; linear_combination -hcon)
  refine ⟨?_, ?_, ?_, by simpa [freshWriteStepChip] using hi4⟩
  · intro asg _ bi hbi hst
    simp only [freshWriteStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl | rfl | rfl
    · simp [bridgeRecv, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · exact Or.inr rfl
    · simp [freshWriteSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · simp [bridgeSend, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · intro asg _ bi hbi hst
    simp only [freshWriteStepChip, List.mem_cons, List.not_mem_nil, or_false] at hbi
    rcases hbi with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · simp [freshWriteLookup, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
  · intro asg _ hacc
    refine ⟨⟨pcFrom, pcTo, base, 3, by norm_num, hw, ?_, ?_, ?_,
      fun i => (i.val : ℤ), ?_, ?_⟩⟩
    · simp [Circuit.allEffects, freshWriteStepChip, bridgeRecv, bridgeSend, freshWriteLookup,
        freshWriteSend, BusInteraction.eval, Expression.eval, openVmGuestRules, h3]
    · simp [Circuit.allEffects, freshWriteStepChip, bridgeRecv, bridgeSend, freshWriteLookup,
        freshWriteSend, BusInteraction.eval, Expression.eval, openVmGuestRules, h3]
    · rintro ⟨mb, ml⟩ hbus hr hs
      simp only [openVmGuestRules] at hbus
      subst hbus
      simp only [ne_eq, Prod.mk.injEq, true_and, hcast3, openVmGuestRules] at hr hs
      simp [Circuit.allEffects, freshWriteStepChip, bridgeRecv, bridgeSend, freshWriteLookup,
        freshWriteSend, BusInteraction.eval, Expression.eval, Ne.symm hr, Ne.symm hs]
    · rintro i ⟨hst, -⟩
      fin_cases i
      · exact ⟨by push_cast; omega, by norm_num, by
          simp [freshWriteStepChip, bridgeRecv, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
            BusInteraction.eval, Expression.eval, openVmMemBusId, openVmExecBusId]⟩
      · simp [freshWriteStepChip, freshWriteLookup, openVmGuestRules, openVmIsStateful,
          defaultBusMap, OpenVmBusType.isStateful] at hst
      · exact ⟨by push_cast; omega, by norm_num, by
          simp [freshWriteStepChip, freshWriteSend, openVmGuestRules, openVmTimestamp,
            Circuit.msgAt, BusInteraction.eval, Expression.eval, openVmMemBusId]⟩
      · exact ⟨by push_cast; omega, by norm_num, by
          simp [freshWriteStepChip, bridgeSend, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
            BusInteraction.eval, Expression.eval, openVmMemBusId, openVmExecBusId]⟩
    · rintro i ⟨⟨hst, hmult⟩, hbmem⟩ -
      fin_cases i
      · exact absurd hmult hneg
      · simp [freshWriteStepChip, freshWriteLookup, openVmGuestRules, openVmIsStateful,
          defaultBusMap, OpenVmBusType.isStateful] at hst
      · -- The limb is a byte because the chip's own bitwise lookup says so.
        have hlook : freshWriteLookup x ∈ (freshWriteStepChip x pcFrom pcTo ptr base).busInteractions
          := by simp [freshWriteStepChip]
        have hacc' := hacc (freshWriteLookup x) hlook rfl one_ne_zero
        replace hacc' : (match ((1 : ZMod p)).val with
          | 0 => isByte (asg x) ∧ isByte (asg x) ∧ ((0 : ZMod p)).val = 0
          | 1 => isByte (asg x) ∧ isByte (asg x) ∧
                   ((0 : ZMod p)).val = Nat.xor (asg x).val (asg x).val
          | _ => False) := hacc'
        rw [ZMod.val_one p] at hacc'
        show openVmPayloadOk defaultBusMap
          ((1 : ℕ), [(1 : ZMod p), ptr, asg x, 0, 0, 0, base + 2])
        exact (openVmPayloadOk_mem_iff ptr (asg x) 0 0 0 (base + 2)).mpr
          ⟨hacc'.1, isByte_zero, isByte_zero, isByte_zero⟩
      · -- The bridge send is not on the memory bus, so `memSendsOk`'s own hypothesis rules this
        -- case out.
        simp [freshWriteStepChip, bridgeSend, openVmGuestRules, openVmExecBusId,
          openVmMemBusId] at hbmem
