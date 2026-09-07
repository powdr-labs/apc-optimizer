import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import ApcOptimizer.VmSpec.Audit.BridgeCheck
import ApcOptimizer.VmSpec.Audit.PlaceCheck
import ApcOptimizer.VmSpec.Audit.ByteCheck
import ApcOptimizer.VmSpec.Audit.OpenVmShapes
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **What every real-APC audit under `Apcs/` shares.**

    Nothing here mentions a particular circuit: it is the bus rules the APCs are measured against,
    the BabyBear facts powdr's encoding forces, and the OpenVM gadgets a `StepLayout` is read off —
    the lt gadget in both the shape powdr's optimizer leaves (`lt_gadget_offset`,
    `lookback_of_gadget`) and the raw pre-substitution shape (`rawGadget_heq`,
    `gadgetLookback_raw`), and the bitwise table's byte guarantees (`isByte_of_xorEq` and friends).

    One directory per APC sits alongside: `Stages.lean` defines the circuit at each point of
    powdr's pipeline, and one file per stage carries that stage's proofs. See
    `Audit/Legality/All.lean` for the results and what they say. -/

namespace ApcOptimizer.OpenVM

/-! `Spec.lean` assumes primality of the characteristic for every `p` it quantifies over. These
    circuits sit at the literal `babyBear`, so the one theorem that needs `ZMod babyBear` to be a
    field takes the same assumption as an instance hypothesis rather than re-proving it (Mathlib's
    `norm_num` primality extension is not built in this checkout). -/

/-- The rules every APC here is checked against: OpenVM's own bus map, memory on bus `1`. -/
abbrev apcRules : GuestBusRules babyBear :=
  openVmGuestRules defaultBusMap openVmMemBusId

/-- powdr emits `-1` as the literal `p - 1`; the two are the same field element. -/
theorem babyBear_negOne : (2013265920 : ZMod babyBear) = -1 := by decide

/-- **`Circuit.satisfiesAlgebraic`, re-typed so `decide` applies.** It is a `def` returning `Prop`,
    so instance resolution will not look under it for the decidable `∀ x ∈ L` it unfolds to. These
    two change nothing but the head symbol, and turn a padding-row argument -- does the all-zero
    assignment satisfy this circuit? -- into a `decide` on a concrete constraint list. -/
theorem satisfiesAlgebraic_of_forall {p : ℕ} {c : Circuit p} {asg : ChipAssignment p}
    (h : ∀ e ∈ c.algebraicConstraints, e.eval asg = 0) : c.satisfiesAlgebraic asg := h

theorem not_satisfiesAlgebraic_of_not_forall {p : ℕ} {c : Circuit p} {asg : ChipAssignment p}
    (h : ¬ ∀ e ∈ c.algebraicConstraints, e.eval asg = 0) : ¬ c.satisfiesAlgebraic asg := h

/-- A circuit whose every multiplicity vanishes puts nothing on any bus. -/
theorem allEffects_eq_zero_of_mults_zero {p : ℕ} {c : Circuit p} {asg : ChipAssignment p}
    (h : ∀ bi ∈ c.busInteractions, (bi.eval asg).multiplicity = 0) (m : BusMessage p) :
    c.allEffects asg m = 0 := by
  refine List.sum_eq_zero (fun x hx => ?_)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, -⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  exact h bi hbi

/-- **`StepLayout.memSendsOk`, from the unrestricted (all-buses) shape `ByteCheck.lean`
    produces.** A proof of the old, cross-bus `sendsOk` is strictly more than `memSendsOk` asks
    for, so this just plugs `memPayloadOnly` in for whichever `j` the memory-scoped hypothesis
    doesn't cover. -/
theorem memSendsOk_of_sendsOk {p : ℕ} {r : GuestBusRules p} {c : Circuit p}
    {asg : ChipAssignment p}
    (hsendsOk : ∀ i : Fin c.busInteractions.length, c.statefulSend r asg i →
      (∀ j : Fin c.busInteractions.length, j < i → c.activeStateful r asg j →
        r.payloadOk (c.msgAt asg j)) → r.payloadOk (c.msgAt asg i)) :
    ∀ i : Fin c.busInteractions.length, c.memSend r asg i →
      (∀ j : Fin c.busInteractions.length, j < i → c.activeMem r asg j →
        r.payloadOk (c.msgAt asg j)) →
      r.payloadOk (c.msgAt asg i) :=
  fun i ⟨hsend, _⟩ hlow => hsendsOk i hsend (fun j hji hactj =>
    if hjmem : (c.busInteractions.get j).busId = r.memBusId then hlow j hji ⟨hactj, hjmem⟩
    else r.memPayloadOnly _ hactj.1 hjmem)

--------- The gadgets a placement is read off ---------

/-- `-1` is neither `0` nor `1`: what rules a memory *receive* out of `StepLayout.ordered`'s and
    `StepLayout.sendsOk`'s send obligations. -/
theorem babyBear_negOne_ne_one : (2013265920 : ZMod babyBear) ≠ 1 := by decide

theorem babyBear_negOne_ne_zero : (2013265920 : ZMod babyBear) ≠ 0 := by decide

/-- **OpenVM's `AssertLtSubAir`, as it survives powdr's optimizer.** The gadget's own constraint
    `prev + 1 + lo + 2 ^ 17 * hi = t` is substituted away; what is left is its *range checks* — the
    low limb to 17 bits and, as the high limb's payload, `15360 * (prev + lo - base - δ)` to 12.
    That is the same equation, because `15360 = -1/2 ^ 17` in BabyBear (`15360 * 131072 = p - 1`),
    so the payload *is* `hi`.

    Reading it back: the access sits at `base + δ` and the record it receives sits `n` ticks
    earlier, `n = lo + 2 ^ 17 * hi < 2 ^ 29 = openVmTimestampBound`. That bound is the whole content
    of `StepLayout.tOffsetMatch`'s `-maxLookback ≤ offset`, and this is why `Circuit.hasStepLayout` is
    gated on `Circuit.satisfiesStateless`: after the substitution nothing about a receive's offset
    is derivable from the algebraic constraints alone. -/
theorem lt_gadget_offset (δ : ℤ) (prev base : ZMod babyBear) {lo hi : ZMod babyBear}
    (hlo : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [lo, 17] })
    (hhi : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [hi, 12] })
    (heq : hi = 15360 * prev + 15360 * lo - 15360 * base - 15360 * ((δ : ℤ) : ZMod babyBear)) :
    ∃ n : ℕ, n = lo.val + 131072 * hi.val ∧ n < 2 ^ 29 ∧
      prev = base + (((δ - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hlo' : lo.val < 2 ^ 17 := by
    have := (show (17 : ZMod babyBear).val ≤ 17 ∧ lo.val < 2 ^ (17 : ZMod babyBear).val from hlo).2
    rwa [show (17 : ZMod babyBear).val = 17 from by decide] at this
  have hhi' : hi.val < 2 ^ 12 := by
    have := (show (12 : ZMod babyBear).val ≤ 17 ∧ hi.val < 2 ^ (12 : ZMod babyBear).val from hhi).2
    rwa [show (12 : ZMod babyBear).val = 12 from by decide] at this
  refine ⟨lo.val + 131072 * hi.val, rfl, by omega, ?_⟩
  have hlo'' : ((lo.val : ℕ) : ZMod babyBear) = lo := by simp
  have hhi'' : ((hi.val : ℕ) : ZMod babyBear) = hi := by simp
  push_cast [hlo'', hhi'']
  have h15 : (15360 : ZMod babyBear) * 131072 = -1 := by decide
  linear_combination (131072 : ZMod babyBear) * heq
    + (prev + lo - base - ((δ : ℤ) : ZMod babyBear)) * h15

/-- `x + 3 = (x ^^^ 3) + 2 * (x &&& 3)` for a byte, by cases: the low two bits are the only ones
    the two operations disagree on. -/
theorem xor_three : ∀ x < 256, x + 3 = Nat.xor x 3 + 2 * (x % 4) := by decide

/-- **`x AND 3` is a byte, from the bitwise table alone.** OpenVM masks by lookup up rather than by
    constraint: `z = x XOR 3` (the table's `op = 1` arm) with `z = x + 3 - 2 * a` pins
    `a = x AND 3`, hence `a < 4`. What it buys is an APC's fresh memory send — a value the circuit
    computes rather than echoes — whose byte-ness is not inherited from a receive. -/
theorem isByte_of_xorThree {x z a : ZMod babyBear}
    (hx : isByte x) (hz : z.val = Nat.xor x.val 3) (heq : z = x + 3 - 2 * a) : isByte a := by
  have hx' : ((x.val : ℕ) : ZMod babyBear) = x := by simp
  have hz' : ((z.val : ℕ) : ZMod babyBear) = z := by simp
  have key : (2 : ZMod babyBear) * a = 2 * ((x.val % 4 : ℕ) : ZMod babyBear) := by
    have hc : ((x.val + 3 : ℕ) : ZMod babyBear)
        = ((Nat.xor x.val 3 + 2 * (x.val % 4) : ℕ) : ZMod babyBear) := by rw [xor_three x.val hx]
    push_cast at hc
    rw [hx', ← hz, hz'] at hc
    linear_combination hc + heq
  -- `2` is a unit, so `key` determines `a`; no primality needed.
  have h2inv : (1006632961 : ZMod babyBear) * 2 = 1 := by decide
  have ha : a = ((x.val % 4 : ℕ) : ZMod babyBear) := by
    linear_combination (1006632961 : ZMod babyBear) * key
      - (a - ((x.val % 4 : ℕ) : ZMod babyBear)) * h2inv
  have hmod : x.val % 4 < 4 := Nat.mod_lt _ (by norm_num)
  show a.val < 256
  rw [ha, ZMod.val_natCast_of_lt (lt_trans hmod (by norm_num [babyBear]))]
  omega

/-- Which payload position OpenVM keeps a timestamp in: field `6` of a memory record, field `1` of
    an execution-bridge state. -/
def openVmTsPos : TimestampPos :=
  fun b => if b = openVmMemBusId then some 6 else if b = openVmExecBusId then some 1 else none

theorem openVmReadsTimestampAt : ReadsTimestampAt (p := babyBear) apcRules openVmTsPos := by
  intro m j hj
  simp only [openVmTsPos] at hj
  by_cases hmem : m.1 = openVmMemBusId
  · rw [if_pos hmem] at hj
    cases hj
    simp [apcRules, openVmGuestRules, openVmTimestamp, hmem, List.getD_eq_getElem?_getD]
  · rw [if_neg hmem] at hj
    by_cases hexec : m.1 = openVmExecBusId
    · rw [if_pos hexec] at hj
      cases hj
      simp [apcRules, openVmGuestRules, openVmTimestamp, hexec,
        List.getD_eq_getElem?_getD]
    · rw [if_neg hexec] at hj; cases hj

/-- **`lt_gadget_offset`'s conclusion, in `Recipe` form.** Whatever shape the gadget is in, once
    its two limbs are range-checked and `hi` is pinned to `15360 * (ts + lo - base - k)`, the
    reach is bounded and the timestamp sits where `Recipe.lookback` computes. -/
theorem lookback_of_limbs {asg : ChipAssignment babyBear} {k : ℤ}
    {baseE tsE loE hiE : Expression babyBear}
    (hlo : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [loE.eval asg, 17] })
    (hhi : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [hiE.eval asg, 12] })
    (heq : hiE.eval asg = 15360 * tsE.eval asg + 15360 * loE.eval asg
      - 15360 * baseE.eval asg - 15360 * ((k : ℤ) : ZMod babyBear)) :
    (Recipe.lookback k 131072 loE hiE).back asg < openVmTimestampBound ∧
      tsE.eval asg = baseE.eval asg
        + (((Recipe.lookback k 131072 loE hiE).place asg : ℤ) : ZMod babyBear) := by
  obtain ⟨n, hneq, hn, ht⟩ := lt_gadget_offset k (tsE.eval asg) (baseE.eval asg) hlo hhi heq
  exact ⟨by simpa [Recipe.back, openVmTimestampBound, openVmTimestampBits, ← hneq] using hn,
    by simpa [Recipe.place, ← hneq] using ht⟩

/-- **The lt gadget as powdr's optimizer leaves it, as a `Recipe`.** `AssertLtSubAir` writes the
    distance `n` between a memory receive's timestamp and the step's base as two limbs,
    `lo + 2 ^ 17 * hi`, range-checks them to `17` and `12` bits, and range-checks `hi` as the
    payload `15360 * (ts + lo - base - k)` — `15360` being `-1 / 2 ^ 17` in BabyBear, which is what
    survives once the gadget's own constraint is substituted away.

    The arithmetic is checked (`gadgetIdentity`); the two lookups are supplied. What comes back is
    exactly the pair `hasStepLayout_of_checks` asks of a `lookback` recipe. -/
theorem lookback_of_gadget {vs : List Variable} {rules : List (PinRule babyBear)}
    {baseE : Expression babyBear} {baseF : LinForm babyBear} {k : ℤ}
    {tsE loE hiE : Expression babyBear} {asg : ChipAssignment babyBear}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hbase : Expression.toLin vs rules baseE = some baseF)
    (hid : gadgetIdentity vs rules 15360 baseF k tsE loE hiE = true)
    (hlo : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [loE.eval asg, 17] })
    (hhi : accepts (p := babyBear) defaultBusMap
      { busId := 3, multiplicity := 1, payload := [hiE.eval asg, 12] }) :
    (Recipe.lookback k 131072 loE hiE).back asg < openVmTimestampBound ∧
      tsE.eval asg = baseE.eval asg
        + (((Recipe.lookback k 131072 loE hiE).place asg : ℤ) : ZMod babyBear) :=
  lookback_of_limbs hlo hhi (by rw [gadgetIdentity_sound hrules hbase hid]; ring)

/-- One interaction of a circuit, unpacked from `Circuit.satisfiesStateless`. The message is given
    explicitly and matched against the list entry by `rfl`, which leaves the side conditions as
    `decide`s on concrete field elements. -/
theorem acceptsAt {c : Circuit babyBear} {asg : ChipAssignment babyBear}
    (hacc : c.satisfiesStateless apcRules asg)
    (k : ℕ) (hk : k < c.busInteractions.length)
    (m : BusInteraction (ZMod babyBear)) (hm : (c.busInteractions[k]).eval asg = m)
    (hst : apcRules.isStateful m.busId = false) (hmult : m.multiplicity ≠ 0) :
    accepts defaultBusMap m := by
  subst hm; exact hacc _ (List.getElem_mem hk) hst hmult

--------- The whole step layout, from four checkers ---------

/-- **Read a circuit's bus ids off a precomputed list.** A per-interaction case split that
    `decide`s `(c.busInteractions.get i).busId = …` makes the elaborator whnf the whole circuit
    once per case, which for a twenty-interaction APC exhausts the heartbeat budget. Proving the
    id list once by `rfl` and rewriting through this turns every such check into a lookup in a
    short `Nat` list. -/
theorem busId_get_eq {c : Circuit babyBear} {ids : List Nat}
    (h : c.busInteractions.map (fun bi => bi.busId) = ids)
    (i : Fin c.busInteractions.length) :
    (c.busInteractions.get i).busId = ids.getD i.val 0 := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.get_eq_getElem,
    List.getElem?_eq_getElem i.isLt]
  rfl

/-- **`Circuit.hasStepLayout` from four `Bool`s and the gadget facts.** The bridge, the placement,
    the memory ordering and the byte invariant are each decided against the circuit powdr emitted;
    `tOffset` is the recipes' `place`. What is left for the caller is exactly what a decidable
    check cannot see:

    * `hlook` — where each memory *receive* reaches back to. Nothing in the algebraic constraints
      says; it comes off the lt gadget, and `lookback_of_gadget` returns this pair verbatim.
    * `hext` — why a fresh memory *send* is byte-valued, for the sends `ByteCheck.lean` marks
      `.external`. That is a lookup table's promise, not a shape.
    * the six memory-access clauses a concrete APC discharges off its recipe list and payloads:
      `partner` names the other half of each access (§4.6.1), and the last two say its memory
      sends carry distinct ticks inside `[0, d)`.

    Everything else — which interaction sits where, which are sends, which order they fall in — is
    read off the recipes and the interaction list. `vs` and `vsB` are the variable lists the
    placement and the byte check normalize against; a fused APC wants different ones, since
    `placeCheckAll` reads every stateful payload and `byteCheckAll` only the memory sends. -/
theorem hasStepLayout_of_checks {c : Circuit babyBear}
    {vs vsB : List Variable} {rules : List (PinRule babyBear)}
    {baseE pcFromE pcToE : Expression babyBear} {baseF : LinForm babyBear}
    {R : List (Recipe babyBear)} {W : List ByteWitness}
    {maxWindow d : ℕ} (hd : 0 < d) (hw : d < maxWindow)
    (hrules : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      ∀ q ∈ rules, q.1.eval asg = q.2)
    (hbase : Expression.toLin vs rules baseE = some baseF)
    (hbridge : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.allEffects asg (0, [pcFromE.eval asg, baseE.eval asg]) = -1 ∧
      c.allEffects asg (0, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod babyBear)]) = 1 ∧
      ∀ m : BusMessage babyBear, m.1 = 0 →
        m ≠ (0, [pcFromE.eval asg, baseE.eval asg]) →
        m ≠ (0, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod babyBear)]) →
        c.allEffects asg m = 0)
    (hplace :
      placeCheckAll vs rules apcRules.isStateful openVmTsPos baseF c.busInteractions R = true)
    (horder :
      memOrderCheck rules openVmMemBusId openVmTimestampBound c.busInteractions R = true)
    (hfits : (List.range c.busInteractions.length).all
      (fun i => (R.getD i (.fixed 0)).fits openVmTimestampBound d) = true)
    (hbyte : byteCheckAll vsB rules c.busInteractions W = true)
    (hlook : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg →
      ∀ i : Fin c.busInteractions.length, ∀ (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear),
        R.getD i.val (.fixed 0) = .lookback k radix loE hiE →
        (R.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
          apcRules.getTimestamp (c.msgAt asg i)
            = baseE.eval asg + (((R.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear))
    (hext : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg →
      ∀ i : Fin c.busInteractions.length, W.getD i.val .notSend = .external →
        c.statefulSend apcRules asg i →
        (∀ j : Fin c.busInteractions.length, j < i → c.activeStateful apcRules asg j →
          apcRules.payloadOk (c.msgAt asg j)) →
        apcRules.payloadOk (c.msgAt asg i))
    (hneg : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg → ∀ i : Fin c.busInteractions.length,
      c.activeStateful apcRules asg i → (R.getD i.val (.fixed 0)).place asg < 0 →
        (c.busInteractions.get i).busId = openVmMemBusId ∧ c.multAt asg i = -1)
    (partner : Fin c.busInteractions.length → Fin c.busInteractions.length)
    (hinvol : ∀ i : Fin c.busInteractions.length,
      (c.busInteractions.get i).busId = openVmMemBusId →
        partner (partner i) = i ∧ partner i ≠ i ∧
          (c.busInteractions.get (partner i)).busId = openVmMemBusId)
    (hmult : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg → ∀ i : Fin c.busInteractions.length,
      (c.busInteractions.get i).busId = openVmMemBusId →
        c.multAt asg (partner i) = - c.multAt asg i ∧
        openVmMemAddress (c.msgAt asg i) = openVmMemAddress (c.msgAt asg (partner i)))
    (htime : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg → ∀ i : Fin c.busInteractions.length,
      (c.busInteractions.get i).busId = openVmMemBusId → c.multAt asg i = -1 →
        (R.getD i.val (.fixed 0)).place asg < (R.getD (partner i).val (.fixed 0)).place asg)
    (hdistinct : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg → ∀ i j : Fin c.busInteractions.length,
      c.memSend apcRules asg i → c.memSend apcRules asg j →
        openVmMemAddress (c.msgAt asg i) = openVmMemAddress (c.msgAt asg j) →
        (R.getD i.val (.fixed 0)).place asg = (R.getD j.val (.fixed 0)).place asg → i = j)
    (hwindow : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg → ∀ i : Fin c.busInteractions.length,
      c.memSend apcRules asg i →
        0 ≤ (R.getD i.val (.fixed 0)).place asg ∧
          (R.getD i.val (.fixed 0)).place asg < (d : ℤ)) :
    c.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  have hr := hrules asg halg
  have hback : ∀ i : Fin c.busInteractions.length,
      (R.getD i.val (.fixed 0)).back asg < openVmTimestampBound := by
    intro i
    cases hrc : R.getD i.val (.fixed 0) with
    | fixed k => simp [Recipe.back, openVmTimestampBound, openVmTimestampBits]
    | lookback k radix loE hiE =>
      rw [← hrc]; exact (hlook asg halg hacc i k radix loE hiE hrc).1
  have hfit : ∀ i : Fin c.busInteractions.length,
      (R.getD i.val (.fixed 0)).fits openVmTimestampBound d = true :=
    fun i => List.all_eq_true.mp hfits i.val (List.mem_range.mpr i.isLt)
  obtain ⟨hrecv, hsend, hother⟩ := hbridge asg halg
  refine ⟨⟨_, _, _, d, hd, hw, hrecv, hsend, hother,
    fun i => (R.getD i.val (.fixed 0)).place asg, ?_,
    hdistinct asg halg hacc, hwindow asg halg hacc, hneg asg halg hacc, partner, hinvol,
    hmult asg halg hacc, htime asg halg hacc, ?_⟩⟩
  · exact fun i hi => placeCheck_placed hr hbase openVmReadsTimestampAt rfl hplace i hi
      (hfit i) (hback i) (fun k radix loE hiE hrc => (hlook asg halg hacc i k radix loE hiE hrc).2)
  · intro i hsendI hlow
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk hr hbyte
      (fun i hwit hs hl => hext asg halg hacc i hwit hs hl)) i hsendI ?_
    intro j hji hactj
    exact hlow j (memOrderCheck_sound horder hr (Fin.lt_def.mp hji) hactj.2 hsendI.2
      hsendI.1.2 (hback j) (hback i)) hactj



--------- The raw gadget, before powdr's substitution pass ---------

/-- **The raw `AssertLtSubAir`, before powdr's substitution pass removes it** — reshaped into
    `lt_gadget_offset`'s `15360`-scaled form. Unlike the optimized APC (`lookback_of_gadget`), the
    unoptimized one still carries the gadget's own constraint, so this is a straight substitution
    rather than an inversion. -/
theorem rawGadget_heq {ts prev lo hi : ZMod babyBear} {k : ℤ}
    (hraw : prev = ts + ((k : ℤ) : ZMod babyBear) - lo - 131072 * hi) :
    hi = 15360 * prev + 15360 * lo - 15360 * ts - 15360 * ((k : ℤ) : ZMod babyBear) := by
  have h15 : (15360 : ZMod babyBear) * 131072 = -1 := by decide
  linear_combination (-15360 : ZMod babyBear) * hraw + hi * h15

/-- The raw gadget constraint, gate-cancelled and reshaped into `lt_gadget_offset`'s form: `δ` is
    the read's own send offset (`0` for `rs1`, `1` for arc `3`'s `rs2`, `2` for the write), so
    `lt_gadget_offset`'s `k` is `δ - 1`, matching the substituted gadget's convention on the same
    reads. -/
theorem gadgetLookback_raw {gate ts prev lo hi : ZMod babyBear} {δ : ℤ}
    (hgate : gate = 1)
    (hcon : gate * (ts + ((δ : ℤ) : ZMod babyBear) - prev - 1 - (lo + 131072 * hi)) = 0) :
    hi = 15360 * prev + 15360 * lo - 15360 * ts - 15360 * (((δ - 1 : ℤ) : ℤ) : ZMod babyBear) := by
  rw [hgate, one_mul] at hcon
  refine rawGadget_heq (k := δ - 1) ?_
  push_cast
  linear_combination -hcon

/-- A one-hot flag sum, in the exact left-folded `0 + a + b + c + d + e` shape
    `Expression.eval` produces, is nonzero once it is known to be `1`. -/
theorem sum5_eq1_ne_zero {a b c d e : ZMod babyBear} (h : a + b + c + d + e = 1) :
    (0 + a + b + c + d + e : ZMod babyBear) ≠ 0 := by
  rw [show (0 + a + b + c + d + e : ZMod babyBear) = 1 from by linear_combination h]
  decide

/-- The two-flag (branch) analogue of `sum5_eq1_ne_zero`. -/
theorem sum2_eq1_ne_zero {a b : ZMod babyBear} (h : a + b = 1) :
    (0 + a + b : ZMod babyBear) ≠ 0 := by
  rw [show (0 + a + b : ZMod babyBear) = 1 from by linear_combination h]
  decide

/-- On bus `3` (`variableRangeChecker`), `accepts` never inspects `multiplicity`, so a fact about
    one multiplicity transports to any other. Unlike the memory bus, this arm of
    `OpenVmSemantics.accepts` does not branch on it. -/
theorem accepts_congr_mult3 {m1 m2 x k : ZMod babyBear}
    (h : accepts (p := babyBear) defaultBusMap ⟨3, m1, [x, k]⟩) :
    accepts (p := babyBear) defaultBusMap ⟨3, m2, [x, k]⟩ := h

--------- The bitwise table's byte guarantees ---------

/-- On bus `6` (`bitwiseLookup`), `accepts` never inspects `multiplicity`, mirroring
    `accepts_congr_mult3` for the range checker. -/
theorem accepts_congr_mult6 {m1 m2 x y z op : ZMod babyBear}
    (h : accepts (p := babyBear) defaultBusMap ⟨6, m1, [x, y, z, op]⟩) :
    accepts (p := babyBear) defaultBusMap ⟨6, m2, [x, y, z, op]⟩ := h

/-- What a `bitwiseLookup` table row at `op = 1` promises, read directly off `accepts`. -/
theorem bitwiseTable_extract {x y z : ZMod babyBear}
    (h : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1, payload := [x, y, z, 1] }) :
    isByte x ∧ isByte y ∧ z.val = Nat.xor x.val y.val := h

/-- **The two arithmetic identities OpenVM's OR/AND masking tricks rest on**, plus the byte bound
    each needs: for bytes `x, y`, `x + y` splits into `xor x y` and twice `land x y`, `lor x y`
    is half of `x + y + xor x y`, and both `lor` and `land` of two bytes are themselves bytes. -/
theorem bitwiseByteIdentities : ∀ x < 256, ∀ y < 256,
    x + y = Nat.xor x y + 2 * Nat.land x y ∧
    2 * Nat.lor x y = x + y + Nat.xor x y ∧
    Nat.lor x y < 256 ∧ Nat.land x y < 256 := by decide

/-- **`x XOR y` is a byte, from the bitwise table alone**, when a third value is pinned to it. -/
theorem isByte_of_xorEq {x y z a : ZMod babyBear} (hx : isByte x) (hy : isByte y)
    (hxor : z.val = Nat.xor x.val y.val) (heq : z = a) : isByte a := by
  rw [← heq]
  show z.val < 256
  rw [hxor]
  have hx8 : x.val < 2 ^ 8 := by simpa using hx
  have hy8 : y.val < 2 ^ 8 := by simpa using hy
  simpa using Nat.xor_lt_two_pow hx8 hy8

/-- **`x OR y` is a byte**: `2a = x + y + (x xor y)` forces `a = x ||| y` via `bitwiseByteIdentities`
    and `2`'s invertibility, the same shape as `isByte_of_xorThree`. -/
theorem isByte_of_orEq {x y z a : ZMod babyBear} (hx : isByte x) (hy : isByte y)
    (hxor : z.val = Nat.xor x.val y.val) (heq : z = 2 * a - x - y) : isByte a := by
  obtain ⟨-, hlor, hlorLt, -⟩ := bitwiseByteIdentities x.val hx y.val hy
  have hxv : ((x.val : ℕ) : ZMod babyBear) = x := by simp
  have hyv : ((y.val : ℕ) : ZMod babyBear) = y := by simp
  have hzv : ((z.val : ℕ) : ZMod babyBear) = z := by simp
  have hcast : ((x.val + y.val + Nat.xor x.val y.val : ℕ) : ZMod babyBear)
      = ((2 * Nat.lor x.val y.val : ℕ) : ZMod babyBear) := by rw [hlor]
  push_cast at hcast
  rw [hxv, hyv, ← hxor, hzv] at hcast
  have h2a : (2 : ZMod babyBear) * a = 2 * ((Nat.lor x.val y.val : ℕ) : ZMod babyBear) := by
    linear_combination hcast - heq
  have h2inv : (1006632961 : ZMod babyBear) * 2 = 1 := by decide
  have ha : a = ((Nat.lor x.val y.val : ℕ) : ZMod babyBear) := by
    linear_combination (1006632961 : ZMod babyBear) * h2a
      - (a - ((Nat.lor x.val y.val : ℕ) : ZMod babyBear)) * h2inv
  show a.val < 256
  rw [ha, ZMod.val_natCast_of_lt (lt_trans hlorLt (by norm_num [babyBear]))]
  exact hlorLt

/-- **`x AND y` is a byte**: `2a = x + y - (x xor y)` forces `a = x &&& y`, dually to
    `isByte_of_orEq`. -/
theorem isByte_of_andEq {x y z a : ZMod babyBear} (hx : isByte x) (hy : isByte y)
    (hxor : z.val = Nat.xor x.val y.val) (heq : z = x + y - 2 * a) : isByte a := by
  obtain ⟨hland, -, -, hlandLt⟩ := bitwiseByteIdentities x.val hx y.val hy
  have hxv : ((x.val : ℕ) : ZMod babyBear) = x := by simp
  have hyv : ((y.val : ℕ) : ZMod babyBear) = y := by simp
  have hzv : ((z.val : ℕ) : ZMod babyBear) = z := by simp
  have hcast : ((x.val + y.val : ℕ) : ZMod babyBear)
      = ((Nat.xor x.val y.val + 2 * Nat.land x.val y.val : ℕ) : ZMod babyBear) := by rw [hland]
  push_cast at hcast
  rw [hxv, hyv, ← hxor, hzv] at hcast
  have h2a : (2 : ZMod babyBear) * a = 2 * ((Nat.land x.val y.val : ℕ) : ZMod babyBear) := by
    linear_combination heq + hcast
  have h2inv : (1006632961 : ZMod babyBear) * 2 = 1 := by decide
  have ha : a = ((Nat.land x.val y.val : ℕ) : ZMod babyBear) := by
    linear_combination (1006632961 : ZMod babyBear) * h2a
      - (a - ((Nat.land x.val y.val : ℕ) : ZMod babyBear)) * h2inv
  show a.val < 256
  rw [ha, ZMod.val_natCast_of_lt (lt_trans hlandLt (by norm_num [babyBear]))]
  exact hlandLt

/-- **A boolean-constrained field element is `0` or `1`.** `babyBear` is prime (`norm_num`'s
    primality extension, not the plain `decide` the rest of this file uses — trial division to
    `√babyBear` is well past `decide`'s reach), so `ZMod babyBear` has no zero divisors and
    `x * (x - 1) = 0` splits. Kept separate from `aluOneHot` so the `Fact (Nat.Prime babyBear)`
    instance doesn't linger in scope for that theorem's closing `decide`. -/
theorem zmod_boolElim {x : ZMod babyBear} (hx : x * (x + 2013265920 * 1) = 0) :
    x = 0 ∨ x = 1 := by
  haveI : Fact (Nat.Prime babyBear) := ⟨by norm_num [babyBear]⟩
  rw [babyBear_negOne] at hx
  rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-- **One-hot decomposition of a 5-way opcode selector.** Booleanity plus a sum of `1` forces
    exactly one flag to be `1`; `decide` closes each of the `32` literal cases the case split
    produces (`27` contradict the sum, `5` match a disjunct). -/
theorem aluOneHot {add sub xorf orf andf : ZMod babyBear}
    (hsum : add + sub + xorf + orf + andf = 1)
    (hb_add : add * (add + 2013265920 * 1) = 0)
    (hb_sub : sub * (sub + 2013265920 * 1) = 0)
    (hb_xor : xorf * (xorf + 2013265920 * 1) = 0)
    (hb_or : orf * (orf + 2013265920 * 1) = 0)
    (hb_and : andf * (andf + 2013265920 * 1) = 0) :
    (add = 1 ∧ sub = 0 ∧ xorf = 0 ∧ orf = 0 ∧ andf = 0) ∨
    (add = 0 ∧ sub = 1 ∧ xorf = 0 ∧ orf = 0 ∧ andf = 0) ∨
    (add = 0 ∧ sub = 0 ∧ xorf = 1 ∧ orf = 0 ∧ andf = 0) ∨
    (add = 0 ∧ sub = 0 ∧ xorf = 0 ∧ orf = 1 ∧ andf = 0) ∨
    (add = 0 ∧ sub = 0 ∧ xorf = 0 ∧ orf = 0 ∧ andf = 1) := by
  rcases zmod_boolElim hb_add with ha | ha <;> rcases zmod_boolElim hb_sub with hs | hs <;>
    rcases zmod_boolElim hb_xor with hx | hx <;> rcases zmod_boolElim hb_or with ho | ho <;>
    rcases zmod_boolElim hb_and with hn | hn <;>
    subst ha <;> subst hs <;> subst hx <;> subst ho <;> subst hn <;>
    revert hsum <;> decide

/-- **The ALU result of one limb is a byte, whichever of the five ops is active.** `add`/`sub`
    put it directly at the table's first position; `xor` puts it at the table's output; `or`/`and`
    recover it from the output via `isByte_of_orEq`/`isByte_of_andEq`. -/
theorem isByte_of_aluLimb {add sub xorf orf andf a b c x y z : ZMod babyBear}
    (hcase : (add = 1 ∧ sub = 0 ∧ xorf = 0 ∧ orf = 0 ∧ andf = 0) ∨
             (add = 0 ∧ sub = 1 ∧ xorf = 0 ∧ orf = 0 ∧ andf = 0) ∨
             (add = 0 ∧ sub = 0 ∧ xorf = 1 ∧ orf = 0 ∧ andf = 0) ∨
             (add = 0 ∧ sub = 0 ∧ xorf = 0 ∧ orf = 1 ∧ andf = 0) ∨
             (add = 0 ∧ sub = 0 ∧ xorf = 0 ∧ orf = 0 ∧ andf = 1))
    (hbx : isByte x) (hby : isByte y) (hxy : z.val = Nat.xor x.val y.val)
    (hx : x = (1 + 2013265920 * (xorf + orf + andf)) * a + (xorf + orf + andf) * b)
    (hy : y = (1 + 2013265920 * (xorf + orf + andf)) * a + (xorf + orf + andf) * c)
    (hz : z = xorf * a + orf * (2 * a + 2013265920 * b + 2013265920 * c)
              + andf * (b + c + 2013265920 * (2 * a))) :
    isByte a := by
  rw [babyBear_negOne] at hx hy hz
  rcases hcase with ⟨e1,e2,e3,e4,e5⟩|⟨e1,e2,e3,e4,e5⟩|⟨e1,e2,e3,e4,e5⟩|⟨e1,e2,e3,e4,e5⟩|⟨e1,e2,e3,e4,e5⟩ <;>
    subst e1 <;> subst e2 <;> subst e3 <;> subst e4 <;> subst e5
  · exact (show x = a by linear_combination hx) ▸ hbx
  · exact (show x = a by linear_combination hx) ▸ hbx
  · exact isByte_of_xorEq hbx hby hxy (by linear_combination hz)
  · exact isByte_of_orEq hbx hby hxy (by rw [hx, hy]; linear_combination hz)
  · exact isByte_of_andEq hbx hby hxy (by rw [hx, hy]; linear_combination hz)

end ApcOptimizer.OpenVM
