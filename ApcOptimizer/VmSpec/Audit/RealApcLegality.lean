import ApcOptimizer.VmSpec.Audit.Apc2105000
import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity
import ApcOptimizer.VmSpec.Audit.BridgeCheck
import ApcOptimizer.VmSpec.Audit.PlaceCheck
import ApcOptimizer.VmSpec.Audit.ByteCheck
import ApcOptimizer.VmSpec.Audit.OpenVmLegalAudit
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **`Circuit.legalGuest` measured against real APCs.**

    `Audit/OpenVmLegalAudit.lean` checks the legality clauses against hand-written chips in the
    shape a real OpenVM AIR has. This file does the same against circuits nobody wrote by hand:
    the keccak basic block at pc `2105000`, at three points in powdr's own optimizer pipeline
    (`Apc2105000.lean`, emitted from the stage dumps by `Scripts/emit-apc-lean.py`). Same block,
    same semantics, three forms — so a difference between two results is a statement about the
    optimizer, not about the block.

    | | `apc2105000Unopt` (`000_unopt`) | `apc2105000Opt` (`039_trivial_simp`) | `apc2105000Gated` (`040`) |
    | --- | --- | --- | --- |
    | `statelessSendOnly` | **true** | **true** | true, out of checker reach |
    | `statefulPolarity` | **true** | **true** | true, out of checker reach |
    | `hasStepLayout` | four steps, so **false** | **true**, one step | **false**, padding row |

    Every "true" above is discharged by `Audit/SendOnlyPolarity.lean`'s decidable checker and its
    soundness theorem — a `Bool` and a `rfl`, with no case analysis over the circuit written by
    hand. The optimized APC needs only the constant-folding tier; the unoptimized one needs the
    constant-propagation tier, since its multiplicities are opcode-flag sums that are legal only
    because a constraint pins them.

    **Why `039` and not the pipeline's final output.** The last pass introduces a fresh `is_valid`
    column and multiplies every multiplicity by it, which puts the circuit out of the multiplicity
    checker's reach (`apc2105000Gated_checkMultiplicities_fails`): `Expression.foldConst` returns
    `none` on a bare variable, and the booleanity constraint `is_valid * (is_valid - 1) = 0` is not
    linear, so no pin rule comes off it either. Stage `039` is that same circuit one pass earlier —
    identical bus interactions and constraints, multiplicities the literal `±1`.

    The padding row that gate introduces also makes `040` fail `hasStepLayout` outright
    (`apc2105000Gated_not_hasStepLayout`): the all-zero assignment is algebraically satisfying and
    nets `0` on the bridge, where a step's receive must net `-1`. Closing that is a change to the
    circuit — pin `is_valid` — not to the clause.

    `apc2105000Unopt` fails for an unrelated reason: it is four instruction steps whose
    intermediate bridge states do not cancel, because powdr leaves `from_state__timestamp_0..3`
    algebraically unrelated until its substitution pass runs. Adding
    `from_state__timestamp_{i+1} = from_state__timestamp_i + d_i` collapses it to the one step
    `039` already has.

    **What a real APC's memory traffic looks like, and why the clause admits it.** Every memory
    *receive* sits at a free `*_prev_timestamp_*` column — the record an earlier instruction left,
    which the AssertLt gadget constrains only to be *less than* the access — and the first memory
    *send* sits at `from_state__timestamp_0 + 0`, i.e. exactly at the step's base. Neither fits
    the old `Circuit.advancesClock`, which demanded that memory sit strictly inside
    `(base, base + d)`; both fit `StepLayout`, which places an interaction at any integer offset
    in `[-maxLookback, d]` and orders only the sends. That is what
    `apc2105000Opt_hasStepLayout` exhibits, and it closes the memory half of finding G.

    See `agent-docs/vm-spec.md`. -/

namespace ApcOptimizer.OpenVM

/-! `Spec.lean` assumes primality of the characteristic for every `p` it quantifies over. These
    circuits sit at the literal `babyBear`, so the one theorem that needs `ZMod babyBear` to be a
    field takes the same assumption as an instance hypothesis rather than re-proving it (Mathlib's
    `norm_num` primality extension is not built in this checkout). -/

/-- The rules all three circuits are checked against: OpenVM's own bus map, memory on bus `1`. -/
abbrev apcRules : GuestBusRules babyBear :=
  openVmGuestRules defaultBusMap openVmMemBusId

/-- powdr emits `-1` as the literal `p - 1`; the two are the same field element. -/
theorem babyBear_negOne : (2013265920 : ZMod babyBear) = -1 := by decide

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
    `a = x AND 3`, hence `a < 4`. This is `apc2105000Opt`'s only fresh memory send — a value the
    APC computes rather than echoes — and the one place its byte-ness is not inherited from a
    receive. -/
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

--------- The optimized APC: both multiplicity clauses, by static analysis ---------

/-- **The static check passes on a real optimized APC.** Every multiplicity stage `039` carries is
    a field literal, so `Expression.foldConst` — `Audit/SendOnlyPolarity.lean`'s first and only
    tier — resolves all 23 of them, and `decide` closes the check in the kernel. No case analysis
    over the circuit is written by hand. -/
theorem apc2105000Opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful apc2105000Opt = true := by decide

/-- **Both multiplicity clauses of `Circuit.legalGuest`, for a real optimized APC**, discharged by
    `checkMultiplicities_sound` from the `Bool` above rather than by a proof about this particular
    circuit. -/
theorem apc2105000Opt_legalMultiplicities :
    apc2105000Opt.statelessSendOnly apcRules ∧ apc2105000Opt.statefulPolarity apcRules :=
  checkMultiplicities_sound apc2105000Opt_checkMultiplicities rfl

/-- **The checker does not reach the pipeline's final output.** `apc2105000Gated`'s multiplicities
    are `±is_valid`, and `Expression.foldConst` returns `none` on a bare variable, so the check
    fails on a circuit whose clauses are in fact true — reachable only through the booleanity
    constraint `is_valid * (is_valid - 1) = 0`. That is precisely the second tier
    `Audit/SendOnlyPolarity.lean`'s docstring names and does not attempt, and powdr's last pass is
    what moves the circuit out of the first tier's reach. -/
theorem apc2105000Gated_checkMultiplicities_fails :
    checkMultiplicities apcRules.isStateful apc2105000Gated = false := by decide

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment — so unlike `apc2105000Gated_not_hasStepLayout`'s row, no
    assignment makes this circuit silent. -/
theorem apc2105000Opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ apc2105000Opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (apc2105000Opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [apc2105000Opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

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

/-- **The lt gadget, as a `Recipe`.** OpenVM's `AssertLtSubAir` writes the distance `n` between a
    memory receive's timestamp and the step's base as two limbs, `lo + 2 ^ 17 * hi`, range-checks
    them to `17` and `12` bits, and range-checks `hi` as the payload
    `15360 * (ts + lo - base - k)` — `15360` being `-1 / 2 ^ 17` in BabyBear, which is what the
    optimizer leaves once the gadget's own constraint is substituted away.

    The arithmetic is checked (`gadgetIdentity`); the two lookups are supplied. What comes back is
    exactly what `Recipe.lookback` needs: the reach is bounded, and the timestamp sits at the
    offset the recipe computes. -/
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
      tsE.eval asg
        = baseE.eval asg
          + ((((Recipe.lookback k 131072 loE hiE).place asg : ℤ)) : ZMod babyBear) := by
  obtain ⟨n, hneq, hn, ht⟩ := lt_gadget_offset k (tsE.eval asg) (baseE.eval asg) hlo hhi
    (by rw [gadgetIdentity_sound hrules hbase hid]; ring)
  refine ⟨?_, ?_⟩
  · simpa [Recipe.back, openVmTimestampBound, openVmTimestampBits, ← hneq] using hn
  · simpa [Recipe.place, ← hneq] using ht

/-- One interaction of `apc2105000Opt`, unpacked from `Circuit.satisfiesStateless`. The message is
    given explicitly and matched against the list entry by `rfl`, which leaves the side conditions
    as `decide`s on concrete field elements. -/
theorem optAccepts {asg : ChipAssignment babyBear}
    (hacc : apc2105000Opt.satisfiesStateless apcRules asg)
    (k : ℕ) (hk : k < apc2105000Opt.busInteractions.length)
    (m : BusInteraction (ZMod babyBear)) (hm : (apc2105000Opt.busInteractions[k]).eval asg = m)
    (hst : apcRules.isStateful m.busId = false) (hmult : m.multiplicity ≠ 0) :
    accepts defaultBusMap m := by
  subst hm; exact hacc _ (List.getElem_mem hk) hst hmult

/-- Where each of `apc2105000Opt`'s twelve stateful interactions sits, as an offset from the step's
    `from_state__timestamp_0`. Positions `7` and `13`–`22` are the stateless lookups and never read.
    The five receives look back by their own gadget's `n`; the six sends and the bridge receive sit
    at literal offsets. -/
def optOffsets (n0 nw0 nr1 nw1 nr3 : ℕ) : List ℤ :=
  [-1 - (n0 : ℤ), 0, 1 - nw0, 0, 2 - nr1, 4 - nw1, 5, 0, 6, 9, 9 - nr3, 10, 11]

/-- The largest offset each position can hold: a receive's is `δ - n` for a lookback `n ≥ 0`, so
    `δ` bounds it; the six sends attain their entry exactly. -/
def optOffsetUb : List ℤ := [-1, 0, 1, 0, 2, 4, 5, 0, 6, 9, 9, 10, 11]

/-- Each of the six sends dominates every position before it. With `optOffsetUb` this is the whole
    of `StepLayout.ordered` for this circuit — a `decide` over positions, which is what stating the
    layout in integer offsets rather than field timestamps buys. -/
theorem optOffsetUb_dominates :
    ∀ b ∈ [1, 6, 8, 9, 11, 12], ∀ k < b, optOffsetUb.getD k 0 < optOffsetUb.getD b 0 := by decide

/-- The variables the optimized APC's stateful payloads and lt gadgets mention: the step's base,
    the branch flag the outgoing `pc` depends on, and each gadget's `prev_timestamp` and low
    decomposition limb. -/
def optVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_3", some 126⟩,
   ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩,
   ⟨"writes_aux__base__prev_timestamp_0", some 12⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩,
   ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩,
   ⟨"writes_aux__base__prev_timestamp_1", some 48⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩,
   ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩,
   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩,
   ⟨"a__0_0", some 19⟩, ⟨"a__1_0", some 20⟩, ⟨"a__2_0", some 21⟩, ⟨"a__3_0", some 22⟩,
   ⟨"a__0_1", some 55⟩, ⟨"a__1_1", some 56⟩, ⟨"a__2_1", some 57⟩, ⟨"a__3_1", some 58⟩,
   ⟨"a__0_2", some 91⟩]

/-- The step's base, as an expression and as a normal form. -/
def optBaseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def optBaseF : LinForm babyBear := LinForm.varF optVars ⟨"from_state__timestamp_0", some 1⟩

/-- The pin rules the optimized APC's own constraints supply. -/
def optPinRules : List (PinRule babyBear) :=
  apc2105000Opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : apc2105000Opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

/-- **The bridge half of the layout, by static analysis.** No case analysis over the circuit is
    written by hand: `bridgeCheck` normalizes the two bus-`0` payloads, sees the receive first and
    the send last with nothing between them, reads `d = 11` off the timestamps, and separates the
    two endpoints at payload position `1` — they carry the same coefficient on
    `from_state__timestamp_0` and differ by the constant `11`.

    The three expressions name the endpoints, and the checker verifies them against the traffic, so
    `bridgeCheck_sound` hands back facts about exactly these messages. -/
theorem optBaseLin : Expression.toLin optVars optPinRules optBaseE = some optBaseF := by decide

theorem optBridgeCheck :
    bridgeCheck optVars optPinRules 0 apc2105000Opt 11 1
        (.const 2105000)
        optBaseE
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

/-- Why each of `apc2105000Opt`'s interactions is `payloadOk`, position by position: six memory
    receives and the bridge receive are not sends; three memory sends echo the read that preceded
    them; one writes literal zeros; the bridge send is not on the memory bus; ten lookups are not
    stateful. Only the masked write at position `9` is left to the caller — it is a byte because
    the bitwise table says so, which is where a decidable check stops. -/
def optWitnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend,
   .echo 0, .external, .notSend, .limbs, .notMemory] ++ List.replicate 10 .notSend

theorem optByteCheck :
    byteCheckAll optVars optPinRules apc2105000Opt.busInteractions optWitnesses = true := by decide

/-- **A real optimized APC has a step layout.** One arc — `(2105000, t) → (2105016 - 192·cmp,
    t + 11)` — and the twelve stateful interactions placed at `optOffsets`, read off the five
    surviving lt gadgets (`lt_gadget_offset`). Its five memory sends are byte-valued: four echo a
    receive earlier in the same step, and the fifth is the masked value the bitwise table checks
    (`isByte_of_xorThree`).

    This is finding G's memory half, closed. The clause the old `Circuit.advancesClock` failed on
    every APC — memory strictly inside `(base, base + d)` — is gone; what replaces it, an integer
    offset in `[-2 ^ 29, 11]` with the sends ordered, this circuit satisfies. -/
theorem apc2105000Opt_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    apc2105000Opt.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  obtain ⟨n0, hn0, ht0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := optPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf apc2105000Opt 13 0) (hiE := payloadOf apc2105000Opt 14 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (optAccepts hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (optAccepts hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw0, hnw0, htw0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := optPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf apc2105000Opt 15 0) (hiE := payloadOf apc2105000Opt 16 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (optAccepts hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (optAccepts hacc 16 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((2 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := optPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
      (loE := payloadOf apc2105000Opt 17 0) (hiE := payloadOf apc2105000Opt 18 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (optAccepts hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (optAccepts hacc 18 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw1, hnw1, htw1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((4 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := optPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 4)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf apc2105000Opt 19 0) (hiE := payloadOf apc2105000Opt 20 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (optAccepts hacc 19 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (optAccepts hacc 20 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr3, hnr3, htr3⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((9 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := optPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 9)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
      (loE := payloadOf apc2105000Opt 21 0) (hiE := payloadOf apc2105000Opt 22 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (optAccepts hacc 21 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (optAccepts hacc 22 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"a__0_0", some 19⟩, 3,
          asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩), 1] } :=
    optAccepts hacc 7 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  replace hbit : isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (3 : ZMod babyBear) ∧
      (asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩)).val
        = Nat.xor (asg ⟨"a__0_0", some 19⟩).val (3 : ZMod babyBear).val := hbit
  have ha02 : isByte (asg ⟨"a__0_2", some 91⟩) :=
    isByte_of_xorThree hbit.1
      (by rw [hbit.2.2, show (3 : ZMod babyBear).val = 3 from by decide])
      (by linear_combination (2 * asg ⟨"a__0_2", some 91⟩) * babyBear_negOne)
  have hub : ∀ i : Fin apc2105000Opt.busInteractions.length,
      apcRules.isStateful (apc2105000Opt.busInteractions.get i).busId = true →
      ((apc2105000Opt.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0 ≤ optOffsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [optOffsets, optOffsetUb, apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin apc2105000Opt.busInteractions.length,
      apcRules.isStateful (apc2105000Opt.busInteractions.get i).busId = true →
      ((apc2105000Opt.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [1, 6, 8, 9, 11, 12] ∧
      (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0 = optOffsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [optOffsets, optOffsetUb, apc2105000Opt, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful, BusInteraction.eval,
        Expression.eval, babyBear_negOne_ne_one]
  -- The bridge, by static analysis: `optBridgeCheck` is a `decide`.
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg)
  refine ⟨_, _, _, 11, by norm_num, hw, hrecv, hsend, hother,
    fun i => (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using ht0⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw0⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId,
          openVmExecBusId]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr1⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw1⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr3⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000Opt, BusInteraction.eval, Expression.eval, apcRules,
          openVmGuestRules, openVmTimestamp, Circuit.msgAt, openVmMemBusId,
          openVmExecBusId]⟩
    all_goals
      simp [apc2105000Opt, apcRules, openVmGuestRules, openVmIsStateful, defaultBusMap,
        OpenVmBusType.isStateful] at hst
  · -- The byte invariant, by static analysis: only the masked write is left by hand. What used to
    -- be `memOrdered` (`optOffsetUb_dominates`) is inlined here, converting the caller's
    -- `place`-ordered hypothesis into the index order `byteCheck_sendsOk` expects.
    intro i hsend hlow
    have hordered : ∀ j : Fin apc2105000Opt.busInteractions.length, j < i →
        apc2105000Opt.activeMem apcRules asg j →
        apcRules.payloadOk (apc2105000Opt.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.1.2
      refine hlow j ?_ hactj
      show (optOffsets n0 nw0 nr1 nw1 nr3).getD j.val 0
        < (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj.1.1 hactj.1.2)
        (optOffsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (optPinRules_hold asg halg) optByteCheck ?_)
      i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
      asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

theorem apc2105000Opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    apc2105000Opt.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := apc2105000Opt_legalMultiplicities.1
  polarity := apc2105000Opt_legalMultiplicities.2
  stepLayout := apc2105000Opt_hasStepLayout hw
  size := by simpa [apc2105000Opt] using hi

--------- The unoptimized APC: same clauses, via constant propagation ---------

/-- **The strengthened check passes on the unoptimized APC.** Its multiplicities are not literals —
    each is a sum of that instruction's opcode flags, or an operand's address space — so
    `checkMultiplicities` cannot see them. `checkMultiplicitiesWith` reads 27 pin rules off the
    constraints, among them `1 - (add + sub + xor + or + and) = 0` (the flag sum is `1`) and
    `rs2_as_i - 0 = 0` (that operand is an immediate), and every one of the 71 multiplicities folds
    against them. -/
theorem apc2105000Unopt_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful apc2105000Unopt = true := by decide

/-- **Both multiplicity clauses for the unoptimized APC**, again from the `Bool` rather than from a
    proof about this circuit. With `apc2105000Opt_legalMultiplicities` this says the two clauses
    survive powdr's optimizer on this block — the interesting direction for `PreservesLegality`. -/
theorem apc2105000Unopt_legalMultiplicities :
    apc2105000Unopt.statelessSendOnly apcRules ∧ apc2105000Unopt.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound apc2105000Unopt_checkMultiplicitiesWith rfl

--------- The gated APC: the padding row kills `hasStepLayout` ---------

/-- **The padding row.** Every column zero satisfies the gated APC's four constraints: they are
    `cmp * (cmp - 1)`, `(1 - cmp) * a`, `free * a - cmp`, and `is_valid * (is_valid - 1)`, each of
    which vanishes at `0`. Nothing pins `is_valid` to `1`. -/
theorem apc2105000Gated_satisfiesAlgebraic_zero :
    apc2105000Gated.satisfiesAlgebraic (fun _ => 0) := by
  intro c hc
  simp only [apc2105000Gated, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [Expression.eval]

/-- On that row the gated APC is silent: every multiplicity is `±is_valid`, which is `0`. -/
theorem apc2105000Gated_mults_zero_on_padding :
    ∀ bi ∈ apc2105000Gated.busInteractions,
      (bi.eval (fun _ => 0)).multiplicity = 0 := by
  intro bi hbi
  simp only [apc2105000Gated, List.mem_cons, List.not_mem_nil, or_false] at hbi
  rcases hbi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [BusInteraction.eval, Expression.eval]

/-- **Finding G1, still open: the padding row has no step layout.** powdr's optimizer replaces each
    fused instruction's pinned opcode-flag sum with one fresh `is_valid` column carrying only
    `is_valid * (is_valid - 1) = 0`, so the all-zero assignment is algebraically satisfying and the
    circuit nets `0` on every message of every bus. `StepLayout` asks for a bridge receive netting
    `-1` on *every* algebraically-satisfying assignment, and this row cannot supply one.

    The unoptimized APC has no such row (`apc2105000Unopt_zero_not_satisfiesAlgebraic`) — same
    block, same semantics, so **the optimization is what breaks legality**, which makes this the
    legality-preservation gap of `agent-docs/vm-spec.md` observed in the wild rather than
    constructed. Closing it is a change to the *circuit* (pin `is_valid`), not to the clause. -/
theorem apc2105000Gated_not_hasStepLayout {maxWindow maxLookback : ℕ} :
    ¬ apc2105000Gated.hasStepLayout apcRules maxWindow maxLookback := by
  intro h
  obtain ⟨L⟩ := h (fun _ => 0) apc2105000Gated_satisfiesAlgebraic_zero
    (fun bi hbi _ hmult => absurd (apc2105000Gated_mults_zero_on_padding bi hbi) hmult)
  exact babyBear_negOne_ne_zero
    (L.bridgeRecv.symm.trans (allEffects_eq_zero_of_mults_zero apc2105000Gated_mults_zero_on_padding _))

/-- **The unoptimized APC has no padding row either**: it pins each fused instruction's opcode-flag
    sum to `1` (`1 - (add + sub + xor + or + and) = 0`, one per instruction). -/
theorem apc2105000Unopt_zero_not_satisfiesAlgebraic :
    ¬ apc2105000Unopt.satisfiesAlgebraic (fun _ => 0) := by
  intro h
  have := h
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
          (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
          (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))
      (.const 1))
    (by simp [apc2105000Unopt])
  simp only [Expression.eval] at this
  exact absurd this (by decide)

--------- The gated APC, with `is_valid` pinned: proved, closing finding G1 in full ---------

/-- **`apc2105000Gated` fails `hasStepLayout` only because `is_valid` is unpinned** — pin it, and
    every clause the checkers proved for `apc2105000Opt` carries over verbatim: `apc2105000Gated`
    is `apc2105000Opt`'s own algebraic constraints and bus interactions, each multiplicity
    additionally scaled by `is_valid`, which folds away to the literal it already was. -/
def gatedPinRules : List (PinRule babyBear) :=
  apc2105000GatedPinned.algebraicConstraints.filterMap pinRuleOf

theorem gatedPinRules_hold (asg : ChipAssignment babyBear)
    (halg : apc2105000GatedPinned.satisfiesAlgebraic asg) :
    ∀ q ∈ gatedPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem gatedIsValid {asg : ChipAssignment babyBear}
    (halg : apc2105000GatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 137⟩ = 1 :=
  gatedPinRules_hold asg halg (.var ⟨"is_valid", some 137⟩, 1) (by decide)

theorem gatedIsValid_ne_zero {asg : ChipAssignment babyBear}
    (halg : apc2105000GatedPinned.satisfiesAlgebraic asg) :
    asg ⟨"is_valid", some 137⟩ ≠ 0 := by
  rw [gatedIsValid halg]; exact (show (1 : ZMod babyBear) ≠ 0 by decide)

/-- **The strengthened check passes, `is_valid` pinned.** Same shape as `apc2105000Unopt`'s: every
    multiplicity is a literal times `is_valid`, legal only because the pin says `is_valid = 1`. -/
theorem apc2105000GatedPinned_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful apc2105000GatedPinned = true := by decide

theorem apc2105000GatedPinned_legalMultiplicities :
    apc2105000GatedPinned.statelessSendOnly apcRules ∧
      apc2105000GatedPinned.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound apc2105000GatedPinned_checkMultiplicitiesWith rfl

theorem gatedAccepts {asg : ChipAssignment babyBear}
    (hacc : apc2105000GatedPinned.satisfiesStateless apcRules asg)
    (k : ℕ) (hk : k < apc2105000GatedPinned.busInteractions.length)
    (m : BusInteraction (ZMod babyBear))
    (hm : (apc2105000GatedPinned.busInteractions[k]).eval asg = m)
    (hst : apcRules.isStateful m.busId = false) (hmult : m.multiplicity ≠ 0) :
    accepts defaultBusMap m := by
  subst hm; exact hacc _ (List.getElem_mem hk) hst hmult

theorem gatedBaseLin : Expression.toLin optVars gatedPinRules optBaseE = some optBaseF := by decide

theorem gatedBridgeCheck :
    bridgeCheck optVars gatedPinRules 0 apc2105000GatedPinned 11 1
        (.const 2105000)
        optBaseE
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

theorem gatedByteCheck :
    byteCheckAll optVars gatedPinRules apc2105000GatedPinned.busInteractions optWitnesses = true := by
  decide

/-- **A pinned gated APC has a step layout.** Identical in shape to `apc2105000Opt_hasStepLayout`
    — same offsets, same gadgets, same byte witnesses — since pinning `is_valid` is exactly what
    collapses `apc2105000GatedPinned` back to `apc2105000Opt`'s multiplicities. -/
theorem apc2105000GatedPinned_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    apc2105000GatedPinned.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  have hiv := gatedIsValid halg
  have hivne := gatedIsValid_ne_zero halg
  obtain ⟨n0, hn0, ht0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc13 := gatedAccepts hacc 13 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc14 := gatedAccepts hacc 14 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [apc2105000GatedPinned, apc2105000Gated, BusInteraction.eval] at hacc13 hacc14
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := gatedPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf apc2105000GatedPinned 13 0) (hiE := payloadOf apc2105000GatedPinned 14 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc13
      hacc14
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw0, hnw0, htw0⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((1 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc15 := gatedAccepts hacc 15 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc16 := gatedAccepts hacc 16 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [apc2105000GatedPinned, apc2105000Gated, BusInteraction.eval] at hacc15 hacc16
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := gatedPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf apc2105000GatedPinned 15 0) (hiE := payloadOf apc2105000GatedPinned 16 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc15
      hacc16
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr1, hnr1, htr1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((2 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc17 := gatedAccepts hacc 17 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc18 := gatedAccepts hacc 18 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [apc2105000GatedPinned, apc2105000Gated, BusInteraction.eval] at hacc17 hacc18
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := gatedPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
      (loE := payloadOf apc2105000GatedPinned 17 0) (hiE := payloadOf apc2105000GatedPinned 18 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc17
      hacc18
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nw1, hnw1, htw1⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((4 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc19 := gatedAccepts hacc 19 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc20 := gatedAccepts hacc 20 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [apc2105000GatedPinned, apc2105000Gated, BusInteraction.eval] at hacc19 hacc20
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := gatedPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 4)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf apc2105000GatedPinned 19 0) (hiE := payloadOf apc2105000GatedPinned 20 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc19
      hacc20
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  obtain ⟨nr3, hnr3, htr3⟩ : ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + (((9 - (n : ℤ)) : ℤ) : ZMod babyBear) := by
    have hacc21 := gatedAccepts hacc 21 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    have hacc22 := gatedAccepts hacc 22 (by decide) _ rfl rfl
      (show asg ⟨"is_valid", some 137⟩ ≠ 0 from hivne)
    simp only [apc2105000GatedPinned, apc2105000Gated, BusInteraction.eval] at hacc21 hacc22
    obtain ⟨hb, ht⟩ := lookback_of_gadget (vs := optVars) (rules := gatedPinRules)
      (baseE := optBaseE) (baseF := optBaseF) (k := 9)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
      (loE := payloadOf apc2105000GatedPinned 21 0) (hiE := payloadOf apc2105000GatedPinned 22 0)
      (gatedPinRules_hold asg halg) gatedBaseLin (by decide)
      hacc21
      hacc22
    rw [Recipe.place_eq] at ht
    exact ⟨_, hb, ht⟩
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"a__0_0", some 19⟩, 3,
          asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩), 1] } :=
    gatedAccepts hacc 7 (by decide) _ (by simp [apc2105000GatedPinned, apc2105000Gated,
      BusInteraction.eval, Expression.eval, hiv]) rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  replace hbit : isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (3 : ZMod babyBear) ∧
      (asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩)).val
        = Nat.xor (asg ⟨"a__0_0", some 19⟩).val (3 : ZMod babyBear).val := hbit
  have ha02 : isByte (asg ⟨"a__0_2", some 91⟩) :=
    isByte_of_xorThree hbit.1
      (by rw [hbit.2.2, show (3 : ZMod babyBear).val = 3 from by decide])
      (by linear_combination (2 * asg ⟨"a__0_2", some 91⟩) * babyBear_negOne)
  have hub : ∀ i : Fin apc2105000GatedPinned.busInteractions.length,
      apcRules.isStateful (apc2105000GatedPinned.busInteractions.get i).busId = true →
      ((apc2105000GatedPinned.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0 ≤ optOffsetUb.getD i.val 0 := by
    intro i hst _
    fin_cases i <;>
      simp [optOffsets, optOffsetUb, apc2105000GatedPinned, apc2105000Gated, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at hst ⊢
  have hsendIdx : ∀ i : Fin apc2105000GatedPinned.busInteractions.length,
      apcRules.isStateful (apc2105000GatedPinned.busInteractions.get i).busId = true →
      ((apc2105000GatedPinned.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [1, 6, 8, 9, 11, 12] ∧
      (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0 = optOffsetUb.getD i.val 0 := by
    intro i hst hm
    fin_cases i <;>
      simp_all [optOffsets, optOffsetUb, apc2105000GatedPinned, apc2105000Gated, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful,
        BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  -- The bridge, by static analysis: `gatedBridgeCheck` is a `decide`.
  obtain ⟨hrecv, hsend, hother⟩ := bridgeCheck_sound gatedBridgeCheck (gatedPinRules_hold asg halg)
  refine ⟨_, _, _, 11, by norm_num, hw, hrecv, hsend, hother,
    fun i => (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset.
    rintro i ⟨hst, hm⟩
    fin_cases i
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using ht0⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htw0⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htr1⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htw1⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · simp [apc2105000GatedPinned, apc2105000Gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits]; omega,
        by simp [optOffsets]; omega,
        by simpa [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt] using htr3⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt]⟩
    · exact ⟨by simp [optOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [optOffsets],
        by simp [optOffsets, optBaseE, apc2105000GatedPinned, apc2105000Gated,
          BusInteraction.eval, Expression.eval, apcRules, openVmGuestRules, openVmTimestamp,
          Circuit.msgAt, openVmMemBusId, openVmExecBusId]⟩
    all_goals
      simp [apc2105000GatedPinned, apc2105000Gated, apcRules, openVmGuestRules, openVmIsStateful,
        defaultBusMap, OpenVmBusType.isStateful] at hst
  · -- The byte invariant, by static analysis: only the masked write is left by hand. What used to
    -- be `memOrdered` (`optOffsetUb_dominates`) is inlined here, converting the caller's
    -- `place`-ordered hypothesis into the index order `byteCheck_sendsOk` expects.
    intro i hsend hlow
    have hordered : ∀ j : Fin apc2105000GatedPinned.busInteractions.length, j < i →
        apc2105000GatedPinned.activeMem apcRules asg j →
        apcRules.payloadOk (apc2105000GatedPinned.msgAt asg j) := by
      intro j hji hactj
      obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.1.2
      refine hlow j ?_ hactj
      show (optOffsets n0 nw0 nr1 nw1 nr3).getD j.val 0
        < (optOffsets n0 nw0 nr1 nw1 nr3).getD i.val 0
      rw [heq]
      exact lt_of_le_of_lt (hub j hactj.1.1 hactj.1.2)
        (optOffsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))
    refine memSendsOk_of_sendsOk (byteCheck_sendsOk (gatedPinRules_hold asg halg) gatedByteCheck ?_)
      i hsend hordered
    intro i hi hsend hlow
    fin_cases i
    all_goals try exact absurd hi (by decide)
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
      asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

theorem apc2105000GatedPinned_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 23 ≤ maxInteractions) :
    apc2105000GatedPinned.legalGuest apcRules maxWindow openVmTimestampBound maxInteractions where
  sendOnly := apc2105000GatedPinned_legalMultiplicities.1
  polarity := apc2105000GatedPinned_legalMultiplicities.2
  stepLayout := apc2105000GatedPinned_hasStepLayout hw
  size := by simpa [apc2105000GatedPinned, apc2105000Gated] using hi

--------- The unoptimized APC, timestamps chained: the bridge, closing finding G2 ---------

/-- **The strengthened check still passes**: the three chaining constraints are not pin-rule
    shaped (their right side is `from_state__timestamp_i + 3`, a variable plus a constant, not a
    literal), so `pinRuleOf` extracts nothing new from them — the check runs on exactly
    `apc2105000Unopt`'s own 27 rules. -/
theorem apc2105000UnoptChained_checkMultiplicitiesWith :
    checkMultiplicitiesWith apcRules.isStateful apc2105000UnoptChained = true := by decide

theorem apc2105000UnoptChained_legalMultiplicities :
    apc2105000UnoptChained.statelessSendOnly apcRules ∧
      apc2105000UnoptChained.statefulPolarity apcRules :=
  checkMultiplicitiesWith_sound apc2105000UnoptChained_checkMultiplicitiesWith rfl

/-- **The three chaining hypotheses, unpacked from `satisfiesAlgebraic`.** The constraints
    themselves; `pinRuleOf`'s reach ends at literals, so this is by hand. -/
theorem chainedTimes {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    asg ⟨"from_state__timestamp_1", some 37⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩ + 3 ∧
      asg ⟨"from_state__timestamp_2", some 73⟩
        = asg ⟨"from_state__timestamp_1", some 37⟩ + 3 ∧
      asg ⟨"from_state__timestamp_3", some 109⟩
        = asg ⟨"from_state__timestamp_2", some 73⟩ + 3 := by
  have h1 := halg
    (.add (.var ⟨"from_state__timestamp_1", some 37⟩)
      (.mul (.const 2013265920)
        (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3))))
    (by simp [apc2105000UnoptChained])
  have h2 := halg
    (.add (.var ⟨"from_state__timestamp_2", some 73⟩)
      (.mul (.const 2013265920)
        (.add (.var ⟨"from_state__timestamp_1", some 37⟩) (.const 3))))
    (by simp [apc2105000UnoptChained])
  have h3 := halg
    (.add (.var ⟨"from_state__timestamp_3", some 109⟩)
      (.mul (.const 2013265920)
        (.add (.var ⟨"from_state__timestamp_2", some 73⟩) (.const 3))))
    (by simp [apc2105000UnoptChained])
  simp only [Expression.eval] at h1 h2 h3
  refine ⟨by linear_combination h1 - (asg ⟨"from_state__timestamp_0", some 1⟩ + 3) * babyBear_negOne,
    by linear_combination h2 - (asg ⟨"from_state__timestamp_1", some 37⟩ + 3) * babyBear_negOne,
    by linear_combination h3 - (asg ⟨"from_state__timestamp_2", some 73⟩ + 3) * babyBear_negOne⟩

/-- The variables the unoptimized (chained) APC's bridge payloads mention. -/
def unoptVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"from_state__timestamp_1", some 37⟩,
   ⟨"from_state__timestamp_2", some 73⟩, ⟨"from_state__timestamp_3", some 109⟩,
   ⟨"cmp_result_3", some 126⟩]

/-- The pin rules `apc2105000Unopt`'s own constraints supply -- identical to
    `apc2105000UnoptChained`'s, since the three chaining constraints extract none (their right
    side is not a literal). -/
def unoptPinRules : List (PinRule babyBear) :=
  apc2105000Unopt.algebraicConstraints.filterMap pinRuleOf

theorem unoptPinRules_hold (asg : ChipAssignment babyBear)
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    ∀ q ∈ unoptPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con (List.mem_append_left _ hcon))

/-- **The bridge's linear pins**: each fused instruction's own start timestamp, in terms of
    `from_state__timestamp_0`, read off `chainedTimes` rather than a literal constraint. -/
def unoptLinRules : List (LinPinRule babyBear) :=
  [ (⟨"from_state__timestamp_1", some 37⟩, ⟨3, [1, 0, 0, 0, 0]⟩)
  , (⟨"from_state__timestamp_2", some 73⟩, ⟨6, [1, 0, 0, 0, 0]⟩)
  , (⟨"from_state__timestamp_3", some 109⟩, ⟨9, [1, 0, 0, 0, 0]⟩) ]

theorem unoptLinRules_sized : ∀ q ∈ unoptLinRules, q.2.Sized unoptVars.length := by
  intro q hq
  simp only [unoptLinRules, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> (unfold LinForm.Sized unoptVars; decide)

theorem unoptLinRules_hold {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    ∀ q ∈ unoptLinRules, asg q.1 = q.2.eval unoptVars asg := by
  obtain ⟨ht01, ht12, ht23⟩ := chainedTimes halg
  intro q hq
  simp only [unoptLinRules, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · simp only [LinForm.eval, unoptVars, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.sum_cons, List.sum_nil]
    linear_combination ht01
  · simp only [LinForm.eval, unoptVars, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.sum_cons, List.sum_nil]
    linear_combination ht12 + ht01
  · simp only [LinForm.eval, unoptVars, List.zipWith_cons_cons, List.zipWith_nil_right,
      List.sum_cons, List.sum_nil]
    linear_combination ht23 + ht12 + ht01

/-- **The bridge check, with the chain's linear pins in scope.** With `unoptLinRules` normalizing
    each fused instruction's start timestamp back to `from_state__timestamp_0`, `bridgeCheckL` sees
    the six intermediate bridge messages cancel automatically — no per-pair hand argument needed,
    unlike `apc2105000Unopt` (unchained) or the earlier hand proof this replaces. -/
theorem unoptBridgeCheckL :
    bridgeCheckL unoptVars unoptPinRules unoptLinRules 0 apc2105000UnoptChained 11 1
        (.const 2105000)
        (.var ⟨"from_state__timestamp_0", some 1⟩)
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

/-- **The bridge, closing finding G2.** `bridgeCheckL_sound` from `unoptBridgeCheckL`, a `decide`
    — the linear pins do the work `apc2105000UnoptChained_bridge`'s earlier hand proof did by
    unfolding `allEffects` and cancelling six terms in pairs. -/
theorem apc2105000UnoptChained_bridge {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    apc2105000UnoptChained.allEffects asg
        (0, [2105000, asg ⟨"from_state__timestamp_0", some 1⟩]) = -1 ∧
      apc2105000UnoptChained.allEffects asg
        (0, [2105016 + 2013265920 * (192 * asg ⟨"cmp_result_3", some 126⟩),
          asg ⟨"from_state__timestamp_0", some 1⟩ + 11]) = 1 ∧
      ∀ m : BusMessage babyBear, m.1 = 0 →
        m ≠ (0, [2105000, asg ⟨"from_state__timestamp_0", some 1⟩]) →
        m ≠ (0, [2105016 + 2013265920 * (192 * asg ⟨"cmp_result_3", some 126⟩),
          asg ⟨"from_state__timestamp_0", some 1⟩ + 11]) →
        apc2105000UnoptChained.allEffects asg m = 0 := by
  simpa using bridgeCheckL_sound unoptBridgeCheckL (unoptPinRules_hold asg halg)
    unoptLinRules_sized (unoptLinRules_hold halg)

--------- The unoptimized APC, timestamps chained: the memory placement ---------

/-- **The pins `apc2105000Unopt`'s own constraints supply, read directly rather than through
    `pinRuleOf`.** One-hot flags force `rs2_as_i = 0` on all three arithmetic slots (this basic
    block's second operand is always an immediate), the four `pc_i` and `imm_3`, and each slot's
    flag sum is `1`. -/
theorem unoptPins {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_0", some 31⟩ + asg ⟨"opcode_sub_flag_0", some 32⟩
        + asg ⟨"opcode_xor_flag_0", some 33⟩ + asg ⟨"opcode_or_flag_0", some 34⟩
        + asg ⟨"opcode_and_flag_0", some 35⟩ = 1) ∧
    (asg ⟨"opcode_add_flag_1", some 67⟩ + asg ⟨"opcode_sub_flag_1", some 68⟩
        + asg ⟨"opcode_xor_flag_1", some 69⟩ + asg ⟨"opcode_or_flag_1", some 70⟩
        + asg ⟨"opcode_and_flag_1", some 71⟩ = 1) ∧
    (asg ⟨"opcode_add_flag_2", some 103⟩ + asg ⟨"opcode_sub_flag_2", some 104⟩
        + asg ⟨"opcode_xor_flag_2", some 105⟩ + asg ⟨"opcode_or_flag_2", some 106⟩
        + asg ⟨"opcode_and_flag_2", some 107⟩ = 1) ∧
    (asg ⟨"opcode_beq_flag_3", some 128⟩ + asg ⟨"opcode_bne_flag_3", some 129⟩ = 1) ∧
    asg ⟨"from_state__pc_0", some 0⟩ = 2105000 ∧
    asg ⟨"from_state__pc_1", some 36⟩ = 2105004 ∧
    asg ⟨"from_state__pc_2", some 72⟩ = 2105008 ∧
    asg ⟨"from_state__pc_3", some 108⟩ = 2105012 ∧
    asg ⟨"rs2_as_0", some 5⟩ = 0 ∧
    asg ⟨"rs2_as_1", some 41⟩ = 0 ∧
    asg ⟨"rs2_as_2", some 77⟩ = 0 := by
  have hfs0 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
          (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
          (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))
      (.const 1)) (List.mem_append_left _ (by decide))
  have hfs1 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_1", some 67⟩))
          (.var ⟨"opcode_sub_flag_1", some 68⟩)) (.var ⟨"opcode_xor_flag_1", some 69⟩))
          (.var ⟨"opcode_or_flag_1", some 70⟩)) (.var ⟨"opcode_and_flag_1", some 71⟩)))
      (.const 1)) (List.mem_append_left _ (by decide))
  have hfs2 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_2", some 103⟩))
          (.var ⟨"opcode_sub_flag_2", some 104⟩)) (.var ⟨"opcode_xor_flag_2", some 105⟩))
          (.var ⟨"opcode_or_flag_2", some 106⟩)) (.var ⟨"opcode_and_flag_2", some 107⟩)))
      (.const 1)) (List.mem_append_left _ (by decide))
  have hfs3 := halg
    (.add (.mul (.const 2013265920)
        (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_3", some 128⟩))
          (.var ⟨"opcode_bne_flag_3", some 129⟩))) (.const 1))
    (List.mem_append_left _ (by decide))
  have hpc0 := halg
    (.add (.var ⟨"from_state__pc_0", some 0⟩) (.mul (.const 2013265920) (.const 2105000)))
    (List.mem_append_left _ (by decide))
  have hpc1 := halg
    (.add (.var ⟨"from_state__pc_1", some 36⟩) (.mul (.const 2013265920) (.const 2105004)))
    (List.mem_append_left _ (by decide))
  have hpc2 := halg
    (.add (.var ⟨"from_state__pc_2", some 72⟩) (.mul (.const 2013265920) (.const 2105008)))
    (List.mem_append_left _ (by decide))
  have hpc3 := halg
    (.add (.var ⟨"from_state__pc_3", some 108⟩) (.mul (.const 2013265920) (.const 2105012)))
    (List.mem_append_left _ (by decide))
  have hrs0 := halg
    (.add (.var ⟨"rs2_as_0", some 5⟩) (.mul (.const 2013265920) (.const 0)))
    (List.mem_append_left _ (by decide))
  have hrs1 := halg
    (.add (.var ⟨"rs2_as_1", some 41⟩) (.mul (.const 2013265920) (.const 0)))
    (List.mem_append_left _ (by decide))
  have hrs2 := halg
    (.add (.var ⟨"rs2_as_2", some 77⟩) (.mul (.const 2013265920) (.const 0)))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hfs0 hfs1 hfs2 hfs3 hpc0 hpc1 hpc2 hpc3 hrs0 hrs1 hrs2
  rw [babyBear_negOne] at hfs0 hfs1 hfs2 hfs3 hpc0 hpc1 hpc2 hpc3 hrs0 hrs1 hrs2
  refine ⟨by linear_combination -hfs0, by linear_combination -hfs1,
    by linear_combination -hfs2, by linear_combination -hfs3,
    by linear_combination hpc0, by linear_combination hpc1,
    by linear_combination hpc2, by linear_combination hpc3,
    by linear_combination hrs0, by linear_combination hrs1, by linear_combination hrs2⟩

/-- **The raw `AssertLtSubAir`, before powdr's substitution pass removes it** — reshaped into
    `lt_gadget_offset`'s `15360`-scaled form. Unlike the optimized APC (`lookback_of_gadget`), the
    unoptimized one still carries the gadget's own constraint, so this is a straight substitution
    rather than an inversion. -/
theorem rawGadget_heq {ts prev lo hi : ZMod babyBear} {k : ℤ}
    (hraw : prev = ts + ((k : ℤ) : ZMod babyBear) - lo - 131072 * hi) :
    hi = 15360 * prev + 15360 * lo - 15360 * ts - 15360 * ((k : ℤ) : ZMod babyBear) := by
  have h15 : (15360 : ZMod babyBear) * 131072 = -1 := by decide
  linear_combination (-15360 : ZMod babyBear) * hraw + hi * h15

/-- One interaction of `apc2105000UnoptChained`, unpacked from `Circuit.satisfiesStateless`. -/
theorem unoptAccepts {asg : ChipAssignment babyBear}
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg)
    (k : ℕ) (hk : k < apc2105000UnoptChained.busInteractions.length)
    (m : BusInteraction (ZMod babyBear))
    (hm : (apc2105000UnoptChained.busInteractions[k]).eval asg = m)
    (hst : apcRules.isStateful m.busId = false) (hmult : m.multiplicity ≠ 0) :
    accepts defaultBusMap m := by
  subst hm; exact hacc _ (List.getElem_mem hk) hst hmult

/-- The raw gadget constraint, gate-cancelled and reshaped into `lt_gadget_offset`'s form: `δ` is
    the read's own send offset (`0` for `rs1`, `1` for arc `3`'s `rs2`, `2` for the write), so
    `lt_gadget_offset`'s `k` is `δ - 1`, matching `apc2105000Opt`'s convention on the same reads. -/
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

set_option maxRecDepth 32000 in
/-- Instr `0`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_0 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩
          + ((((-1) - (n : ℤ)) : ℤ) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hcon := halg
    (.mul (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))
        (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩))
        (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩)
            (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩)
            (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 5 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 6 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩
set_option maxRecDepth 32000 in
/-- Instr `0`'s write: send offset `2`. -/
theorem unoptLookback_w_0 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩
        = asg ⟨"from_state__timestamp_0", some 1⟩
          + ((((1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩))) (.var ⟨"opcode_sub_flag_0", some 32⟩))) (.var ⟨"opcode_xor_flag_0", some 33⟩))) (.var ⟨"opcode_or_flag_0", some 34⟩))) (.var ⟨"opcode_and_flag_0", some 35⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2))
        (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩) (.const 1)))
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 2)
    (ts := asg ⟨"from_state__timestamp_0", some 1⟩)
    (prev := asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
    (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩)
    (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 13 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 14 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (1)
    (asg ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
    (asg ⟨"from_state__timestamp_0", some 1⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩


set_option maxRecDepth 32000 in
/-- Instr `1`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_1 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩
        = asg ⟨"from_state__timestamp_1", some 37⟩
          + ((((-1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_1", some 67⟩))) (.var ⟨"opcode_sub_flag_1", some 68⟩))) (.var ⟨"opcode_xor_flag_1", some 69⟩))) (.var ⟨"opcode_or_flag_1", some 70⟩))) (.var ⟨"opcode_and_flag_1", some 71⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_1", some 37⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_1", some 44⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_1", some 37⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_1", some 44⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 25 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 26 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
    (asg ⟨"from_state__timestamp_1", some 37⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩


set_option maxRecDepth 32000 in
/-- Instr `1`'s write: send offset `2`. -/
theorem unoptLookback_w_1 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩
        = asg ⟨"from_state__timestamp_1", some 37⟩
          + ((((1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_1", some 67⟩))) (.var ⟨"opcode_sub_flag_1", some 68⟩))) (.var ⟨"opcode_xor_flag_1", some 69⟩))) (.var ⟨"opcode_or_flag_1", some 70⟩))) (.var ⟨"opcode_and_flag_1", some 71⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_1", some 37⟩) (.const 2))
        (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩) (.const 1)))
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_1", some 50⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 2)
    (ts := asg ⟨"from_state__timestamp_1", some 37⟩)
    (prev := asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
    (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩)
    (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_1", some 50⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 33 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 34 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (1)
    (asg ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
    (asg ⟨"from_state__timestamp_1", some 37⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩


set_option maxRecDepth 32000 in
/-- Instr `2`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_2 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩
        = asg ⟨"from_state__timestamp_2", some 73⟩
          + ((((-1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_2", some 103⟩))) (.var ⟨"opcode_sub_flag_2", some 104⟩))) (.var ⟨"opcode_xor_flag_2", some 105⟩))) (.var ⟨"opcode_or_flag_2", some 106⟩))) (.var ⟨"opcode_and_flag_2", some 107⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_2", some 73⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_2", some 79⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_2", some 80⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_2", some 73⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_2", some 79⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_2", some 80⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 45 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 46 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩)
    (asg ⟨"from_state__timestamp_2", some 73⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩


set_option maxRecDepth 32000 in
/-- Instr `2`'s write: send offset `2`. -/
theorem unoptLookback_w_2 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"writes_aux__base__prev_timestamp_2", some 84⟩
        = asg ⟨"from_state__timestamp_2", some 73⟩
          + ((((1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.1
  have hcon := halg
    (.mul (.add ((.add ((.add ((.add ((.add (.const 0) (.var ⟨"opcode_add_flag_2", some 103⟩))) (.var ⟨"opcode_sub_flag_2", some 104⟩))) (.var ⟨"opcode_xor_flag_2", some 105⟩))) (.var ⟨"opcode_or_flag_2", some 106⟩))) (.var ⟨"opcode_and_flag_2", some 107⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_2", some 73⟩) (.const 2))
        (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_2", some 84⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_2", some 85⟩) (.const 1)))
          (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_2", some 86⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 2)
    (ts := asg ⟨"from_state__timestamp_2", some 73⟩)
    (prev := asg ⟨"writes_aux__base__prev_timestamp_2", some 84⟩)
    (lo := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_2", some 85⟩)
    (hi := asg ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_2", some 86⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 53 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 54 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (1)
    (asg ⟨"writes_aux__base__prev_timestamp_2", some 84⟩)
    (asg ⟨"from_state__timestamp_2", some 73⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `3`'s `rs1` read: send offset `0`. -/
theorem unoptLookback_r1_3 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩
        = asg ⟨"from_state__timestamp_3", some 109⟩
          + ((((-1 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.2.1
  have hcon := halg
    (.mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_3", some 128⟩)) (.var ⟨"opcode_bne_flag_3", some 129⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_3", some 109⟩) (.const 0))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_3", some 113⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_3", some 114⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 0)
    (ts := asg ⟨"from_state__timestamp_3", some 109⟩)
    (prev := asg ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩)
    (lo := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_3", some 113⟩)
    (hi := asg ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_3", some 114⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 60 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 61 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (-1)
    (asg ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩)
    (asg ⟨"from_state__timestamp_3", some 109⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

set_option maxRecDepth 32000 in
/-- Instr `3`'s `rs2` read: send offset `1`. -/
theorem unoptLookback_r2_3 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∃ n : ℕ, n < 2 ^ 29 ∧
      asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩
        = asg ⟨"from_state__timestamp_3", some 109⟩
          + ((((0 - (n : ℤ)) : ℤ)) : ZMod babyBear) := by
  have hgate := (unoptPins halg).2.2.2.1
  have hcon := halg
    (.mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_3", some 128⟩)) (.var ⟨"opcode_bne_flag_3", some 129⟩))
      (.add (.add (.add (.add (.var ⟨"from_state__timestamp_3", some 109⟩) (.const 1))
        (.mul (.const 2013265920) (.var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)))
        (.mul (.const 2013265920) (.const 1)))
        (.mul (.const 2013265920) (.add (.add (.const 0)
          (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩) (.const 1)))
          (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_3", some 117⟩) (.const 131072))))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hcon
  rw [babyBear_negOne] at hcon
  have heq := gadgetLookback_raw (δ := 1)
    (ts := asg ⟨"from_state__timestamp_3", some 109⟩)
    (prev := asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
    (lo := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩)
    (hi := asg ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_3", some 117⟩)
    hgate (by linear_combination hcon)
  have hlo := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 64 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  have hhi := accepts_congr_mult3 (m2 := 1)
    (unoptAccepts hacc 65 (by decide) _ rfl rfl (sum2_eq1_ne_zero hgate))
  simp only [Expression.eval] at hlo hhi
  obtain ⟨n, -, hn29, hplace⟩ := lt_gadget_offset (0)
    (asg ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
    (asg ⟨"from_state__timestamp_3", some 109⟩) hlo hhi (by push_cast at heq ⊢; linear_combination heq)
  exact ⟨n, hn29, hplace⟩

--------- The unoptimized APC, timestamps chained: the byte invariant ---------

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

/-- Instr `0`'s opcode selector is one-hot, from its booleanity constraints and `unoptPins`'s
    flag-sum pin. -/
theorem unoptAluCase0 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 1 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 1 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 1 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 1 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_0", some 31⟩ = 0 ∧ asg ⟨"opcode_sub_flag_0", some 32⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_0", some 33⟩ = 0 ∧ asg ⟨"opcode_or_flag_0", some 34⟩ = 0 ∧
        asg ⟨"opcode_and_flag_0", some 35⟩ = 1) := by
  have hb_add := halg
    (.mul (.var ⟨"opcode_add_flag_0", some 31⟩)
      (.add (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_sub := halg
    (.mul (.var ⟨"opcode_sub_flag_0", some 32⟩)
      (.add (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_xor := halg
    (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩)
      (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_or := halg
    (.mul (.var ⟨"opcode_or_flag_0", some 34⟩)
      (.add (.var ⟨"opcode_or_flag_0", some 34⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_and := halg
    (.mul (.var ⟨"opcode_and_flag_0", some 35⟩)
      (.add (.var ⟨"opcode_and_flag_0", some 35⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).1 hb_add hb_sub hb_xor hb_or hb_and

/-- Instr `1`'s opcode selector is one-hot. -/
theorem unoptAluCase1 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 1 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 1 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 1 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 1 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_1", some 67⟩ = 0 ∧ asg ⟨"opcode_sub_flag_1", some 68⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_1", some 69⟩ = 0 ∧ asg ⟨"opcode_or_flag_1", some 70⟩ = 0 ∧
        asg ⟨"opcode_and_flag_1", some 71⟩ = 1) := by
  have hb_add := halg
    (.mul (.var ⟨"opcode_add_flag_1", some 67⟩)
      (.add (.var ⟨"opcode_add_flag_1", some 67⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_sub := halg
    (.mul (.var ⟨"opcode_sub_flag_1", some 68⟩)
      (.add (.var ⟨"opcode_sub_flag_1", some 68⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_xor := halg
    (.mul (.var ⟨"opcode_xor_flag_1", some 69⟩)
      (.add (.var ⟨"opcode_xor_flag_1", some 69⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_or := halg
    (.mul (.var ⟨"opcode_or_flag_1", some 70⟩)
      (.add (.var ⟨"opcode_or_flag_1", some 70⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_and := halg
    (.mul (.var ⟨"opcode_and_flag_1", some 71⟩)
      (.add (.var ⟨"opcode_and_flag_1", some 71⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).2.1 hb_add hb_sub hb_xor hb_or hb_and

/-- Instr `2`'s opcode selector is one-hot. -/
theorem unoptAluCase2 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg) :
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 1 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 1 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 1 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 1 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 0) ∨
    (asg ⟨"opcode_add_flag_2", some 103⟩ = 0 ∧ asg ⟨"opcode_sub_flag_2", some 104⟩ = 0 ∧
        asg ⟨"opcode_xor_flag_2", some 105⟩ = 0 ∧ asg ⟨"opcode_or_flag_2", some 106⟩ = 0 ∧
        asg ⟨"opcode_and_flag_2", some 107⟩ = 1) := by
  have hb_add := halg
    (.mul (.var ⟨"opcode_add_flag_2", some 103⟩)
      (.add (.var ⟨"opcode_add_flag_2", some 103⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_sub := halg
    (.mul (.var ⟨"opcode_sub_flag_2", some 104⟩)
      (.add (.var ⟨"opcode_sub_flag_2", some 104⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_xor := halg
    (.mul (.var ⟨"opcode_xor_flag_2", some 105⟩)
      (.add (.var ⟨"opcode_xor_flag_2", some 105⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_or := halg
    (.mul (.var ⟨"opcode_or_flag_2", some 106⟩)
      (.add (.var ⟨"opcode_or_flag_2", some 106⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  have hb_and := halg
    (.mul (.var ⟨"opcode_and_flag_2", some 107⟩)
      (.add (.var ⟨"opcode_and_flag_2", some 107⟩) (.mul (.const 2013265920) (.const 1))))
    (List.mem_append_left _ (by decide))
  simp only [Expression.eval] at hb_add hb_sub hb_xor hb_or hb_and
  exact aluOneHot (unoptPins halg).2.2.1 hb_add hb_sub hb_xor hb_or hb_and

set_option maxRecDepth 32000 in
/-- **Instr `0`'s write is byte-valued**, whichever ALU op fired: each limb's own `bitwiseLookup`
    row (positions `0`–`3`) plus `unoptAluCase0`'s one-hot split feeds `isByte_of_aluLimb`. -/
theorem unoptWriteIsByte_0 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (asg ⟨"a__1_0", some 20⟩) ∧
      isByte (asg ⟨"a__2_0", some 21⟩) ∧ isByte (asg ⟨"a__3_0", some 22⟩) := by
  have hgate := (unoptPins halg).1
  have hcase := unoptAluCase0 halg
  have h0 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 0 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h1 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 1 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h2 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 2 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h3 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 3 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at h0 h1 h2 h3
  obtain ⟨hbx0, hby0, hxy0⟩ := bitwiseTable_extract h0
  obtain ⟨hbx1, hby1, hxy1⟩ := bitwiseTable_extract h1
  obtain ⟨hbx2, hby2, hxy2⟩ := bitwiseTable_extract h2
  obtain ⟨hbx3, hby3, hxy3⟩ := bitwiseTable_extract h3
  exact ⟨isByte_of_aluLimb hcase hbx0 hby0 hxy0 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx1 hby1 hxy1 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx2 hby2 hxy2 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx3 hby3 hxy3 rfl rfl rfl⟩

set_option maxRecDepth 32000 in
/-- **Instr `1`'s write is byte-valued.** -/
theorem unoptWriteIsByte_1 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_1", some 55⟩) ∧ isByte (asg ⟨"a__1_1", some 56⟩) ∧
      isByte (asg ⟨"a__2_1", some 57⟩) ∧ isByte (asg ⟨"a__3_1", some 58⟩) := by
  have hgate := (unoptPins halg).2.1
  have hcase := unoptAluCase1 halg
  have h0 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 20 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h1 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 21 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h2 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 22 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h3 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 23 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at h0 h1 h2 h3
  obtain ⟨hbx0, hby0, hxy0⟩ := bitwiseTable_extract h0
  obtain ⟨hbx1, hby1, hxy1⟩ := bitwiseTable_extract h1
  obtain ⟨hbx2, hby2, hxy2⟩ := bitwiseTable_extract h2
  obtain ⟨hbx3, hby3, hxy3⟩ := bitwiseTable_extract h3
  exact ⟨isByte_of_aluLimb hcase hbx0 hby0 hxy0 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx1 hby1 hxy1 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx2 hby2 hxy2 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx3 hby3 hxy3 rfl rfl rfl⟩

set_option maxRecDepth 32000 in
/-- **Instr `2`'s write is byte-valued.** -/
theorem unoptWriteIsByte_2 {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    isByte (asg ⟨"a__0_2", some 91⟩) ∧ isByte (asg ⟨"a__1_2", some 92⟩) ∧
      isByte (asg ⟨"a__2_2", some 93⟩) ∧ isByte (asg ⟨"a__3_2", some 94⟩) := by
  have hgate := (unoptPins halg).2.2.1
  have hcase := unoptAluCase2 halg
  have h0 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 40 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h1 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 41 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h2 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 42 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  have h3 := accepts_congr_mult6 (m2 := 1)
    (unoptAccepts hacc 43 (by decide) _ rfl rfl (sum5_eq1_ne_zero hgate))
  simp only [Expression.eval] at h0 h1 h2 h3
  obtain ⟨hbx0, hby0, hxy0⟩ := bitwiseTable_extract h0
  obtain ⟨hbx1, hby1, hxy1⟩ := bitwiseTable_extract h1
  obtain ⟨hbx2, hby2, hxy2⟩ := bitwiseTable_extract h2
  obtain ⟨hbx3, hby3, hxy3⟩ := bitwiseTable_extract h3
  exact ⟨isByte_of_aluLimb hcase hbx0 hby0 hxy0 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx1 hby1 hxy1 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx2 hby2 hxy2 rfl rfl rfl,
    isByte_of_aluLimb hcase hbx3 hby3 hxy3 rfl rfl rfl⟩

/-- The variables `apc2105000UnoptChained`'s echoed memory sends and their preceding receives
    mention: each instruction's `rs1` pointer, the four limbs it reads back, its own base
    timestamp and lookback record, and (for the branch) the same for `rs2`. -/
def unoptByteVars : List Variable :=
  [⟨"rs1_ptr_0", some 3⟩, ⟨"b__0_0", some 23⟩, ⟨"b__1_0", some 24⟩, ⟨"b__2_0", some 25⟩,
   ⟨"b__3_0", some 26⟩, ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"from_state__timestamp_0", some 1⟩,
   ⟨"rs1_ptr_1", some 39⟩, ⟨"b__0_1", some 59⟩, ⟨"b__1_1", some 60⟩, ⟨"b__2_1", some 61⟩,
   ⟨"b__3_1", some 62⟩, ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩,
   ⟨"from_state__timestamp_1", some 37⟩,
   ⟨"rs1_ptr_2", some 75⟩, ⟨"b__0_2", some 95⟩, ⟨"b__1_2", some 96⟩, ⟨"b__2_2", some 97⟩,
   ⟨"b__3_2", some 98⟩, ⟨"reads_aux__0__base__prev_timestamp_2", some 78⟩,
   ⟨"from_state__timestamp_2", some 73⟩,
   ⟨"rs1_ptr_3", some 110⟩, ⟨"a__0_3", some 118⟩, ⟨"a__1_3", some 119⟩, ⟨"a__2_3", some 120⟩,
   ⟨"a__3_3", some 121⟩, ⟨"reads_aux__0__base__prev_timestamp_3", some 112⟩,
   ⟨"from_state__timestamp_3", some 109⟩,
   ⟨"rs2_ptr_3", some 111⟩, ⟨"b__0_3", some 122⟩, ⟨"b__1_3", some 123⟩, ⟨"b__2_3", some 124⟩,
   ⟨"b__3_3", some 125⟩, ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩]

/-- One fused instruction's twenty stateful/lookup interactions: four `bitwiseLookup` rows for the
    ALU result's limbs, a range check for the immediate, the `rs1` gadget and its receive/echo, the
    (structurally inactive, since `rs2_as_i = 0`) `rs2` gadget and receive/send, the write gadget
    and its receive, the write itself (`external` — the ALU result, justified by the caller), the
    register-file lookup, and the bridge receive/send. -/
def unoptInstrWitnesses (base : ℕ) : List ByteWitness :=
  [.notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .echo (base + 7), .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .external, .notSend, .notSend, .notMemory]

/-- The branch instruction's eleven: the `rs1` and `rs2` gadgets and their receive/echo, the
    register-file lookup, and the bridge receive/send — no write, so no `external`. -/
def unoptBranchWitnesses (base : ℕ) : List ByteWitness :=
  [.notSend, .notSend, .notSend, .echo (base + 2), .notSend, .notSend, .notSend,
   .echo (base + 6), .notSend, .notSend, .notMemory]

/-- The witness for each of `apc2105000UnoptChained`'s `71` interactions: three fused-instruction
    blocks of `20` (indices `0`, `20`, `40`) and the branch's `11` (index `60`). -/
def unoptWitnesses : List ByteWitness :=
  unoptInstrWitnesses 0 ++ unoptInstrWitnesses 20 ++ unoptInstrWitnesses 40 ++
    unoptBranchWitnesses 60

theorem unoptByteCheck :
    byteCheckAll unoptByteVars unoptPinRules apc2105000UnoptChained.busInteractions unoptWitnesses
      = true := by decide

/-- **`StepLayout.memSendsOk`, by static analysis.** `byteCheckAll` accounts for every echoed
    read and every interaction that isn't a genuine memory send; the three ALU writes are left to
    the caller, closed by `unoptWriteIsByte_0/1/2`. -/
theorem apc2105000UnoptChained_memSendsOk {asg : ChipAssignment babyBear}
    (halg : apc2105000UnoptChained.satisfiesAlgebraic asg)
    (hacc : apc2105000UnoptChained.satisfiesStateless apcRules asg) :
    ∀ i : Fin apc2105000UnoptChained.busInteractions.length,
      apc2105000UnoptChained.memSend apcRules asg i →
      (∀ j : Fin apc2105000UnoptChained.busInteractions.length, j < i →
        apc2105000UnoptChained.activeMem apcRules asg j →
        apcRules.payloadOk (apc2105000UnoptChained.msgAt asg j)) →
      apcRules.payloadOk (apc2105000UnoptChained.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  refine memSendsOk_of_sendsOk (byteCheck_sendsOk (unoptPinRules_hold asg halg) unoptByteCheck ?_)
  intro i hi hsend hlow
  fin_cases i
  all_goals try exact absurd hi (by decide)
  · obtain ⟨h0, h1, h2, h3⟩ := unoptWriteIsByte_0 halg hacc
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_0", some 2⟩,
      asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
      asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨h0, h1, h2, h3⟩
  · obtain ⟨h0, h1, h2, h3⟩ := unoptWriteIsByte_1 halg hacc
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_1", some 38⟩,
      asg ⟨"a__0_1", some 55⟩, asg ⟨"a__1_1", some 56⟩, asg ⟨"a__2_1", some 57⟩,
      asg ⟨"a__3_1", some 58⟩, asg ⟨"from_state__timestamp_1", some 37⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨h0, h1, h2, h3⟩
  · obtain ⟨h0, h1, h2, h3⟩ := unoptWriteIsByte_2 halg hacc
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), asg ⟨"rd_ptr_2", some 74⟩,
      asg ⟨"a__0_2", some 91⟩, asg ⟨"a__1_2", some 92⟩, asg ⟨"a__2_2", some 93⟩,
      asg ⟨"a__3_2", some 94⟩, asg ⟨"from_state__timestamp_2", some 73⟩ + 2])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨h0, h1, h2, h3⟩

--------- The unoptimized APC, timestamps chained: the ordering ---------

/-- Where each of `apc2105000UnoptChained`'s `71` interactions sits, as an upper bound on its
    offset from `from_state__timestamp_0`: the four fused steps' local offsets (mirroring
    `apc2105000Opt`'s `optOffsetUb`, one memory gadget's receive/send pair per instruction, two
    for the branch's `rs1`/`rs2`), shifted by each instruction's own `3`-tick advance
    (`chainedTimes`). Stateless positions, and the inactive `rs2` gadgets `rs2_as_i = 0` disables,
    get a placeholder far below every real offset — the domination check below never reads
    them for anything but a `<`, and they are never `activeStateful` either way. -/
def unoptOffsetUb : List ℤ :=
  -- instr 0 (shift 0)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, -1, 0, -1000, -1000, -1000, -1000, -1000,
   -1000, 1, 2, -1000, -1000, -1000] ++
  -- instr 1 (shift 3)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 2, 3, -1000, -1000, -1000, -1000, -1000,
   -1000, 4, 5, -1000, -1000, -1000] ++
  -- instr 2 (shift 6)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 5, 6, -1000, -1000, -1000, -1000, -1000,
   -1000, 7, 8, -1000, -1000, -1000] ++
  -- instr 3 / branch (shift 9)
  [-1000, -1000, 8, 9, -1000, -1000, 9, 10, -1000, -1000, -1000]

/-- Each of `apc2105000UnoptChained`'s eight memory sends dominates every position before it —
    the ordering fact `memSendsOk` needs for this circuit, `decide` over `71` positions. Unlike
    `apc2105000Opt`, several sends share an upper bound with an *earlier, different* send's own
    predecessor (e.g. positions `36` and `47` both cap out at `5`) — harmless, since domination is
    only ever asked of a send against what precedes *it*, never between two unrelated positions. -/
theorem unoptOffsetUb_dominates :
    ∀ b ∈ [8, 16, 28, 36, 48, 56, 63, 67], ∀ k < b, unoptOffsetUb.getD k 0 < unoptOffsetUb.getD b 0 := by
  decide

/-- The exact offset each of `apc2105000UnoptChained`'s `71` interactions sits at, mirroring
    `unoptOffsetUb`'s shape but with each memory receive's real lookback (`δ - n`, from the eight
    `unoptLookback_*` lemmas) rather than its upper bound `δ`, and the bridge's own literal offsets
    filled in (the upper-bound table leaves those `-1000`, since ordering never reads them). -/
def unoptOffsets (nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23 : ℕ) : List ℤ :=
  -- instr 0 (shift 0)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, -1 - (nr10 : ℤ), 0, -1000, -1000, -1000,
   -1000, -1000, -1000, 1 - (nw0 : ℤ), 2, -1000, 0, 3] ++
  -- instr 1 (shift 3)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 2 - (nr11 : ℤ), 3, -1000, -1000, -1000,
   -1000, -1000, -1000, 4 - (nw1 : ℤ), 5, -1000, 3, 6] ++
  -- instr 2 (shift 6)
  [-1000, -1000, -1000, -1000, -1000, -1000, -1000, 5 - (nr12 : ℤ), 6, -1000, -1000, -1000,
   -1000, -1000, -1000, 7 - (nw2 : ℤ), 8, -1000, 6, 9] ++
  -- instr 3 / branch (shift 9)
  [-1000, -1000, 8 - (nr13 : ℤ), 9, -1000, -1000, 9 - (nr23 : ℤ), 10, -1000, 9, 11]

--------- The unoptimized APC, timestamps chained: assembling the layout ---------

set_option maxRecDepth 20000 in
set_option linter.unnecessarySeqFocus false in
/-- **A chained-but-unoptimized APC has a step layout.** `d = 11`, matching `apc2105000Opt`'s own
    arc: the four fused instructions' local `3`/`3`/`3`/`2`-tick advances, chained by
    `apc2105000UnoptChained_bridge`. Every one of the `71` interactions is placed by
    `unoptOffsets`, the eight memory sends dominate what precedes them (`unoptOffsetUb_dominates`),
    and `apc2105000UnoptChained_memSendsOk` closes the byte invariant.

    This is what `memSendsOk`'s restriction to the memory bus buys over the old cross-bus
    `ordered`: the bridge-round-trip-vs-echo timestamp collision that made this circuit fail the
    old `ordered` (two unrelated instructions' own bookkeeping landing on the same field
    timestamp) never enters a memory-vs-memory comparison, so it is not a counterexample here. -/
theorem apc2105000UnoptChained_hasStepLayout {maxWindow : ℕ} (hw : 11 < maxWindow) :
    apc2105000UnoptChained.hasStepLayout apcRules maxWindow openVmTimestampBound := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  intro asg halg hacc
  obtain ⟨nr10, hnr10, htr10⟩ := unoptLookback_r1_0 halg hacc
  obtain ⟨nw0, hnw0, htw0⟩ := unoptLookback_w_0 halg hacc
  obtain ⟨nr11, hnr11, htr11⟩ := unoptLookback_r1_1 halg hacc
  obtain ⟨nw1, hnw1, htw1⟩ := unoptLookback_w_1 halg hacc
  obtain ⟨nr12, hnr12, htr12⟩ := unoptLookback_r1_2 halg hacc
  obtain ⟨nw2, hnw2, htw2⟩ := unoptLookback_w_2 halg hacc
  obtain ⟨nr13, hnr13, htr13⟩ := unoptLookback_r1_3 halg hacc
  obtain ⟨nr23, hnr23, htr23⟩ := unoptLookback_r2_3 halg hacc
  obtain ⟨hs0, hs1, hs2, hs3, -, -, -, -, hrs0, hrs1, hrs2⟩ := unoptPins halg
  obtain ⟨ht01, ht12, ht23⟩ := chainedTimes halg
  obtain ⟨hrecv, hsend, hother⟩ := apc2105000UnoptChained_bridge halg
  have hub : ∀ i : Fin apc2105000UnoptChained.busInteractions.length,
      apcRules.isStateful (apc2105000UnoptChained.busInteractions.get i).busId = true →
      (apc2105000UnoptChained.busInteractions.get i).busId = apcRules.memBusId →
      ((apc2105000UnoptChained.busInteractions.get i).eval asg).multiplicity ≠ 0 →
      (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0
        ≤ unoptOffsetUb.getD i.val 0 := by
    intro i hst hbmem _
    fin_cases i <;>
      simp [unoptOffsets, unoptOffsetUb, apc2105000UnoptChained, apc2105000Unopt, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, openVmMemBusId,
        OpenVmBusType.isStateful] at hst hbmem ⊢
  have hsendIdx : ∀ i : Fin apc2105000UnoptChained.busInteractions.length,
      apcRules.isStateful (apc2105000UnoptChained.busInteractions.get i).busId = true →
      (apc2105000UnoptChained.busInteractions.get i).busId = apcRules.memBusId →
      ((apc2105000UnoptChained.busInteractions.get i).eval asg).multiplicity = 1 →
      i.val ∈ [8, 16, 28, 36, 48, 56, 63, 67] ∧
      (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0
        = unoptOffsetUb.getD i.val 0 := by
    intro i hst hbmem hm
    fin_cases i <;>
      simp_all [unoptOffsets, unoptOffsetUb, apc2105000UnoptChained, apc2105000Unopt, apcRules,
        openVmGuestRules, openVmIsStateful, defaultBusMap, openVmMemBusId,
        OpenVmBusType.isStateful, BusInteraction.eval, Expression.eval, babyBear_negOne_ne_one]
  refine ⟨_, _, _, 11, by norm_num, hw, hrecv, hsend, hother,
    fun i => (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0, ?_, ?_⟩
  · -- The placement, offset by offset: `30` genuinely stateful positions (memory or bridge),
    -- read off directly; every other position is either stateless or a structurally inactive
    -- `rs2` gadget (`rs2_as_i = 0`, so its multiplicity can never be nonzero).
    rintro i ⟨hst, hm⟩
    fin_cases i <;>
      simp [apc2105000UnoptChained, apc2105000Unopt, apcRules, openVmGuestRules,
        openVmIsStateful, defaultBusMap, OpenVmBusType.isStateful] at hst
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by simpa [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htr10⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact absurd (by simp [apc2105000UnoptChained, apc2105000Unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs0]) hm
    · exact absurd (by simp [apc2105000UnoptChained, apc2105000Unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs0]) hm
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by simpa [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt] using htw0⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr11
           simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01]⟩
    · exact absurd (by simp [apc2105000UnoptChained, apc2105000Unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs1]) hm
    · exact absurd (by simp [apc2105000UnoptChained, apc2105000Unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs1]) hm
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htw1
           simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01]⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr12
           simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12] <;> ring⟩
    · exact absurd (by simp [apc2105000UnoptChained, apc2105000Unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs2]) hm
    · exact absurd (by simp [apc2105000UnoptChained, apc2105000Unopt, Circuit.multAt, BusInteraction.eval,
        Expression.eval, hrs2]) hm
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htw2
           simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr13
           simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12, ht23] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12, ht23] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits]<;> omega,
        by simp [unoptOffsets]<;> omega,
        by have h := htr23
           simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
             Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
             ht01, ht12, ht23] at h ⊢
           linear_combination h⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt, ht01, ht12, ht23] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12, ht23] <;> ring⟩
    · exact ⟨by simp [unoptOffsets, openVmTimestampBound, openVmTimestampBits],
        by simp [unoptOffsets],
        by simp [unoptOffsets, apc2105000UnoptChained, apc2105000Unopt, BusInteraction.eval,
          Expression.eval, apcRules, openVmGuestRules, openVmTimestamp, Circuit.msgAt,
          openVmMemBusId, openVmExecBusId, ht01, ht12, ht23] <;> ring⟩
  · -- The byte invariant: `apc2105000UnoptChained_memSendsOk`, by static analysis. What used to be
    -- `memOrdered` (`unoptOffsetUb_dominates`) is inlined here, converting the caller's
    -- `place`-ordered hypothesis into the index order that theorem expects.
    intro i hsend hlow
    refine apc2105000UnoptChained_memSendsOk halg hacc i hsend (fun j hji hactj => ?_)
    obtain ⟨hmem, heq⟩ := hsendIdx i hsend.1.1 hsend.2 hsend.1.2
    refine hlow j ?_ hactj
    show (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD j.val 0
      < (unoptOffsets nr10 nw0 nr11 nw1 nr12 nw2 nr13 nr23).getD i.val 0
    rw [heq]
    exact lt_of_le_of_lt (hub j hactj.1.1 hactj.2 hactj.1.2)
      (unoptOffsetUb_dominates i.val hmem j.val (Fin.lt_def.mp hji))

theorem apc2105000UnoptChained_legalGuest {maxWindow maxInteractions : ℕ} (hw : 11 < maxWindow)
    (hi : 71 ≤ maxInteractions) :
    apc2105000UnoptChained.legalGuest apcRules maxWindow openVmTimestampBound
      maxInteractions where
  sendOnly := apc2105000UnoptChained_legalMultiplicities.1
  polarity := apc2105000UnoptChained_legalMultiplicities.2
  stepLayout := apc2105000UnoptChained_hasStepLayout hw
  size := by simpa [apc2105000UnoptChained, apc2105000Unopt] using hi
