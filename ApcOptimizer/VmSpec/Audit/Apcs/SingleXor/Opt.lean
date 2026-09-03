import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **The last `trivial_simp` stage: `Circuit.legalGuest` in full.** Every multiplicity is a field
    literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the three surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.SingleXor

/-- **The static check passes.** Every multiplicity this stage carries is a field literal, so
    `Expression.foldConst` resolves all 18 of them and `decide` closes the check in the kernel. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment — so unlike `gated_not_hasStepLayout`'s row, no assignment makes
    this circuit silent. -/
theorem opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- The pin rules this stage's own constraints supply: none, it has no constraints left. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

/-- **The bridge half of the layout, by static analysis**: `bridgeCheck` normalizes the two bus-`0`
    payloads, sees the receive first and the send last with nothing between them, reads `d = 3` off
    the timestamps, and separates the two endpoints at payload position `1`. -/
theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 3 1 (.const 0) baseE (.const 4) = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- Where each interaction sits, as a `Recipe`: the three memory receives reach back by their own
    lt gadget's `n`, everything else sits at a literal tick. Positions `0`–`3` and `12`–`17` are
    the bitwise and range lookups, which no clause reads. -/
def recipes : List (Recipe babyBear) :=
  [.fixed 0, .fixed 0, .fixed 0, .fixed 0,
   .lookback (-1) 131072 (payloadOf opt 12 0) (payloadOf opt 13 0), .fixed 0,
   .lookback 0 131072 (payloadOf opt 14 0) (payloadOf opt 15 0), .fixed 1,
   .lookback 1 131072 (payloadOf opt 16 0) (payloadOf opt 17 0), .fixed 2,
   .fixed 0, .fixed 3,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

theorem optPlaceCheck :
    placeCheckAll layoutVars optPinRules apcRules.isStateful openVmTsPos baseF
      opt.busInteractions recipes = true := by decide

theorem optOrderCheck :
    memOrderCheck optPinRules openVmMemBusId openVmTimestampBound opt.busInteractions recipes
      = true := by decide

theorem optFitsCheck :
    (List.range opt.busInteractions.length).all
      (fun i => (recipes.getD i (.fixed 0)).fits openVmTimestampBound 3) = true := by decide

/-- Where each memory receive reaches back to, off the lt gadget (`lookback_of_gadget`). -/
theorem optLookbacks {asg : ChipAssignment babyBear}
    (halg : opt.satisfiesAlgebraic asg) (hacc : opt.satisfiesStateless apcRules asg)
    (i : Fin opt.busInteractions.length) (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear)
    (hrc : recipes.getD i.val (.fixed 0) = .lookback k radix loE hiE) :
    (recipes.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
      apcRules.getTimestamp (opt.msgAt asg i)
        = baseE.eval asg + (((recipes.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear) := by
  fin_cases i
  case «4» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf opt 12 0) (hiE := payloadOf opt 13 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 12 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «6» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)
      (loE := payloadOf opt 14 0) (hiE := payloadOf opt 15 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «8» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf opt 16 0) (hiE := payloadOf opt 17 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 16 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  all_goals simp [recipes] at hrc

/-- The other thing a decidable check cannot see: the write at position `9` sends the `xor` the
    bitwise table computes, so its four limbs are bytes (`isByte_of_xorEq`). -/
theorem optWriteOk {asg : ChipAssignment babyBear}
    (hacc : opt.satisfiesStateless apcRules asg) (i : Fin opt.busInteractions.length)
    (hwit : witnesses.getD i.val .notSend = .external) :
    apcRules.payloadOk (opt.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  have hbit0 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__0_0", some 23⟩, asg ⟨"c__0_0", some 27⟩,
          asg ⟨"a__0_0", some 19⟩, 1] } :=
    acceptsAt hacc 0 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha0 : isByte (asg ⟨"a__0_0", some 19⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit0).1 (bitwiseTable_extract hbit0).2.1
      (bitwiseTable_extract hbit0).2.2 rfl
  have hbit1 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__1_0", some 24⟩, asg ⟨"c__1_0", some 28⟩,
          asg ⟨"a__1_0", some 20⟩, 1] } :=
    acceptsAt hacc 1 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha1 : isByte (asg ⟨"a__1_0", some 20⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit1).1 (bitwiseTable_extract hbit1).2.1
      (bitwiseTable_extract hbit1).2.2 rfl
  have hbit2 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__2_0", some 25⟩, asg ⟨"c__2_0", some 29⟩,
          asg ⟨"a__2_0", some 21⟩, 1] } :=
    acceptsAt hacc 2 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha2 : isByte (asg ⟨"a__2_0", some 21⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit2).1 (bitwiseTable_extract hbit2).2.1
      (bitwiseTable_extract hbit2).2.2 rfl
  have hbit3 : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__3_0", some 26⟩, asg ⟨"c__3_0", some 30⟩,
          asg ⟨"a__3_0", some 22⟩, 1] } :=
    acceptsAt hacc 3 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha3 : isByte (asg ⟨"a__3_0", some 22⟩) :=
    isByte_of_xorEq (bitwiseTable_extract hbit3).1 (bitwiseTable_extract hbit3).2.1
      (bitwiseTable_extract hbit3).2.2 rfl
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 8,
    asg ⟨"a__0_0", some 19⟩, asg ⟨"a__1_0", some 20⟩, asg ⟨"a__2_0", some 21⟩,
    asg ⟨"a__3_0", some 22⟩, asg ⟨"from_state__timestamp_0", some 1⟩ + 2])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha0, ha1, ha2, ha3⟩

end ApcOptimizer.OpenVM.SingleXor
