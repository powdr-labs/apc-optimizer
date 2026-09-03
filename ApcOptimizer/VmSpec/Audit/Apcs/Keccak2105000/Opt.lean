import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Stage `039_trivial_simp`: `Circuit.legalGuest` in full.** Every multiplicity is a field
    literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the five surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- **The static check passes on a real optimized APC.** Every multiplicity stage `039` carries is
    a field literal, so `Expression.foldConst` — `Audit/SendOnlyPolarity.lean`'s first and only
    tier — resolves all 23 of them, and `decide` closes the check in the kernel. No case analysis
    over the circuit is written by hand. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

/-- **Both multiplicity clauses of `Circuit.legalGuest`, for a real optimized APC**, discharged by
    `checkMultiplicities_sound` from the `Bool` above rather than by a proof about this particular
    circuit. -/
theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment — so unlike `gated_not_hasStepLayout`'s row, no
    assignment makes this circuit silent. -/
theorem opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- The pin rules the optimized APC's own constraints supply. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
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
theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 11 1
        (.const 2105000)
        baseE
        (.add (.const 2105016) (.mul (.const 2013265920)
          (.mul (.const 192) (.var ⟨"cmp_result_3", some 126⟩))))
      = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- Where each interaction sits, as a `Recipe`: the five surviving lt gadgets place their memory
    receives, everything else sits at a literal tick. Position `7` and `13`–`22` are the stateless
    lookups, which no clause reads. -/
def recipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf opt 13 0) (payloadOf opt 14 0), .fixed 0,
   .lookback 1 131072 (payloadOf opt 15 0) (payloadOf opt 16 0), .fixed 0,
   .lookback 2 131072 (payloadOf opt 17 0) (payloadOf opt 18 0),
   .lookback 4 131072 (payloadOf opt 19 0) (payloadOf opt 20 0),
   .fixed 5, .fixed 0, .fixed 6, .fixed 9,
   .lookback 9 131072 (payloadOf opt 21 0) (payloadOf opt 22 0),
   .fixed 10, .fixed 11] ++ List.replicate 10 (.fixed 0)

theorem optPlaceCheck :
    placeCheckAll layoutVars optPinRules apcRules.isStateful openVmTsPos baseF
      opt.busInteractions recipes = true := by decide

theorem optOrderCheck :
    memOrderCheck optPinRules openVmMemBusId openVmTimestampBound opt.busInteractions recipes
      = true := by decide

theorem optFitsCheck :
    (List.range opt.busInteractions.length).all
      (fun i => (recipes.getD i (.fixed 0)).fits openVmTimestampBound 11) = true := by decide

/-- Where each of the five memory receives reaches back to, off its own lt gadget. -/
theorem optLookbacks {asg : ChipAssignment babyBear}
    (halg : opt.satisfiesAlgebraic asg) (hacc : opt.satisfiesStateless apcRules asg)
    (i : Fin opt.busInteractions.length) (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear)
    (hrc : recipes.getD i.val (.fixed 0) = .lookback k radix loE hiE) :
    (recipes.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
      apcRules.getTimestamp (opt.msgAt asg i)
        = baseE.eval asg + (((recipes.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear) := by
  fin_cases i
  case «0» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf opt 13 0) (hiE := payloadOf opt 14 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «2» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf opt 15 0) (hiE := payloadOf opt 16 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 16 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «4» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩)
      (loE := payloadOf opt 17 0) (hiE := payloadOf opt 18 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 18 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «5» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 4)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf opt 19 0) (hiE := payloadOf opt 20 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 19 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 20 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «10» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 9)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩)
      (loE := payloadOf opt 21 0) (hiE := payloadOf opt 22 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 21 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 22 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  all_goals simp [recipes] at hrc

/-- The masked write at position `9`, the one send a decidable check cannot vouch for: OpenVM
    computes `a AND 3` by looking it up rather than by constraint (`isByte_of_xorThree`). -/
theorem optWriteOk {asg : ChipAssignment babyBear}
    (hacc : opt.satisfiesStateless apcRules asg) (i : Fin opt.busInteractions.length)
    (hwit : witnesses.getD i.val .notSend = .external) :
    apcRules.payloadOk (opt.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"a__0_0", some 19⟩, 3,
          asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩), 1] } :=
    acceptsAt hacc 7 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  replace hbit : isByte (asg ⟨"a__0_0", some 19⟩) ∧ isByte (3 : ZMod babyBear) ∧
      (asg ⟨"a__0_0", some 19⟩ + 3 + 2013265920 * (2 * asg ⟨"a__0_2", some 91⟩)).val
        = Nat.xor (asg ⟨"a__0_0", some 19⟩).val (3 : ZMod babyBear).val := hbit
  have ha02 : isByte (asg ⟨"a__0_2", some 91⟩) :=
    isByte_of_xorThree hbit.1
      (by rw [hbit.2.2, show (3 : ZMod babyBear).val = 3 from by decide])
      (by linear_combination (2 * asg ⟨"a__0_2", some 91⟩) * babyBear_negOne)
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
    asg ⟨"a__0_2", some 91⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 9])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha02, isByte_zero, isByte_zero, isByte_zero⟩

end ApcOptimizer.OpenVM.Keccak2105000
