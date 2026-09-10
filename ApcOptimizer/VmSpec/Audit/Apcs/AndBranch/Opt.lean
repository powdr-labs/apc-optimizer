import ApcOptimizer.VmSpec.Audit.Apcs.AndBranch.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **`Circuit.legalGuest` in full, for the optimized `andi`/`bnez` block.** Every multiplicity is
    a field literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the three surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.AndBranch

/-- **The static check passes.** Every multiplicity this stage carries is a field literal, so
    `Expression.foldConst` resolves all 15 of them and `decide` closes the check in the kernel. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- **The optimized APC has no padding row**: its multiplicities are literals, and one of them is
    nonzero under every assignment. -/
theorem opt_no_padding_row (asg : ChipAssignment babyBear) :
    ¬ ∀ bi ∈ opt.busInteractions, (bi.eval asg).multiplicity = 0 := by
  intro h
  have hne := h (opt.busInteractions.get ⟨0, by decide⟩) (List.get_mem _ _)
  simp only [opt, BusInteraction.eval, Expression.eval, List.get] at hne
  exact absurd hne (by decide)

/-- The pin rules this stage's own constraints supply: none, all three are products. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

/-- **The bridge half of the layout, by static analysis.** The block spans `d = 5` ticks; the
    outgoing `pc` is `2100188 + 12 * cmp_result_1`, so the two endpoints are separated at the
    timestamp position rather than the `pc` one. -/
theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 5 1 (.const 2100180) baseE (payloadOf opt 8 0)
      = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- Where each interaction sits, as a `Recipe`: the three memory receives reach back by their own
    lt gadget's `n`, everything else sits at a literal tick of the step. Positions `9`–`14` are
    the range lookups and `0` the bitwise one, which no clause reads. -/
def recipes : List (Recipe babyBear) :=
  [.fixed 0,
   .lookback (-1) 131072 (payloadOf opt 9 0) (payloadOf opt 10 0), .fixed 0,
   .lookback 1 131072 (payloadOf opt 11 0) (payloadOf opt 12 0),
   .fixed 0, .fixed 3,
   .lookback 3 131072 (payloadOf opt 13 0) (payloadOf opt 14 0), .fixed 4,
   .fixed 5,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

theorem optPlaceCheck :
    placeCheckAll layoutVars optPinRules apcRules.isStateful openVmTsPos baseF
      opt.busInteractions recipes = true := by decide

theorem optOrderCheck :
    memOrderCheck optPinRules openVmMemBusId openVmTimestampBound opt.busInteractions recipes
      = true := by decide

theorem optFitsCheck :
    (List.range opt.busInteractions.length).all
      (fun i => (recipes.getD i (.fixed 0)).fits openVmTimestampBound 5) = true := by decide

/-- Where each memory receive reaches back to, off the lt gadget (`lookback_of_gadget`). -/
theorem optLookbacks {asg : ChipAssignment babyBear}
    (halg : opt.satisfiesAlgebraic asg) (hacc : opt.satisfiesStateless apcRules asg)
    (i : Fin opt.busInteractions.length) (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear)
    (hrc : recipes.getD i.val (.fixed 0) = .lookback k radix loE hiE) :
    (recipes.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
      apcRules.getTimestamp (opt.msgAt asg i)
        = baseE.eval asg + (((recipes.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear) := by
  fin_cases i
  case «1» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)
      (loE := payloadOf opt 9 0) (hiE := payloadOf opt 10 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 9 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 10 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «3» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)
      (loE := payloadOf opt 11 0) (hiE := payloadOf opt 12 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 11 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 12 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «6» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 3)
      (tsE := .var ⟨"reads_aux__1__base__prev_timestamp_1", some 43⟩)
      (loE := payloadOf opt 13 0) (hiE := payloadOf opt 14 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  all_goals simp [recipes] at hrc

/-- The other thing a decidable check cannot see: the write at position `5` sends
    `b__0_0 AND 2`, which OpenVM masks by *lookup* rather than by constraint — the bitwise table's
    `op = 1` row `z = b XOR 2` together with `z = b + 2 - 2 * a` pins `a` to the mask, hence a
    byte (`isByte_of_andEq`). -/
theorem optWriteOk {asg : ChipAssignment babyBear}
    (hacc : opt.satisfiesStateless apcRules asg) (i : Fin opt.busInteractions.length)
    (hwit : witnesses.getD i.val .notSend = .external) :
    apcRules.payloadOk (opt.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  have hbit : accepts (p := babyBear) defaultBusMap
      { busId := 6, multiplicity := 1,
        payload := [asg ⟨"b__0_0", some 23⟩, 2,
          asg ⟨"b__0_0", some 23⟩ + 2 + 2013265920 * (2 * asg ⟨"a__0_0", some 19⟩), 1] } :=
    acceptsAt hacc 0 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide)
  have ha0 : isByte (asg ⟨"a__0_0", some 19⟩) :=
    isByte_of_andEq (bitwiseTable_extract hbit).1 (bitwiseTable_extract hbit).2.1
      (bitwiseTable_extract hbit).2.2 (by rw [babyBear_negOne]; ring)
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 44,
    asg ⟨"a__0_0", some 19⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 3])
  exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr ⟨ha0, isByte_zero, isByte_zero, isByte_zero⟩

end ApcOptimizer.OpenVM.AndBranch
