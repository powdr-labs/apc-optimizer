import ApcOptimizer.VmSpec.Audit.Apcs.LoadBranch.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **`Circuit.legalGuest` in full, for the optimized `loadw`/`beq` block.** Every multiplicity is
    a field literal, so the constant-folding tier of `Audit/SendOnlyPolarity.lean` settles both
    multiplicity clauses, and the layout is read off the four surviving lt gadgets. -/

namespace ApcOptimizer.OpenVM.LoadBranch

/-- **The static check passes.** Every multiplicity this stage carries is a field literal, so
    `Expression.foldConst` resolves all 20 of them and `decide` closes the check in the kernel. -/
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

/-- The pin rules this stage's own constraints supply: none, all eight are products. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

/-- **The bridge half of the layout, by static analysis.** The block spans `d = 5` ticks; the
    outgoing `pc` is `3739676 - 56 * cmp_result_1`, so the two endpoints are separated at the
    timestamp position rather than the `pc` one. -/
theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 5 1 (.const 3739668) baseE (payloadOf opt 9 0)
      = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- Where each interaction sits, as a `Recipe`: the four memory receives reach back by their own
    lt gadget's `n`, everything else sits at a literal tick of the step. Positions `10`–`19` are
    the range lookups, which no clause reads — two of them (`12`, `19`) range-check the load's
    pointer limbs rather than a gadget. -/
def recipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf opt 10 0) (payloadOf opt 11 0), .fixed 0,
   .lookback 0 131072 (payloadOf opt 13 0) (payloadOf opt 14 0), .fixed 1,
   .lookback 1 131072 (payloadOf opt 15 0) (payloadOf opt 16 0), .fixed 0,
   .lookback 2 131072 (payloadOf opt 17 0) (payloadOf opt 18 0), .fixed 3,
   .fixed 4, .fixed 5,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

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
  case «0» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := (-1))
      (tsE := .var ⟨"rs1_aux_cols__base__prev_timestamp_0", some 7⟩)
      (loE := payloadOf opt 10 0) (hiE := payloadOf opt 11 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 10 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 11 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «2» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"read_data_aux__base__prev_timestamp_0", some 11⟩)
      (loE := payloadOf opt 13 0) (hiE := payloadOf opt 14 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 13 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «4» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"write_base_aux__prev_timestamp_0", some 19⟩)
      (loE := payloadOf opt 15 0) (hiE := payloadOf opt 16 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 16 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «6» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 2)
      (tsE := .var ⟨"reads_aux__0__base__prev_timestamp_1", some 45⟩)
      (loE := payloadOf opt 17 0) (hiE := payloadOf opt 18 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 18 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  all_goals simp [recipes] at hrc

end ApcOptimizer.OpenVM.LoadBranch
