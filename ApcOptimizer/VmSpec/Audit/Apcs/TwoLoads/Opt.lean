import ApcOptimizer.VmSpec.Audit.Apcs.TwoLoads.Layout

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **`Circuit.legalGuest` in full, for the optimized two-`loadb` block.**

    Every multiplicity is a field literal, so the constant-folding tier of
    `Audit/SendOnlyPolarity.lean` settles both multiplicity clauses, and the layout is read off the
    six surviving lt gadgets. What this APC adds over `LoadBranch` is a **byte** load: its
    main-memory pointer is quadratic in its own `flags__*` selector, so the placement and byte
    checks reach it only because they normalize the fields they read rather than the whole payload
    (`memShapeLin`, `Audit/ByteCheck.lean`). The written limb is then one of the four the load
    brought back — `isByte_of_loadSelect`. -/

namespace ApcOptimizer.OpenVM.TwoLoads

/-- **The static multiplicity check passes.** Every multiplicity this stage carries is a field
    literal, so `Expression.foldConst` resolves all 30 of them. -/
theorem opt_checkMultiplicities :
    checkMultiplicities apcRules.isStateful opt = true := by decide

theorem opt_legalMultiplicities :
    opt.statelessSendOnly apcRules ∧ opt.statefulPolarity apcRules :=
  checkMultiplicities_sound opt_checkMultiplicities rfl

/-- The pin rules this stage's own constraints supply. -/
def optPinRules : List (PinRule babyBear) :=
  opt.algebraicConstraints.filterMap pinRuleOf

theorem optPinRules_hold (asg : ChipAssignment babyBear)
    (halg : opt.satisfiesAlgebraic asg) : ∀ q ∈ optPinRules, q.1.eval asg = q.2 := by
  intro q hq
  obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
  exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)

theorem optBaseLin : Expression.toLin layoutVars optPinRules baseE = some baseF := by decide

/-- **The bridge half of the layout, by static analysis.** The block spans `d = 8` ticks; the
    outgoing `pc` is `5164116 + 24 * cmp_result_2`. -/
theorem optBridgeCheck :
    bridgeCheck layoutVars optPinRules 0 opt 8 1 (.const 5164104) baseE (payloadOf opt 13 0)
      = true := by decide

theorem optByteCheck :
    byteCheckAll layoutVars optPinRules opt.busInteractions witnesses = true := by decide

/-- Where each interaction sits, as a `Recipe`: the six memory receives reach back by their own lt
    gadget's `n`, every send at a literal tick of the step. Positions `14`-`29` are the range
    lookups, which no clause reads -- `16`/`23` range-check a load's flags and `28`/`29` its
    pointer limbs rather than a gadget. -/
def recipes : List (Recipe babyBear) :=
  [.lookback (-1) 131072 (payloadOf opt 14 0) (payloadOf opt 15 0), .fixed 0,
   .lookback 0 131072 (payloadOf opt 17 0) (payloadOf opt 18 0), .fixed 1,
   .lookback 1 131072 (payloadOf opt 19 0) (payloadOf opt 20 0), .fixed 0,
   .lookback 2 131072 (payloadOf opt 21 0) (payloadOf opt 22 0), .fixed 3,
   .lookback 3 131072 (payloadOf opt 24 0) (payloadOf opt 25 0), .fixed 4,
   .lookback 4 131072 (payloadOf opt 26 0) (payloadOf opt 27 0), .fixed 6,
   .fixed 7, .fixed 8,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0,
   .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0, .fixed 0]

theorem optPlaceCheck :
    placeCheckAll layoutVars optPinRules apcRules.isStateful openVmTsPos baseF
      opt.busInteractions recipes = true := by decide

theorem optOrderCheck :
    memOrderCheck optPinRules openVmMemBusId openVmTimestampBound opt.busInteractions recipes
      = true := by decide

theorem optFitsCheck :
    (List.range opt.busInteractions.length).all
      (fun i => (recipes.getD i (.fixed 0)).fits openVmTimestampBound 8) = true := by decide

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
      (loE := payloadOf opt 14 0) (hiE := payloadOf opt 15 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 14 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 15 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «2» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 0)
      (tsE := .var ⟨"read_data_aux__base__prev_timestamp_0", some 11⟩)
      (loE := payloadOf opt 17 0) (hiE := payloadOf opt 18 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 17 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 18 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «4» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 1)
      (tsE := .var ⟨"write_base_aux__prev_timestamp_0", some 19⟩)
      (loE := payloadOf opt 19 0) (hiE := payloadOf opt 20 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 19 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 20 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «6» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 2)
      (tsE := .var ⟨"rs1_aux_cols__base__prev_timestamp_1", some 48⟩)
      (loE := payloadOf opt 21 0) (hiE := payloadOf opt 22 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 21 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 22 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «8» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 3)
      (tsE := .var ⟨"read_data_aux__base__prev_timestamp_1", some 52⟩)
      (loE := payloadOf opt 24 0) (hiE := payloadOf opt 25 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 24 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 25 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  case «10» =>
    exact lookback_of_gadget (vs := layoutVars) (rules := optPinRules)
      (baseE := baseE) (baseF := baseF) (k := 4)
      (tsE := .var ⟨"write_base_aux__prev_timestamp_1", some 60⟩)
      (loE := payloadOf opt 26 0) (hiE := payloadOf opt 27 0)
      (optPinRules_hold asg halg) optBaseLin (by decide)
      (acceptsAt hacc 26 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
      (acceptsAt hacc 27 (by decide) _ rfl rfl (show (1 : ZMod babyBear) ≠ 0 by decide))
  all_goals simp [recipes] at hrc

/-- **A trit-constrained field element is `0`, `1` or `2`.** OpenVM's LoadStore selector flags are
    trits, not bits: `f(f-1)(f-2) = 0`. The bit analogue is `zmod_boolElim` (`Apcs/Common.lean`). -/
theorem zmod_tritElim {x : ZMod babyBear}
    (hx : x * ((x + 2013265920 * 1) * (x + 2013265920 * 2)) = 0) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  haveI : Fact (Nat.Prime babyBear) := ⟨by norm_num [babyBear]⟩
  rw [babyBear_negOne] at hx
  rcases mul_eq_zero.mp (show x * ((x - 1) * (x - 2)) = 0 by linear_combination hx) with h | h
  · exact Or.inl h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))

/-- **The byte a `loadb` writes is one of the four limbs it read, so it is a byte.**

    The written limb is a flag-weighted selection over the loaded word (`hw`, the block's own
    selector constraint). The four flags are trits, and the block's shape constraint (`hsel`) cuts
    the `81` combinations to exactly `4` -- one per byte position -- each of which makes the
    selection one-hot: `w` is `rd0`, `rd1`, `rd2` or `rd3`, and `prev0` never contributes. Every
    source is a limb of the main-memory receive `sendsOk`'s own hypothesis vouches for.

    Both constraints are stated in powdr's own encoding, `a - b` as `a + (p-1) * b`, so that they
    match the emitted circuit syntactically. -/
theorem isByte_of_loadSelect {f0 f1 f2 f3 rd0 rd1 rd2 rd3 prev0 w : ZMod babyBear}
    (t0 : f0 * ((f0 + 2013265920 * 1) * (f0 + 2013265920 * 2)) = 0)
    (t1 : f1 * ((f1 + 2013265920 * 1) * (f1 + 2013265920 * 2)) = 0)
    (t2 : f2 * ((f2 + 2013265920 * 1) * (f2 + 2013265920 * 2)) = 0)
    (t3 : f3 * ((f3 + 2013265920 * 1) * (f3 + 2013265920 * 2)) = 0)
    (hsel : (((((((((f1 * (f1 + (2013265920 * 1))) + (f2 * (f2 + (2013265920 * 1)))) + ((4 * f0) * f1)) + ((4 * f0) * f2)) + ((5 * f0) * f3)) + ((5 * f1) * f2)) + ((5 * f1) * f3)) + ((5 * f2) * f3)) + (2013265920 * (((((((1006632960 * f3) * (f3 + (2013265920 * 1))) + (f0 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2)))) + (f1 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2)))) + (f2 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2)))) + ((3 * f3) * ((((f0 + f1) + f2) + f3) + (2013265920 * 2)))) + 1))) = 0)
    (hw : (((((((((((1006632960 * f0) * (f0 + (2013265920 * 1))) + ((1006632960 * f1) * (f1 + (2013265920 * 1)))) + ((1006632960 * f3) * (f3 + (2013265920 * 1)))) * rd0) + ((f0 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2))) * rd1)) + ((((1006632960 * f2) * (f2 + (2013265920 * 1))) + (f1 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2)))) * rd2)) + ((f2 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2))) * rd3)) + (((f3 * ((((f0 + f1) + f2) + f3) + (2013265920 * 2))) + (2013265920 * ((f0 * f1) + (f0 * f3)))) * rd0)) + w) + (2013265920 * (((((f0 * f2) + (f1 * f2)) + (f1 * f3)) + (f2 * f3)) * prev0))) = 0)
    (b0 : isByte rd0) (b1 : isByte rd1) (b2 : isByte rd2) (b3 : isByte rd3) :
    isByte w := by
  rw [babyBear_negOne] at hsel hw
  -- The one coefficient that is `-1` only after reducing mod `babyBear`; `ring` cannot see it.
  have hc : (1006632960 * 2 : ZMod babyBear) = -1 := by decide
  rcases zmod_tritElim t0 with rfl | rfl | rfl <;>
    rcases zmod_tritElim t1 with rfl | rfl | rfl <;>
      rcases zmod_tritElim t2 with rfl | rfl | rfl <;>
        rcases zmod_tritElim t3 with rfl | rfl | rfl <;>
  first
    | exact absurd hsel (by decide)
    | (rw [show w = rd0 from by linear_combination hw - rd0 * hc]; exact b0)
    | (rw [show w = rd1 from by linear_combination hw]; exact b1)
    | (rw [show w = rd2 from by linear_combination hw]; exact b2)
    | (rw [show w = rd3 from by linear_combination hw]; exact b3)

/-- **Why each of the two register writes is byte-valued.** Each sends the byte its own load
    selected out of the word it read; `isByte_of_loadSelect` turns the block's flag constraints
    into "that byte is one of the four limbs", and those limbs come from the main-memory receive
    that precedes the write, which `sendsOk`'s own hypothesis vouches for. -/
theorem optWriteOk {asg : ChipAssignment babyBear}
    (halg : opt.satisfiesAlgebraic asg)
    (i : Fin opt.busInteractions.length) (hwit : witnesses.getD i.val .notSend = .external)
    (hlow : ∀ j : Fin opt.busInteractions.length, j < i → opt.activeStateful apcRules asg j →
      apcRules.payloadOk (opt.msgAt asg j)) :
    apcRules.payloadOk (opt.msgAt asg i) := by
  haveI : Fact (1 < babyBear) := ⟨by decide⟩
  have hpo : apcRules.payloadOk = openVmPayloadOk (p := babyBear) defaultBusMap := rfl
  have c0 := halg _ (List.get_mem opt.algebraicConstraints ⟨0, by decide⟩)
  have c1 := halg _ (List.get_mem opt.algebraicConstraints ⟨1, by decide⟩)
  have c2 := halg _ (List.get_mem opt.algebraicConstraints ⟨2, by decide⟩)
  have c3 := halg _ (List.get_mem opt.algebraicConstraints ⟨3, by decide⟩)
  have c6 := halg _ (List.get_mem opt.algebraicConstraints ⟨6, by decide⟩)
  have c12 := halg _ (List.get_mem opt.algebraicConstraints ⟨12, by decide⟩)
  have d0 := halg _ (List.get_mem opt.algebraicConstraints ⟨13, by decide⟩)
  have d1 := halg _ (List.get_mem opt.algebraicConstraints ⟨14, by decide⟩)
  have d2 := halg _ (List.get_mem opt.algebraicConstraints ⟨15, by decide⟩)
  have d3 := halg _ (List.get_mem opt.algebraicConstraints ⟨16, by decide⟩)
  have d19 := halg _ (List.get_mem opt.algebraicConstraints ⟨19, by decide⟩)
  have d25 := halg _ (List.get_mem opt.algebraicConstraints ⟨25, by decide⟩)
  simp only [opt, Expression.eval, List.get] at c0 c1 c2 c3 c6 c12 d0 d1 d2 d3 d19 d25
  fin_cases i
  all_goals try exact absurd hwit (by decide)
  · -- position 11: the first load's write, off its main-memory receive at 2
    have hr := hlow ⟨2, by decide⟩ (by decide) ⟨by decide, babyBear_negOne_ne_zero⟩
    rw [hpo] at hr
    obtain ⟨r0, r1, r2, r3⟩ :=
      (openVmPayloadOk_mem_iff_of_byteChecked (p := babyBear) (asp := 2) (Or.inr (by decide))
        _ _ _ _ _ _).mp hr
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 52,
      asg ⟨"write_data__0_0", some 37⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 6])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
      ⟨isByte_of_loadSelect
         (f0 := asg ⟨"flags__0_0", some 23⟩) (f1 := asg ⟨"flags__1_0", some 24⟩)
         (f2 := asg ⟨"flags__2_0", some 25⟩) (f3 := asg ⟨"flags__3_0", some 26⟩)
         (rd0 := asg ⟨"read_data__0_0", some 29⟩)
         (rd1 := asg ⟨"read_data__1_0", some 30⟩)
         (rd2 := asg ⟨"read_data__2_0", some 31⟩)
         (rd3 := asg ⟨"read_data__3_0", some 32⟩)
         (prev0 := asg ⟨"prev_data__0_0", some 33⟩)
         (w := asg ⟨"write_data__0_0", some 37⟩)
         (by linear_combination c0) (by linear_combination c1)
         (by linear_combination c2) (by linear_combination c3) (by linear_combination c12)
         (by linear_combination c6) r0 r1 r2 r3,
       isByte_zero, isByte_zero, isByte_zero⟩
  · -- position 12: the second load's write, off its main-memory receive at 8
    have hr := hlow ⟨8, by decide⟩ (by decide) ⟨by decide, babyBear_negOne_ne_zero⟩
    rw [hpo] at hr
    obtain ⟨r0, r1, r2, r3⟩ :=
      (openVmPayloadOk_mem_iff_of_byteChecked (p := babyBear) (asp := 2) (Or.inr (by decide))
        _ _ _ _ _ _).mp hr
    show openVmPayloadOk defaultBusMap ((1 : ℕ), [(1 : ZMod babyBear), 56,
      asg ⟨"write_data__0_1", some 78⟩, 0, 0, 0, asg ⟨"from_state__timestamp_0", some 1⟩ + 7])
    exact (openVmPayloadOk_mem_iff _ _ _ _ _ _).mpr
      ⟨isByte_of_loadSelect
         (f0 := asg ⟨"flags__0_1", some 64⟩) (f1 := asg ⟨"flags__1_1", some 65⟩)
         (f2 := asg ⟨"flags__2_1", some 66⟩) (f3 := asg ⟨"flags__3_1", some 67⟩)
         (rd0 := asg ⟨"read_data__0_1", some 70⟩)
         (rd1 := asg ⟨"read_data__1_1", some 71⟩)
         (rd2 := asg ⟨"read_data__2_1", some 72⟩)
         (rd3 := asg ⟨"read_data__3_1", some 73⟩)
         (prev0 := asg ⟨"prev_data__0_1", some 74⟩)
         (w := asg ⟨"write_data__0_1", some 78⟩)
         (by linear_combination d0) (by linear_combination d1)
         (by linear_combination d2) (by linear_combination d3) (by linear_combination d25)
         (by linear_combination d19) r0 r1 r2 r3,
       isByte_zero, isByte_zero, isByte_zero⟩

end ApcOptimizer.OpenVM.TwoLoads
