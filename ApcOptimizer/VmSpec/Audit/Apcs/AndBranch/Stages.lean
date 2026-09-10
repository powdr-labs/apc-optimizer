import ApcOptimizer.VmSpec.OpenVm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! **The `andi`/`bnez` block at pc `0x200bd4`, after powdr's optimizer.**

    Two fused instructions: `andi rd, rs, 2` masks the low bits of a register, and the branch that
    follows tests the result against zero. The `.powdr_opt` dump the benchmark ships is the
    pre-gate stage -- multiplicities are literal `±1` -- so this is the analogue of
    `Keccak2105000`'s `opt`. See `Audit/Legality/All.lean`. -/

namespace ApcOptimizer.OpenVM.AndBranch

/-- `opt`, emitted verbatim from `Benchmarks/OpenVM/openvm-eth/apc_056_pc0x200bd4.powdr_opt.json.gz`
    by `Scripts/emit-apc-lean.py`: 3 algebraic constraints, 15 bus interactions. -/
def opt : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.var ⟨"cmp_result_1", some 54⟩) (.add (.var ⟨"cmp_result_1", some 54⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 54⟩))) (.var ⟨"a__0_0", some 19⟩)
    , .add (.mul (.var ⟨"free_var_64", some 64⟩) (.var ⟨"a__0_0", some 19⟩)) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 54⟩)) ]
  busInteractions :=
    [ { busId := 6, multiplicity := .const 1,
        payload := [.var ⟨"b__0_0", some 23⟩, .const 2, .add (.add (.var ⟨"b__0_0", some 23⟩) (.const 2)) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"a__0_0", some 19⟩))), .const 1] }
    , { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 1, .const 48, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 48, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 1, .const 44, .var ⟨"writes_aux__prev_data__0_0", some 15⟩, .var ⟨"writes_aux__prev_data__1_0", some 16⟩, .var ⟨"writes_aux__prev_data__2_0", some 17⟩, .var ⟨"writes_aux__prev_data__3_0", some 18⟩, .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩] }
    , { busId := 0, multiplicity := .const 2013265920,
        payload := [.const 2100180, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 44, .var ⟨"a__0_0", some 19⟩, .const 0, .const 0, .const 0, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3)] }
    , { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 1, .const 0, .const 0, .const 0, .const 0, .const 0, .var ⟨"reads_aux__1__base__prev_timestamp_1", some 43⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 0, .const 0, .const 0, .const 0, .const 0, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 4)] }
    , { busId := 0, multiplicity := .const 1,
        payload := [.add (.mul (.const 12) (.var ⟨"cmp_result_1", some 54⟩)) (.const 2100188), .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 5)] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩))) (.const 15360)) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)) (.mul (.const 15360) (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩))) (.mul (.const 2013265920) (.add (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩)) (.const 15360))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_1", some 44⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__1__base__prev_timestamp_1", some 43⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_1", some 44⟩))) (.mul (.const 2013265920) (.add (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩)) (.const 46080))), .const 12] } ]

end ApcOptimizer.OpenVM.AndBranch
