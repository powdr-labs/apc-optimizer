import ApcOptimizer.VmSpec.OpenVm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! **The `loadw`/`beq` block at pc `0x391014`, after powdr's optimizer.**

    Two fused instructions: a word load through a pointer held in a register, and a branch
    comparing the loaded word to another register. Unlike every other APC audited here it touches
    *main memory* -- address space `2`, at a pointer the circuit computes -- and it reaches the
    bitwise table not at all. The `.powdr_opt` dump the benchmark ships is the pre-gate stage, the
    analogue of `Keccak2105000`'s `opt`. See `Audit/Legality/All.lean`. -/

namespace ApcOptimizer.OpenVM.LoadBranch

/-- `opt`, emitted verbatim from `Benchmarks/OpenVM/openvm-eth/apc_072_pc0x391014.powdr_opt.json.gz`
    by `Scripts/emit-apc-lean.py`: 8 algebraic constraints, 20 bus interactions. -/
def opt : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.add (.mul (.const 30720) (.var ⟨"mem_ptr_limbs__0_0", some 16⟩)) (.mul (.const 2013265920) (.add (.mul (.const 30720) (.var ⟨"rs1_data__0_0", some 3⟩)) (.mul (.const 7864320) (.var ⟨"rs1_data__1_0", some 4⟩))))) (.add (.mul (.const 30720) (.var ⟨"mem_ptr_limbs__0_0", some 16⟩)) (.mul (.const 2013265920) (.add (.add (.mul (.const 30720) (.var ⟨"rs1_data__0_0", some 3⟩)) (.mul (.const 7864320) (.var ⟨"rs1_data__1_0", some 4⟩))) (.const 1))))
    , .mul (.add (.add (.mul (.const 943718400) (.var ⟨"rs1_data__0_0", some 3⟩)) (.mul (.const 30720) (.var ⟨"mem_ptr_limbs__1_0", some 17⟩))) (.mul (.const 2013265920) (.add (.add (.add (.mul (.const 120) (.var ⟨"rs1_data__1_0", some 4⟩)) (.mul (.const 30720) (.var ⟨"rs1_data__2_0", some 5⟩))) (.mul (.const 7864320) (.var ⟨"rs1_data__3_0", some 6⟩))) (.mul (.const 943718400) (.var ⟨"mem_ptr_limbs__0_0", some 16⟩))))) (.add (.add (.mul (.const 943718400) (.var ⟨"rs1_data__0_0", some 3⟩)) (.mul (.const 30720) (.var ⟨"mem_ptr_limbs__1_0", some 17⟩))) (.mul (.const 2013265920) (.add (.add (.add (.add (.mul (.const 120) (.var ⟨"rs1_data__1_0", some 4⟩)) (.mul (.const 30720) (.var ⟨"rs1_data__2_0", some 5⟩))) (.mul (.const 7864320) (.var ⟨"rs1_data__3_0", some 6⟩))) (.mul (.const 943718400) (.var ⟨"mem_ptr_limbs__0_0", some 16⟩))) (.const 1))))
    , .mul (.var ⟨"cmp_result_1", some 59⟩) (.add (.var ⟨"cmp_result_1", some 59⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 59⟩))) (.add (.var ⟨"a__0_1", some 51⟩) (.mul (.const 2013265920) (.var ⟨"read_data__0_0", some 29⟩)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 59⟩))) (.add (.var ⟨"a__1_1", some 52⟩) (.mul (.const 2013265920) (.var ⟨"read_data__1_0", some 30⟩)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 59⟩))) (.add (.var ⟨"a__2_1", some 53⟩) (.mul (.const 2013265920) (.var ⟨"read_data__2_0", some 31⟩)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 59⟩))) (.add (.var ⟨"a__3_1", some 54⟩) (.mul (.const 2013265920) (.var ⟨"read_data__3_0", some 32⟩)))
    , .add (.mul (.var ⟨"free_var_72", some 72⟩) (.add (.add (.add (.mul (.add (.var ⟨"a__0_1", some 51⟩) (.mul (.const 2013265920) (.var ⟨"read_data__0_0", some 29⟩))) (.add (.var ⟨"a__0_1", some 51⟩) (.mul (.const 2013265920) (.var ⟨"read_data__0_0", some 29⟩)))) (.mul (.add (.var ⟨"a__1_1", some 52⟩) (.mul (.const 2013265920) (.var ⟨"read_data__1_0", some 30⟩))) (.add (.var ⟨"a__1_1", some 52⟩) (.mul (.const 2013265920) (.var ⟨"read_data__1_0", some 30⟩))))) (.mul (.add (.var ⟨"a__2_1", some 53⟩) (.mul (.const 2013265920) (.var ⟨"read_data__2_0", some 31⟩))) (.add (.var ⟨"a__2_1", some 53⟩) (.mul (.const 2013265920) (.var ⟨"read_data__2_0", some 31⟩))))) (.mul (.add (.var ⟨"a__3_1", some 54⟩) (.mul (.const 2013265920) (.var ⟨"read_data__3_0", some 32⟩))) (.add (.var ⟨"a__3_1", some 54⟩) (.mul (.const 2013265920) (.var ⟨"read_data__3_0", some 32⟩)))))) (.mul (.const 2013265920) (.var ⟨"cmp_result_1", some 59⟩)) ]
  busInteractions :=
    [ { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 1, .const 8, .var ⟨"rs1_data__0_0", some 3⟩, .var ⟨"rs1_data__1_0", some 4⟩, .var ⟨"rs1_data__2_0", some 5⟩, .var ⟨"rs1_data__3_0", some 6⟩, .var ⟨"rs1_aux_cols__base__prev_timestamp_0", some 7⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 8, .var ⟨"rs1_data__0_0", some 3⟩, .var ⟨"rs1_data__1_0", some 4⟩, .var ⟨"rs1_data__2_0", some 5⟩, .var ⟨"rs1_data__3_0", some 6⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 2, .add (.var ⟨"mem_ptr_limbs__0_0", some 16⟩) (.mul (.const 65536) (.var ⟨"mem_ptr_limbs__1_0", some 17⟩)), .var ⟨"read_data__0_0", some 29⟩, .var ⟨"read_data__1_0", some 30⟩, .var ⟨"read_data__2_0", some 31⟩, .var ⟨"read_data__3_0", some 32⟩, .var ⟨"read_data_aux__base__prev_timestamp_0", some 11⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 2, .add (.var ⟨"mem_ptr_limbs__0_0", some 16⟩) (.mul (.const 65536) (.var ⟨"mem_ptr_limbs__1_0", some 17⟩)), .var ⟨"read_data__0_0", some 29⟩, .var ⟨"read_data__1_0", some 30⟩, .var ⟨"read_data__2_0", some 31⟩, .var ⟨"read_data__3_0", some 32⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 1, .const 40, .var ⟨"prev_data__0_0", some 33⟩, .var ⟨"prev_data__1_0", some 34⟩, .var ⟨"prev_data__2_0", some 35⟩, .var ⟨"prev_data__3_0", some 36⟩, .var ⟨"write_base_aux__prev_timestamp_0", some 19⟩] }
    , { busId := 0, multiplicity := .const 2013265920,
        payload := [.const 3739668, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .const 2013265920,
        payload := [.const 1, .const 88, .var ⟨"a__0_1", some 51⟩, .var ⟨"a__1_1", some 52⟩, .var ⟨"a__2_1", some 53⟩, .var ⟨"a__3_1", some 54⟩, .var ⟨"reads_aux__0__base__prev_timestamp_1", some 45⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 88, .var ⟨"a__0_1", some 51⟩, .var ⟨"a__1_1", some 52⟩, .var ⟨"a__2_1", some 53⟩, .var ⟨"a__3_1", some 54⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3)] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 40, .var ⟨"read_data__0_0", some 29⟩, .var ⟨"read_data__1_0", some 30⟩, .var ⟨"read_data__2_0", some 31⟩, .var ⟨"read_data__3_0", some 32⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 4)] }
    , { busId := 0, multiplicity := .const 1,
        payload := [.add (.const 3739676) (.mul (.const 2013265920) (.mul (.const 56) (.var ⟨"cmp_result_1", some 59⟩))), .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 5)] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"rs1_aux_cols__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.add (.mul (.const 15360) (.var ⟨"rs1_aux_cols__base__prev_timestamp_0", some 7⟩)) (.mul (.const 15360) (.var ⟨"rs1_aux_cols__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩))) (.const 15360)) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.mul (.const 2013265920) (.mul (.const 503316480) (.var ⟨"mem_ptr_limbs__0_0", some 16⟩)), .const 14] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"read_data_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 12⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"read_data_aux__base__prev_timestamp_0", some 11⟩)) (.mul (.const 15360) (.var ⟨"read_data_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 12⟩))) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"write_base_aux__timestamp_lt_aux__lower_decomp__0_0", some 20⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"write_base_aux__prev_timestamp_0", some 19⟩)) (.mul (.const 15360) (.var ⟨"write_base_aux__timestamp_lt_aux__lower_decomp__0_0", some 20⟩))) (.mul (.const 2013265920) (.add (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩)) (.const 15360))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 46⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__0__base__prev_timestamp_1", some 45⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 46⟩))) (.mul (.const 2013265920) (.add (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩)) (.const 30720))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"mem_ptr_limbs__1_0", some 17⟩, .const 13] } ]

end ApcOptimizer.OpenVM.LoadBranch
