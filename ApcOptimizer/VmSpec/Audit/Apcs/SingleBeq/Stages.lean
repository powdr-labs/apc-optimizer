import ApcOptimizer.VmSpec.OpenVm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! **A single OpenVM `beq` instruction, at three points of powdr's pipeline.**

    `if [x8] == [x5] jump +2` -- powdr's `single_beq` APC-builder test. Two register reads echoed
    straight back, no write at all, and a bridge send whose `pc` depends on the comparison
    (`4 - 2 * cmp_result_0`) -- a *branching* step, where `SingleXor` and `Keccak2105000`'s
    optimized stages hand on a literal. One instruction, so there is nothing to chain.

    `unopt`, `opt` and `gated` are emitted verbatim from the stage dumps by
    `Scripts/emit-apc-lean.py`; `gatedPinned` is the modification the proofs need. One file per
    stage carries its proofs -- see `Audit/Legality/All.lean`. -/

namespace ApcOptimizer.OpenVM.SingleBeq


/-- `unopt`, emitted verbatim from `apc_candidate_0_000_unopt.json`
    by `Scripts/emit-apc-lean.py`: 21 algebraic constraints, 11 bus interactions. -/
def unopt : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.var ⟨"opcode_beq_flag_0", some 20⟩) (.add (.var ⟨"opcode_beq_flag_0", some 20⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"opcode_bne_flag_0", some 21⟩) (.add (.var ⟨"opcode_bne_flag_0", some 21⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)) (.add (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"cmp_result_0", some 18⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.mul (.var ⟨"cmp_result_0", some 18⟩) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_0", some 18⟩))) (.var ⟨"opcode_bne_flag_0", some 21⟩))) (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩)))
    , .mul (.add (.mul (.var ⟨"cmp_result_0", some 18⟩) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_0", some 18⟩))) (.var ⟨"opcode_bne_flag_0", some 21⟩))) (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩)))
    , .mul (.add (.mul (.var ⟨"cmp_result_0", some 18⟩) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_0", some 18⟩))) (.var ⟨"opcode_bne_flag_0", some 21⟩))) (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩)))
    , .mul (.add (.mul (.var ⟨"cmp_result_0", some 18⟩) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_0", some 18⟩))) (.var ⟨"opcode_bne_flag_0", some 21⟩))) (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩)))
    , .mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)) (.add (.add (.add (.add (.add (.add (.mul (.var ⟨"cmp_result_0", some 18⟩) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_0", some 18⟩))) (.var ⟨"opcode_bne_flag_0", some 21⟩))) (.mul (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩))) (.var ⟨"diff_inv_marker__0_0", some 22⟩))) (.mul (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩))) (.var ⟨"diff_inv_marker__1_0", some 23⟩))) (.mul (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩))) (.var ⟨"diff_inv_marker__2_0", some 24⟩))) (.mul (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩))) (.var ⟨"diff_inv_marker__3_0", some 25⟩))) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)) (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 0)) (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩))) (.mul (.const 2013265920) (.const 1))) (.mul (.const 2013265920) (.add (.add (.const 0) (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩) (.const 1))) (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 6⟩) (.const 131072)))))
    , .mul (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)) (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)) (.mul (.const 2013265920) (.var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩))) (.mul (.const 2013265920) (.const 1))) (.mul (.const 2013265920) (.add (.add (.const 0) (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩) (.const 1))) (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 9⟩) (.const 131072)))))
    , .add (.mul (.const 2013265920) (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩))) (.const 1)
    , .add (.var ⟨"from_state__pc_0", some 0⟩) (.mul (.const 2013265920) (.const 0))
    , .add (.add (.add (.add (.const 0) (.mul (.var ⟨"opcode_beq_flag_0", some 20⟩) (.const 0))) (.mul (.var ⟨"opcode_bne_flag_0", some 21⟩) (.const 1))) (.const 544)) (.mul (.const 2013265920) (.const 544))
    , .add (.var ⟨"rs1_ptr_0", some 2⟩) (.mul (.const 2013265920) (.const 8))
    , .add (.var ⟨"rs2_ptr_0", some 3⟩) (.mul (.const 2013265920) (.const 5))
    , .add (.var ⟨"imm_0", some 19⟩) (.mul (.const 2013265920) (.const 2))
    , .add (.const 1) (.mul (.const 2013265920) (.const 1))
    , .add (.const 1) (.mul (.const 2013265920) (.const 1))
    , .add (.const 0) (.mul (.const 2013265920) (.const 0))
    , .add (.const 0) (.mul (.const 2013265920) (.const 0)) ]
  busInteractions :=
    [ { busId := 3, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩, .const 17] }
    , { busId := 3, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 6⟩, .const 12] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)),
        payload := [.const 1, .var ⟨"rs1_ptr_0", some 2⟩, .var ⟨"a__0_0", some 10⟩, .var ⟨"a__1_0", some 11⟩, .var ⟨"a__2_0", some 12⟩, .var ⟨"a__3_0", some 13⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩] }
    , { busId := 1, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.const 1, .var ⟨"rs1_ptr_0", some 2⟩, .var ⟨"a__0_0", some 10⟩, .var ⟨"a__1_0", some 11⟩, .var ⟨"a__2_0", some 12⟩, .var ⟨"a__3_0", some 13⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 0)] }
    , { busId := 3, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩, .const 17] }
    , { busId := 3, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 9⟩, .const 12] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)),
        payload := [.const 1, .var ⟨"rs2_ptr_0", some 3⟩, .var ⟨"b__0_0", some 14⟩, .var ⟨"b__1_0", some 15⟩, .var ⟨"b__2_0", some 16⟩, .var ⟨"b__3_0", some 17⟩, .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩] }
    , { busId := 1, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.const 1, .var ⟨"rs2_ptr_0", some 3⟩, .var ⟨"b__0_0", some 14⟩, .var ⟨"b__1_0", some 15⟩, .var ⟨"b__2_0", some 16⟩, .var ⟨"b__3_0", some 17⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 2, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.var ⟨"from_state__pc_0", some 0⟩, .add (.add (.add (.const 0) (.mul (.var ⟨"opcode_beq_flag_0", some 20⟩) (.const 0))) (.mul (.var ⟨"opcode_bne_flag_0", some 21⟩) (.const 1))) (.const 544), .var ⟨"rs1_ptr_0", some 2⟩, .var ⟨"rs2_ptr_0", some 3⟩, .var ⟨"imm_0", some 19⟩, .const 1, .const 1, .const 0, .const 0] }
    , { busId := 0, multiplicity := .mul (.const 2013265920) (.add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩)),
        payload := [.var ⟨"from_state__pc_0", some 0⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 0, multiplicity := .add (.add (.const 0) (.var ⟨"opcode_beq_flag_0", some 20⟩)) (.var ⟨"opcode_bne_flag_0", some 21⟩),
        payload := [.add (.add (.var ⟨"from_state__pc_0", some 0⟩) (.mul (.var ⟨"cmp_result_0", some 18⟩) (.var ⟨"imm_0", some 19⟩))) (.mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"cmp_result_0", some 18⟩))) (.const 4)), .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)] } ]

/-- `opt`, emitted verbatim from `apc_candidate_0_028_trivial_simp.json`
    by `Scripts/emit-apc-lean.py`: 6 algebraic constraints, 10 bus interactions. -/
def opt : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"cmp_result_0", some 18⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩)))
    , .add (.add (.mul (.var ⟨"free_var_30", some 30⟩) (.add (.add (.add (.mul (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩))) (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩)))) (.mul (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩))) (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩))))) (.mul (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩))) (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩))))) (.mul (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩))) (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩)))))) (.var ⟨"cmp_result_0", some 18⟩)) (.mul (.const 2013265920) (.const 1)) ]
  busInteractions :=
    [ { busId := 1, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 1, .const 8, .var ⟨"a__0_0", some 10⟩, .var ⟨"a__1_0", some 11⟩, .var ⟨"a__2_0", some 12⟩, .var ⟨"a__3_0", some 13⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 8, .var ⟨"a__0_0", some 10⟩, .var ⟨"a__1_0", some 11⟩, .var ⟨"a__2_0", some 12⟩, .var ⟨"a__3_0", some 13⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 1, .const 5, .var ⟨"b__0_0", some 14⟩, .var ⟨"b__1_0", some 15⟩, .var ⟨"b__2_0", some 16⟩, .var ⟨"b__3_0", some 17⟩, .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 5, .var ⟨"b__0_0", some 14⟩, .var ⟨"b__1_0", some 15⟩, .var ⟨"b__2_0", some 16⟩, .var ⟨"b__3_0", some 17⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 0, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 0, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 0, multiplicity := .const 1,
        payload := [.add (.const 4) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"cmp_result_0", some 18⟩))), .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩))) (.const 15360)) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩))) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] } ]

/-- `gated`, emitted verbatim from `apc_candidate_0_029.json`
    by `Scripts/emit-apc-lean.py`: 7 algebraic constraints, 10 bus interactions. -/
def gated : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"cmp_result_0", some 18⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩)))
    , .mul (.var ⟨"cmp_result_0", some 18⟩) (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩)))
    , .add (.add (.mul (.var ⟨"free_var_30", some 30⟩) (.add (.add (.add (.mul (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩))) (.add (.var ⟨"a__0_0", some 10⟩) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 14⟩)))) (.mul (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩))) (.add (.var ⟨"a__1_0", some 11⟩) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 15⟩))))) (.mul (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩))) (.add (.var ⟨"a__2_0", some 12⟩) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 16⟩))))) (.mul (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩))) (.add (.var ⟨"a__3_0", some 13⟩) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 17⟩)))))) (.var ⟨"cmp_result_0", some 18⟩)) (.mul (.const 2013265920) (.var ⟨"is_valid", some 31⟩))
    , .mul (.var ⟨"is_valid", some 31⟩) (.add (.var ⟨"is_valid", some 31⟩) (.mul (.const 2013265920) (.const 1))) ]
  busInteractions :=
    [ { busId := 1, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 31⟩),
        payload := [.const 1, .const 8, .var ⟨"a__0_0", some 10⟩, .var ⟨"a__1_0", some 11⟩, .var ⟨"a__2_0", some 12⟩, .var ⟨"a__3_0", some 13⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩] }
    , { busId := 1, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.const 1, .const 8, .var ⟨"a__0_0", some 10⟩, .var ⟨"a__1_0", some 11⟩, .var ⟨"a__2_0", some 12⟩, .var ⟨"a__3_0", some 13⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 31⟩),
        payload := [.const 1, .const 5, .var ⟨"b__0_0", some 14⟩, .var ⟨"b__1_0", some 15⟩, .var ⟨"b__2_0", some 16⟩, .var ⟨"b__3_0", some 17⟩, .var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩] }
    , { busId := 1, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.const 1, .const 5, .var ⟨"b__0_0", some 14⟩, .var ⟨"b__1_0", some 15⟩, .var ⟨"b__2_0", some 16⟩, .var ⟨"b__3_0", some 17⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 0, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 31⟩),
        payload := [.const 0, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 0, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.add (.const 4) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"cmp_result_0", some 18⟩))), .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩, .const 17] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.add (.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 4⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 5⟩))) (.const 15360)) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩, .const 17] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 31⟩,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__1__base__prev_timestamp_0", some 7⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩))) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] } ]

/-- `gated` with `is_valid` pinned to `1`, closing off the padding row that makes
    `gated_not_hasStepLayout` false. Defined by appending to `gated` rather than restating it. -/
def gatedPinned : Circuit babyBear :=
  { gated with
    algebraicConstraints := gated.algebraicConstraints ++
      [ .add (.var ⟨"is_valid", some 31⟩) (.mul (.const 2013265920) (.const 1)) ] }

end ApcOptimizer.OpenVM.SingleBeq
