import ApcOptimizer.VmSpec.OpenVm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! **A single OpenVM `xor` instruction, at three points of powdr's pipeline.**

    `[x8] = [x7] ^ [x5]` -- powdr's `single_xor` APC-builder test. Two register reads echoed
    straight back, one register write whose limbs the bitwise table computes, and the three
    AssertLt gadgets that date the reads. One instruction, so unlike `Keccak2105000` there is
    nothing to chain: `unopt` is already a single step.

    `unopt`, `opt` and `gated` are emitted verbatim from the stage dumps by
    `Scripts/emit-apc-lean.py`; `gatedPinned` is the modification the proofs need. One file per
    stage carries its proofs -- see `Audit/Legality/All.lean`. -/

namespace ApcOptimizer.OpenVM.SingleXor


/-- `unopt`, emitted verbatim from `apc_candidate_0_000_unopt.json`
    by `Scripts/emit-apc-lean.py`: 32 algebraic constraints, 20 bus interactions. -/
def unopt : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.add (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.add (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.add (.var ⟨"opcode_or_flag_0", some 34⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.add (.var ⟨"opcode_and_flag_0", some 35⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.add (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"a__1_0", some 20⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"a__1_0", some 20⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__1_0", some 20⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__1_0", some 20⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__2_0", some 25⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"a__2_0", some 21⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"a__1_0", some 20⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))))))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__2_0", some 25⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"a__2_0", some 21⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"a__1_0", some 20⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))))))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__2_0", some 21⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 25⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__1_0", some 20⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))))))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__2_0", some 21⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 25⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__1_0", some 20⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))))))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__3_0", some 26⟩) (.var ⟨"c__3_0", some 30⟩)) (.mul (.const 2013265920) (.var ⟨"a__3_0", some 22⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__2_0", some 25⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"a__2_0", some 21⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"a__1_0", some 20⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))))))))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__3_0", some 26⟩) (.var ⟨"c__3_0", some 30⟩)) (.mul (.const 2013265920) (.var ⟨"a__3_0", some 22⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__2_0", some 25⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"a__2_0", some 21⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"a__1_0", some 20⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"a__0_0", some 19⟩))) (.const 0))))))))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.mul (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__3_0", some 22⟩) (.var ⟨"c__3_0", some 30⟩)) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 26⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__2_0", some 21⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 25⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__1_0", some 20⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))))))))) (.add (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__3_0", some 22⟩) (.var ⟨"c__3_0", some 30⟩)) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 26⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__2_0", some 21⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 25⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__1_0", some 20⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2005401601) (.add (.add (.add (.var ⟨"a__0_0", some 19⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.const 0))))))))) (.mul (.const 2013265920) (.const 1))))
    , .mul (.var ⟨"rs2_as_0", some 5⟩) (.add (.var ⟨"rs2_as_0", some 5⟩) (.mul (.const 2013265920) (.const 1)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"rs2_as_0", some 5⟩))) (.add (.var ⟨"rs2_0", some 4⟩) (.mul (.const 2013265920) (.add (.add (.var ⟨"c__0_0", some 27⟩) (.mul (.var ⟨"c__1_0", some 28⟩) (.const 256))) (.mul (.var ⟨"c__2_0", some 29⟩) (.const 65536)))))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"rs2_as_0", some 5⟩))) (.add (.var ⟨"c__2_0", some 29⟩) (.mul (.const 2013265920) (.var ⟨"c__3_0", some 30⟩)))
    , .mul (.add (.const 1) (.mul (.const 2013265920) (.var ⟨"rs2_as_0", some 5⟩))) (.mul (.var ⟨"c__2_0", some 29⟩) (.add (.const 255) (.mul (.const 2013265920) (.var ⟨"c__2_0", some 29⟩))))
    , .mul (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 0)) (.mul (.const 2013265920) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩))) (.mul (.const 2013265920) (.const 1))) (.mul (.const 2013265920) (.add (.add (.const 0) (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩) (.const 1))) (.mul (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩) (.const 131072)))))
    , .mul (.var ⟨"rs2_as_0", some 5⟩) (.add (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.mul (.const 2013265920) (.const 1)))
    , .mul (.var ⟨"rs2_as_0", some 5⟩) (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)) (.mul (.const 2013265920) (.var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩))) (.mul (.const 2013265920) (.const 1))) (.mul (.const 2013265920) (.add (.add (.const 0) (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩) (.const 1))) (.mul (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 11⟩) (.const 131072)))))
    , .mul (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.add (.add (.add (.add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)) (.mul (.const 2013265920) (.var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩))) (.mul (.const 2013265920) (.const 1))) (.mul (.const 2013265920) (.add (.add (.const 0) (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩) (.const 1))) (.mul (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩) (.const 131072)))))
    , .add (.mul (.const 2013265920) (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩))) (.const 1)
    , .add (.var ⟨"from_state__pc_0", some 0⟩) (.mul (.const 2013265920) (.const 0))
    , .add (.add (.const 512) (.add (.add (.add (.add (.add (.const 0) (.mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.const 0))) (.mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.const 1))) (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.const 2))) (.mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.const 3))) (.mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.const 4)))) (.mul (.const 2013265920) (.const 514))
    , .add (.var ⟨"rd_ptr_0", some 2⟩) (.mul (.const 2013265920) (.const 8))
    , .add (.var ⟨"rs1_ptr_0", some 3⟩) (.mul (.const 2013265920) (.const 7))
    , .add (.var ⟨"rs2_0", some 4⟩) (.mul (.const 2013265920) (.const 5))
    , .add (.const 1) (.mul (.const 2013265920) (.const 1))
    , .add (.var ⟨"rs2_as_0", some 5⟩) (.mul (.const 2013265920) (.const 1))
    , .add (.const 0) (.mul (.const 2013265920) (.const 0))
    , .add (.const 0) (.mul (.const 2013265920) (.const 0)) ]
  busInteractions :=
    [ { busId := 6, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__0_0", some 19⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"b__0_0", some 23⟩)), .add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__0_0", some 19⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"c__0_0", some 27⟩)), .add (.add (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"a__0_0", some 19⟩)) (.mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.add (.add (.mul (.const 2) (.var ⟨"a__0_0", some 19⟩)) (.mul (.const 2013265920) (.var ⟨"b__0_0", some 23⟩))) (.mul (.const 2013265920) (.var ⟨"c__0_0", some 27⟩))))) (.mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.add (.add (.var ⟨"b__0_0", some 23⟩) (.var ⟨"c__0_0", some 27⟩)) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"a__0_0", some 19⟩))))), .const 1] }
    , { busId := 6, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__1_0", some 20⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"b__1_0", some 24⟩)), .add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__1_0", some 20⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"c__1_0", some 28⟩)), .add (.add (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"a__1_0", some 20⟩)) (.mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.add (.add (.mul (.const 2) (.var ⟨"a__1_0", some 20⟩)) (.mul (.const 2013265920) (.var ⟨"b__1_0", some 24⟩))) (.mul (.const 2013265920) (.var ⟨"c__1_0", some 28⟩))))) (.mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.add (.add (.var ⟨"b__1_0", some 24⟩) (.var ⟨"c__1_0", some 28⟩)) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"a__1_0", some 20⟩))))), .const 1] }
    , { busId := 6, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__2_0", some 21⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"b__2_0", some 25⟩)), .add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__2_0", some 21⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"c__2_0", some 29⟩)), .add (.add (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"a__2_0", some 21⟩)) (.mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.add (.add (.mul (.const 2) (.var ⟨"a__2_0", some 21⟩)) (.mul (.const 2013265920) (.var ⟨"b__2_0", some 25⟩))) (.mul (.const 2013265920) (.var ⟨"c__2_0", some 29⟩))))) (.mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.add (.add (.var ⟨"b__2_0", some 25⟩) (.var ⟨"c__2_0", some 29⟩)) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"a__2_0", some 21⟩))))), .const 1] }
    , { busId := 6, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__3_0", some 22⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"b__3_0", some 26⟩)), .add (.mul (.add (.const 1) (.mul (.const 2013265920) (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)))) (.var ⟨"a__3_0", some 22⟩)) (.mul (.add (.add (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.var ⟨"c__3_0", some 30⟩)), .add (.add (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.var ⟨"a__3_0", some 22⟩)) (.mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.add (.add (.mul (.const 2) (.var ⟨"a__3_0", some 22⟩)) (.mul (.const 2013265920) (.var ⟨"b__3_0", some 26⟩))) (.mul (.const 2013265920) (.var ⟨"c__3_0", some 30⟩))))) (.mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.add (.add (.var ⟨"b__3_0", some 26⟩) (.var ⟨"c__3_0", some 30⟩)) (.mul (.const 2013265920) (.mul (.const 2) (.var ⟨"a__3_0", some 22⟩))))), .const 1] }
    , { busId := 6, multiplicity := .add (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)) (.mul (.const 2013265920) (.var ⟨"rs2_as_0", some 5⟩)),
        payload := [.var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .const 0, .const 0] }
    , { busId := 3, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩, .const 17] }
    , { busId := 3, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0", some 8⟩, .const 12] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)),
        payload := [.const 1, .var ⟨"rs1_ptr_0", some 3⟩, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩] }
    , { busId := 1, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.const 1, .var ⟨"rs1_ptr_0", some 3⟩, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 0)] }
    , { busId := 3, multiplicity := .var ⟨"rs2_as_0", some 5⟩,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩, .const 17] }
    , { busId := 3, multiplicity := .var ⟨"rs2_as_0", some 5⟩,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_0", some 11⟩, .const 12] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.var ⟨"rs2_as_0", some 5⟩),
        payload := [.var ⟨"rs2_as_0", some 5⟩, .var ⟨"rs2_0", some 4⟩, .var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"c__3_0", some 30⟩, .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩] }
    , { busId := 1, multiplicity := .var ⟨"rs2_as_0", some 5⟩,
        payload := [.var ⟨"rs2_as_0", some 5⟩, .var ⟨"rs2_0", some 4⟩, .var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"c__3_0", some 30⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 3, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩, .const 17] }
    , { busId := 3, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__1_0", some 14⟩, .const 12] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)),
        payload := [.const 1, .var ⟨"rd_ptr_0", some 2⟩, .var ⟨"writes_aux__prev_data__0_0", some 15⟩, .var ⟨"writes_aux__prev_data__1_0", some 16⟩, .var ⟨"writes_aux__prev_data__2_0", some 17⟩, .var ⟨"writes_aux__prev_data__3_0", some 18⟩, .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩] }
    , { busId := 1, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.const 1, .var ⟨"rd_ptr_0", some 2⟩, .var ⟨"a__0_0", some 19⟩, .var ⟨"a__1_0", some 20⟩, .var ⟨"a__2_0", some 21⟩, .var ⟨"a__3_0", some 22⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)] }
    , { busId := 2, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.var ⟨"from_state__pc_0", some 0⟩, .add (.const 512) (.add (.add (.add (.add (.add (.const 0) (.mul (.var ⟨"opcode_add_flag_0", some 31⟩) (.const 0))) (.mul (.var ⟨"opcode_sub_flag_0", some 32⟩) (.const 1))) (.mul (.var ⟨"opcode_xor_flag_0", some 33⟩) (.const 2))) (.mul (.var ⟨"opcode_or_flag_0", some 34⟩) (.const 3))) (.mul (.var ⟨"opcode_and_flag_0", some 35⟩) (.const 4))), .var ⟨"rd_ptr_0", some 2⟩, .var ⟨"rs1_ptr_0", some 3⟩, .var ⟨"rs2_0", some 4⟩, .const 1, .var ⟨"rs2_as_0", some 5⟩, .const 0, .const 0] }
    , { busId := 0, multiplicity := .mul (.const 2013265920) (.add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩)),
        payload := [.var ⟨"from_state__pc_0", some 0⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 0, multiplicity := .add (.add (.add (.add (.add (.const 0) (.var ⟨"opcode_add_flag_0", some 31⟩)) (.var ⟨"opcode_sub_flag_0", some 32⟩)) (.var ⟨"opcode_xor_flag_0", some 33⟩)) (.var ⟨"opcode_or_flag_0", some 34⟩)) (.var ⟨"opcode_and_flag_0", some 35⟩),
        payload := [.add (.var ⟨"from_state__pc_0", some 0⟩) (.const 4), .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3)] } ]

/-- `opt`, emitted verbatim from `apc_candidate_0_028_trivial_simp.json`
    by `Scripts/emit-apc-lean.py`: 0 algebraic constraints, 18 bus interactions. -/
def opt : Circuit babyBear where
  algebraicConstraints :=
    [  ]
  busInteractions :=
    [ { busId := 6, multiplicity := .const 1,
        payload := [.var ⟨"b__0_0", some 23⟩, .var ⟨"c__0_0", some 27⟩, .var ⟨"a__0_0", some 19⟩, .const 1] }
    , { busId := 6, multiplicity := .const 1,
        payload := [.var ⟨"b__1_0", some 24⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"a__1_0", some 20⟩, .const 1] }
    , { busId := 6, multiplicity := .const 1,
        payload := [.var ⟨"b__2_0", some 25⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"a__2_0", some 21⟩, .const 1] }
    , { busId := 6, multiplicity := .const 1,
        payload := [.var ⟨"b__3_0", some 26⟩, .var ⟨"c__3_0", some 30⟩, .var ⟨"a__3_0", some 22⟩, .const 1] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 1, .const 7, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 7, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 1, .const 5, .var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"c__3_0", some 30⟩, .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 5, .var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"c__3_0", some 30⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 1, .const 8, .var ⟨"writes_aux__prev_data__0_0", some 15⟩, .var ⟨"writes_aux__prev_data__1_0", some 16⟩, .var ⟨"writes_aux__prev_data__2_0", some 17⟩, .var ⟨"writes_aux__prev_data__3_0", some 18⟩, .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩] }
    , { busId := 1, multiplicity := .const 1,
        payload := [.const 1, .const 8, .var ⟨"a__0_0", some 19⟩, .var ⟨"a__1_0", some 20⟩, .var ⟨"a__2_0", some 21⟩, .var ⟨"a__3_0", some 22⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)] }
    , { busId := 0, multiplicity := .mul (.const 2013265920) (.const 1),
        payload := [.const 0, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 0, multiplicity := .const 1,
        payload := [.const 4, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3)] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩))) (.const 15360)) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩))) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩, .const 17] }
    , { busId := 3, multiplicity := .const 1,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)) (.mul (.const 15360) (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩))) (.mul (.const 2013265920) (.add (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩)) (.const 15360))), .const 12] } ]

/-- `gated`, emitted verbatim from `apc_candidate_0_029.json`
    by `Scripts/emit-apc-lean.py`: 1 algebraic constraints, 18 bus interactions. -/
def gated : Circuit babyBear where
  algebraicConstraints :=
    [ .mul (.var ⟨"is_valid", some 36⟩) (.add (.var ⟨"is_valid", some 36⟩) (.mul (.const 2013265920) (.const 1))) ]
  busInteractions :=
    [ { busId := 6, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"b__0_0", some 23⟩, .var ⟨"c__0_0", some 27⟩, .var ⟨"a__0_0", some 19⟩, .const 1] }
    , { busId := 6, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"b__1_0", some 24⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"a__1_0", some 20⟩, .const 1] }
    , { busId := 6, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"b__2_0", some 25⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"a__2_0", some 21⟩, .const 1] }
    , { busId := 6, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"b__3_0", some 26⟩, .var ⟨"c__3_0", some 30⟩, .var ⟨"a__3_0", some 22⟩, .const 1] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 36⟩),
        payload := [.const 1, .const 7, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩] }
    , { busId := 1, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.const 1, .const 7, .var ⟨"b__0_0", some 23⟩, .var ⟨"b__1_0", some 24⟩, .var ⟨"b__2_0", some 25⟩, .var ⟨"b__3_0", some 26⟩, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 36⟩),
        payload := [.const 1, .const 5, .var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"c__3_0", some 30⟩, .var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩] }
    , { busId := 1, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.const 1, .const 5, .var ⟨"c__0_0", some 27⟩, .var ⟨"c__1_0", some 28⟩, .var ⟨"c__2_0", some 29⟩, .var ⟨"c__3_0", some 30⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 1)] }
    , { busId := 1, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 36⟩),
        payload := [.const 1, .const 8, .var ⟨"writes_aux__prev_data__0_0", some 15⟩, .var ⟨"writes_aux__prev_data__1_0", some 16⟩, .var ⟨"writes_aux__prev_data__2_0", some 17⟩, .var ⟨"writes_aux__prev_data__3_0", some 18⟩, .var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩] }
    , { busId := 1, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.const 1, .const 8, .var ⟨"a__0_0", some 19⟩, .var ⟨"a__1_0", some 20⟩, .var ⟨"a__2_0", some 21⟩, .var ⟨"a__3_0", some 22⟩, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 2)] }
    , { busId := 0, multiplicity := .mul (.const 2013265920) (.var ⟨"is_valid", some 36⟩),
        payload := [.const 0, .var ⟨"from_state__timestamp_0", some 1⟩] }
    , { busId := 0, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.const 4, .add (.var ⟨"from_state__timestamp_0", some 1⟩) (.const 3)] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩, .const 17] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.add (.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩))) (.const 15360)) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩, .const 17] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"reads_aux__1__base__prev_timestamp_0", some 9⟩)) (.mul (.const 15360) (.var ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_0", some 10⟩))) (.mul (.const 2013265920) (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩))), .const 12] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩, .const 17] }
    , { busId := 3, multiplicity := .var ⟨"is_valid", some 36⟩,
        payload := [.add (.add (.mul (.const 15360) (.var ⟨"writes_aux__base__prev_timestamp_0", some 12⟩)) (.mul (.const 15360) (.var ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩))) (.mul (.const 2013265920) (.add (.mul (.const 15360) (.var ⟨"from_state__timestamp_0", some 1⟩)) (.const 15360))), .const 12] } ]

/-- `gated` with `is_valid` pinned to `1`, closing off the padding row that makes
    `gated_not_hasStepLayout` false. Defined by appending to `gated` rather than restating it. -/
def gatedPinned : Circuit babyBear :=
  { gated with
    algebraicConstraints := gated.algebraicConstraints ++
      [ .add (.var ⟨"is_valid", some 36⟩) (.mul (.const 2013265920) (.const 1)) ] }

end ApcOptimizer.OpenVM.SingleXor
