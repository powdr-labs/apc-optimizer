import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.LoadBranch.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** -/

namespace ApcOptimizer.OpenVM.LoadBranch

/-- The variables the optimized APC's stateful payloads, lt gadgets and outgoing `pc` mention.
    The two `mem_ptr_limbs` are here because the load's *pointer* is computed, not a literal:
    `placeCheckAll` normalizes a whole memory payload, address included. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_1", some 59⟩,
   ⟨"rs1_data__0_0", some 3⟩, ⟨"rs1_data__1_0", some 4⟩,
   ⟨"rs1_data__2_0", some 5⟩, ⟨"rs1_data__3_0", some 6⟩,
   ⟨"rs1_aux_cols__base__prev_timestamp_0", some 7⟩,
   ⟨"rs1_aux_cols__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩,
   ⟨"read_data_aux__base__prev_timestamp_0", some 11⟩,
   ⟨"read_data_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 12⟩,
   ⟨"mem_ptr_limbs__0_0", some 16⟩, ⟨"mem_ptr_limbs__1_0", some 17⟩,
   ⟨"write_base_aux__prev_timestamp_0", some 19⟩,
   ⟨"write_base_aux__timestamp_lt_aux__lower_decomp__0_0", some 20⟩,
   ⟨"read_data__0_0", some 29⟩, ⟨"read_data__1_0", some 30⟩,
   ⟨"read_data__2_0", some 31⟩, ⟨"read_data__3_0", some 32⟩,
   ⟨"prev_data__0_0", some 33⟩, ⟨"prev_data__1_0", some 34⟩,
   ⟨"prev_data__2_0", some 35⟩, ⟨"prev_data__3_0", some 36⟩,
   ⟨"reads_aux__0__base__prev_timestamp_1", some 45⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 46⟩,
   ⟨"a__0_1", some 51⟩, ⟨"a__1_1", some 52⟩, ⟨"a__2_1", some 53⟩, ⟨"a__3_1", some 54⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each interaction is `payloadOk`, position by position. Every send here echoes an earlier
    receive — the block computes nothing it writes — so nothing is left to the caller. The echo at
    `8` crosses address spaces: the word it writes to a register came off the *main memory* read at
    `3`, and `openVmPayloadOk` byte-checks both spaces (`MemoryPayload.isByteChecked`). -/
def witnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .echo 2, .notSend, .notMemory, .notSend, .echo 6, .echo 3,
   .notMemory, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .notSend, .notSend]

end ApcOptimizer.OpenVM.LoadBranch
