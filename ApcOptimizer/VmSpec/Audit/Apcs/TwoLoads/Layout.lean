import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.TwoLoads.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** -/

namespace ApcOptimizer.OpenVM.TwoLoads

/-- The variables the optimized APC's stateful payloads, lt gadgets and outgoing `pc` mention.
    The four `flags__*` of each load are here because a byte load's *pointer* is a quadratic
    function of them: `placeCheckAll` normalizes a whole memory payload, address included. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_2", some 100⟩,
   ⟨"rs1_data__0_0", some 3⟩, ⟨"rs1_data__1_0", some 4⟩,
   ⟨"rs1_data__2_0", some 5⟩, ⟨"rs1_data__3_0", some 6⟩,
   ⟨"rs1_aux_cols__base__prev_timestamp_0", some 7⟩,
   ⟨"rs1_aux_cols__base__timestamp_lt_aux__lower_decomp__0_0", some 8⟩,
   ⟨"flags__0_0", some 23⟩, ⟨"flags__1_0", some 24⟩,
   ⟨"flags__2_0", some 25⟩, ⟨"flags__3_0", some 26⟩,
   ⟨"mem_ptr_limbs__0_0", some 16⟩, ⟨"mem_ptr_limbs__1_0", some 17⟩,
   ⟨"read_data__0_0", some 29⟩, ⟨"read_data__1_0", some 30⟩,
   ⟨"read_data__2_0", some 31⟩, ⟨"read_data__3_0", some 32⟩,
   ⟨"read_data_aux__base__prev_timestamp_0", some 11⟩,
   ⟨"read_data_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 12⟩,
   ⟨"prev_data__0_0", some 33⟩, ⟨"prev_data__1_0", some 34⟩,
   ⟨"prev_data__2_0", some 35⟩, ⟨"prev_data__3_0", some 36⟩,
   ⟨"write_base_aux__prev_timestamp_0", some 19⟩,
   ⟨"write_base_aux__timestamp_lt_aux__lower_decomp__0_0", some 20⟩,
   ⟨"write_data__0_0", some 37⟩,
   ⟨"rs1_data__0_1", some 44⟩, ⟨"rs1_data__1_1", some 45⟩,
   ⟨"rs1_data__2_1", some 46⟩, ⟨"rs1_data__3_1", some 47⟩,
   ⟨"rs1_aux_cols__base__prev_timestamp_1", some 48⟩,
   ⟨"rs1_aux_cols__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩,
   ⟨"flags__0_1", some 64⟩, ⟨"flags__1_1", some 65⟩,
   ⟨"flags__2_1", some 66⟩, ⟨"flags__3_1", some 67⟩,
   ⟨"mem_ptr_limbs__0_1", some 57⟩, ⟨"mem_ptr_limbs__1_1", some 58⟩,
   ⟨"read_data__0_1", some 70⟩, ⟨"read_data__1_1", some 71⟩,
   ⟨"read_data__2_1", some 72⟩, ⟨"read_data__3_1", some 73⟩,
   ⟨"read_data_aux__base__prev_timestamp_1", some 52⟩,
   ⟨"read_data_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 53⟩,
   ⟨"prev_data__0_1", some 74⟩, ⟨"prev_data__1_1", some 75⟩,
   ⟨"prev_data__2_1", some 76⟩, ⟨"prev_data__3_1", some 77⟩,
   ⟨"write_base_aux__prev_timestamp_1", some 60⟩,
   ⟨"write_base_aux__timestamp_lt_aux__lower_decomp__0_1", some 61⟩,
   ⟨"write_data__0_1", some 78⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each interaction is `payloadOk`, position by position. The six memory receives are not
    sends; the two bridge interactions are not on the memory bus; the sixteen lookups are not
    stateful. Of the six memory sends, four echo the receive they came from — the register
    read-backs at `1`/`7` and the main-memory echoes at `3`/`9`. What is left is the pair of
    register writes at `11`/`12`: a *byte* load writes one limb the circuit selects, so its
    byte-ness is `optWriteOk`, not a shape. -/
def witnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .echo 2, .notSend, .notMemory, .notSend, .echo 6, .notSend,
   .echo 8, .notSend, .external, .external, .notMemory,
   .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend,
   .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend, .notSend]

end ApcOptimizer.OpenVM.TwoLoads
