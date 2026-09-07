import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.AndBranch.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** -/

namespace ApcOptimizer.OpenVM.AndBranch

/-- The variables the optimized APC's stateful payloads, lt gadgets and outgoing `pc` mention. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_1", some 54⟩, ⟨"a__0_0", some 19⟩,
   ⟨"b__0_0", some 23⟩, ⟨"b__1_0", some 24⟩, ⟨"b__2_0", some 25⟩, ⟨"b__3_0", some 26⟩,
   ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩,
   ⟨"writes_aux__prev_data__0_0", some 15⟩, ⟨"writes_aux__prev_data__1_0", some 16⟩,
   ⟨"writes_aux__prev_data__2_0", some 17⟩, ⟨"writes_aux__prev_data__3_0", some 18⟩,
   ⟨"writes_aux__base__prev_timestamp_0", some 12⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩,
   ⟨"reads_aux__1__base__prev_timestamp_1", some 43⟩,
   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_1", some 44⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each interaction is `payloadOk`, position by position: the three memory receives and the
    bridge receive are not sends; the register echo at `2` repeats the read at `1`; the dummy
    write at `7` is all zeros; the two bridge interactions are not on the memory bus; the six
    lookups are not stateful. What is left is the masked write at `5`, whose limb the circuit
    computes — `optWriteOk`. -/
def witnesses : List ByteWitness :=
  [.notSend, .notSend, .echo 1, .notSend, .notMemory, .external, .notSend, .limbs, .notMemory,
   .notSend, .notSend, .notSend, .notSend, .notSend, .notSend]

end ApcOptimizer.OpenVM.AndBranch
