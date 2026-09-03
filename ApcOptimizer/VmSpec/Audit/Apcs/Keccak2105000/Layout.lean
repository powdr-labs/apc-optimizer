import ApcOptimizer.VmSpec.Audit.Apcs.Common
import ApcOptimizer.VmSpec.Audit.Apcs.Keccak2105000.Stages

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! **Where this APC's step puts its stateful traffic.** Stage `039` and the pinned stage `040`
    have the same bus interactions in the same order -- `040` only scales each multiplicity by
    `is_valid` -- so they place them identically, and `Opt.lean` and `GatedPinned.lean` share
    everything here. -/

namespace ApcOptimizer.OpenVM.Keccak2105000

/-- The variables the optimized APC's stateful payloads and lt gadgets mention: the step's base,
    the branch flag the outgoing `pc` depends on, each gadget's `prev_timestamp` and low
    decomposition limb, and every memory payload's data limbs -- `placeCheckAll` normalizes a
    *receive*'s payload too, which the byte check never had to. -/
def layoutVars : List Variable :=
  [⟨"from_state__timestamp_0", some 1⟩, ⟨"cmp_result_3", some 126⟩,
   ⟨"reads_aux__0__base__prev_timestamp_0", some 6⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0", some 7⟩,
   ⟨"writes_aux__base__prev_timestamp_0", some 12⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_0", some 13⟩,
   ⟨"reads_aux__0__base__prev_timestamp_1", some 42⟩,
   ⟨"reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1", some 43⟩,
   ⟨"writes_aux__base__prev_timestamp_1", some 48⟩,
   ⟨"writes_aux__base__timestamp_lt_aux__lower_decomp__0_1", some 49⟩,
   ⟨"reads_aux__1__base__prev_timestamp_3", some 115⟩,
   ⟨"reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_3", some 116⟩,
   ⟨"writes_aux__prev_data__0_0", some 15⟩, ⟨"writes_aux__prev_data__1_0", some 16⟩,
   ⟨"writes_aux__prev_data__2_0", some 17⟩, ⟨"writes_aux__prev_data__3_0", some 18⟩,
   ⟨"writes_aux__prev_data__0_1", some 51⟩, ⟨"writes_aux__prev_data__1_1", some 52⟩,
   ⟨"writes_aux__prev_data__2_1", some 53⟩, ⟨"writes_aux__prev_data__3_1", some 54⟩,
   ⟨"a__0_0", some 19⟩, ⟨"a__1_0", some 20⟩, ⟨"a__2_0", some 21⟩, ⟨"a__3_0", some 22⟩,
   ⟨"a__0_1", some 55⟩, ⟨"a__1_1", some 56⟩, ⟨"a__2_1", some 57⟩, ⟨"a__3_1", some 58⟩,
   ⟨"a__0_2", some 91⟩]

/-- The step's base, as an expression and as a normal form. -/
def baseE : Expression babyBear := .var ⟨"from_state__timestamp_0", some 1⟩

def baseF : LinForm babyBear := LinForm.varF layoutVars ⟨"from_state__timestamp_0", some 1⟩

/-- Why each of `opt`'s interactions is `payloadOk`, position by position: six memory
    receives and the bridge receive are not sends; three memory sends echo the read that preceded
    them; one writes literal zeros; the bridge send is not on the memory bus; ten lookups are not
    stateful. Only the masked write at position `9` is left to the caller — it is a byte because
    the bitwise table says so, which is where a decidable check stops. -/
def witnesses : List ByteWitness :=
  [.notSend, .echo 0, .notSend, .notSend, .notSend, .notSend, .echo 4, .notSend,
   .echo 0, .external, .notSend, .limbs, .notMemory] ++ List.replicate 10 .notSend

end ApcOptimizer.OpenVM.Keccak2105000
