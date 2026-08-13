import ApcOptimizer.Implementation.Optimizer
import ApcOptimizer.Implementation.OpenVmFacts
import ApcOptimizer.Implementation.Sp1Facts

set_option autoImplicit false

/-! # The optimizers and their correctness (audited) -/

variable {p : ℕ}

/-! ## The optimizers

    Three optimizers are available, each taking the zkVM's degree bound `b` as a parameter:
    - `optimizerWithBusFacts b facts`: This is the most general optimizer. It consumes a `BusFacts`
      instance with *proven* properties of the bus semantics.
    - `simpleOptimizer bs b`: A specialization with `BusFacts.trivial bs` (no bus knowledge). This is
      the optimizer for a new VM with no proven bus facts. It will likely be less effective than the
      fact-aware optimizer.
    - `openVmOptimizer busMap`: A specialization for the OpenVM semantics (degree bound defaulting to
      `OpenVM.defaultDegreeBound`). -/

/-- Optimizer which does not use any bus facts. Works with any VM, but is less effective. Returns
    the optimized system together with the `Derivations` for its newly-introduced columns. -/
def simpleOptimizer (bs : BusSemantics p) [DecidablePred bs.accepts] (b : DegreeBound) :
    Optimizer p :=
  optimizerWithBusFacts b (BusFacts.trivial bs)

namespace ApcOptimizer.OpenVM

/-- Optimizer specialized for the OpenVM semantics. `entryPc` is the block's entry pc when the
    caller knows it (powdr's `block.blocks[0].start_pc`), which declares the execution bridge's
    entry record (ENTRY_KEY, see `memEntryKeyOf`); `none` assumes nothing. -/
def openVmOptimizer (busMap : BusMap := defaultBusMap)
    (entryPc : Option (ZMod babyBear) := none) (b : DegreeBound := defaultDegreeBound) :
    Optimizer babyBear :=
  optimizerWithBusFacts b (openVmFacts babyBear busMap entryPc)

end ApcOptimizer.OpenVM

namespace ApcOptimizer.SP1

/-- Optimizer specialized for the SP1 semantics. `entryPc` is the block's entry pc when the
    caller knows it (powdr's `block.blocks[0].start_pc`), which declares the execution bridge's
    entry record (ENTRY_KEY, see `memEntryKeyOf`); `none` assumes nothing. -/
def sp1Optimizer (busMap : BusMap := defaultBusMap) (entryPc : Option Nat := none)
    (b : DegreeBound := defaultDegreeBound) :
    Optimizer koalaBear :=
  optimizerWithBusFacts b (sp1Facts koalaBear busMap entryPc)

end ApcOptimizer.SP1

/-! ## Correctness

    In the following theorems, we establish that the optimizers maintain correctness. -/

theorem optimizerWithBusFacts_maintainsCorrectness (bs : BusSemantics p) (b : DegreeBound)
    (facts : BusFacts p bs) :
    Optimizer.isCorrect (optimizerWithBusFacts b facts) bs b :=
  ⟨fun cs => optimizerWithBusFacts_correct b facts cs,
   fun cs => optimizerWithBusFacts_respectsDegree b facts cs⟩

theorem simpleOptimizer_maintainsCorrectness (bs : BusSemantics p) [DecidablePred bs.accepts]
    (b : DegreeBound) :
    Optimizer.isCorrect (simpleOptimizer bs b) bs b :=
  optimizerWithBusFacts_maintainsCorrectness bs b (BusFacts.trivial bs)

namespace ApcOptimizer.OpenVM

theorem openVmOptimizer_maintainsCorrectness (busMap : BusMap)
    (entryPc : Option (ZMod babyBear)) (b : DegreeBound) :
    Optimizer.isCorrect (openVmOptimizer busMap entryPc b)
      (openVmBusSemantics babyBear busMap entryPc) b :=
  optimizerWithBusFacts_maintainsCorrectness (openVmBusSemantics babyBear busMap entryPc) b
    (openVmFacts babyBear busMap entryPc)

end ApcOptimizer.OpenVM

namespace ApcOptimizer.SP1

theorem sp1Optimizer_maintainsCorrectness (busMap : BusMap) (entryPc : Option Nat)
    (b : DegreeBound) :
    Optimizer.isCorrect (sp1Optimizer busMap entryPc b)
      (sp1BusSemantics koalaBear busMap entryPc) b :=
  optimizerWithBusFacts_maintainsCorrectness (sp1BusSemantics koalaBear busMap entryPc) b
    (sp1Facts koalaBear busMap entryPc)

end ApcOptimizer.SP1
