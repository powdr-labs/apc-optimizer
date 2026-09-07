import ApcOptimizer.VmSpec.Implementation.OpenVmChain
import ApcOptimizer.VmSpec.OrderFree

set_option autoImplicit false

/-! # `Host.realizes` transports to the order-free rely

    `Host.realizes` never reads `BusSemantics.admissible` — its every field goes through
    `isStateful`, `accepts` and `maintainsInvariants`, which `openVmBusSemanticsOF` shares with
    `openVmBusSemantics` definitionally. So the existing proof carries over field by field, with
    no new content. -/

namespace ApcOptimizer.OpenVM

open ApcOptimizer.OpenVM.OrderFree

variable {p : ℕ}

/-- `openVmHost` realizes the order-free rely, by the same lemmas as `openVmHost_realizes`. -/
theorem openVmHost_realizes (P : OpenVmParams p) (entryPc : Option (ZMod p))
    (hOrd : (openVmHost P).ordersRanks (openVmRankModel openVmMemBusId)
      ((openVmBusSemantics p defaultBusMap).toGuestRules
        (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem) openVmMemAddress) :
    (openVmHost P).realizes
      (openVmBusSemanticsOF p defaultBusMap entryPc) (openVmRankModel openVmMemBusId)
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress where
  hmem := openVmDefaultHmem
  legalGuest := openVmHost_legalGuest_unpack P
  sinksAreTables := openVmHost_sinksAreTables P
  statefulChipsMaintain := ⟨openVmFinalizeIdx P,
    ⟨(openVmHost_finalize_exempt P).bound, (openVmHost_finalize_exempt P).uniform⟩,
    openVmHost_statefulChipsMaintain P⟩
  statefulAcceptsOfPayloadOk :=
    openVmBusSemantics_statefulAcceptsOfPayloadOk
      (openVmGuestRules defaultBusMap openVmMemBusId) openVmDefaultHmem
  absorbsStateless := openVmHost_absorbsStateless P
  ordersRanks := hOrd

end ApcOptimizer.OpenVM
