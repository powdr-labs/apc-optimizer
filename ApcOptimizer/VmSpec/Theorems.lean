import ApcOptimizer.VmSpec.Implementation.MemChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

open ApcOptimizer.OpenVM.OrderFree

/-! Our main theorems.

    ## Flaws

    We assume legality for inputs `G` **and** outputs `G'`. So, we must believe that:

    * OpenVM's instruction chips are legal: unproved.
      * Best evidence: `Audit/Legality/All.lean` checks six real *fused* APCs.
    * legality is closed under concatenation: proved.
      * `Circuit.legalGuest_fuse`, at a doubled `maxWindow`
    * the optimizer preserves legality: unproved.

    We should prove the last one.


    We also work against `openVmBusSemanticsOF`, whose `admissible` is order-free. The optimizer's
    current proof is against `openVmBusSemantics`.

    -/

variable {p : ℕ}
variable [Fact p.Prime]
variable {P : OpenVmParams p}

/-- **Substitution soundness, for OpenVM.** -/
theorem openVm_vmSoundReplacement {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemanticsOF p defaultBusMap none)) G G') :
    VmSoundReplacement (openVmHost P) G G' :=
  vmSoundReplacement_of_forall₂
    (openVmHost_realizes P none
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    hLegal hSound

/-- **Substitution completeness, for OpenVM.** -/
theorem openVm_vmCompleteReplacement {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hComplete : List.Forall₂ (fun c c' => (∀ v ∈ Circuit.vars c, v.powdrId?.isSome) ∧
      ∃ ds : Derivations p, Circuit.isCompleteReplacementOf c' c
        (openVmBusSemanticsOF p defaultBusMap none) ds) G G') :
    VmCompleteReplacement (openVmHost P) G G' :=
  vmCompleteReplacement_of_forall₂
    (openVmHost_realizes P none
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    (openVmHost_forcesAdmissible P) hLegal hComplete

/-- **Substitution equivalence, for OpenVM**: the two directions together. -/
theorem openVm_vmEquivalent {G G' : Guest p}
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) openVmMemAddress
        P.maxWindow openVmTimestampBound P.maxInteractions)
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemanticsOF p defaultBusMap none)) G G')
    (hComplete : List.Forall₂ (fun c c' => (∀ v ∈ Circuit.vars c, v.powdrId?.isSome) ∧
      ∃ ds : Derivations p, Circuit.isCompleteReplacementOf c' c
        (openVmBusSemanticsOF p defaultBusMap none) ds) G G') :
    VmEquivalent (openVmHost P) G G' :=
  ⟨openVm_vmSoundReplacement hLegal hSound, openVm_vmCompleteReplacement hLegal hComplete⟩

end ApcOptimizer.OpenVM
