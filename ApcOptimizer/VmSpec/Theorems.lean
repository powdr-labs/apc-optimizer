import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- **Substitution soundness, for OpenVM.** Assumes `hLegal` (every chip of `G ++ G'` — input and
    output — is legal for the VM `P` configures) and `hSound` (each per-chip replacement is
    sound). -/
theorem openVm_vmSoundReplacement [Fact p.Prime] {P : OpenVmParams p} {G G' : Guest p}
    -- TODO(AO): `G'`'s legality isn't derivable from `G`'s via `isSoundReplacementOf` yet.
    (hLegal : ∀ c ∈ G ++ G',
      c.legalGuest (openVmGuestRules defaultBusMap openVmMemBusId) P.maxWindow
        openVmTimestampBound P.maxInteractions)
    -- NB: legality carries the size bounds `isSoundReplacementOf` itself doesn't depend on.
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c
      (openVmBusSemantics p defaultBusMap)) G G') :
    VmSoundReplacement (openVmHost P) G G' :=
  vmSoundReplacement_of_forall₂
    (openVmHost_realizes P
      (openVmGuestRules_eq defaultBusMap openVmMemBusId ▸ openVmHost_ordersRanks P))
    hLegal hSound

end ApcOptimizer.OpenVM
