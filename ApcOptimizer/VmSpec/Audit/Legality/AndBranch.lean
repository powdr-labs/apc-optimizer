import ApcOptimizer.VmSpec.Audit.Apcs.AndBranch.Opt
import ApcOptimizer.VmSpec.Audit.Legality.Check

set_option autoImplicit false

/-! **`AndBranch`'s `opt` against `Circuit.legalGuest`**, by one `decide`.

    A fused two-instruction block, `d = 5`, from the shipped benchmark corpus. Three accesses:
    `1 ↔ 2`, `3 ↔ 5` and `6 ↔ 7`. -/

namespace ApcOptimizer.OpenVM.AndBranch

open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.LegalityCheck

def optPartnerList : List ℕ := [0, 2, 1, 5, 4, 3, 7, 6, 8, 9, 10, 11, 12, 13, 14]

theorem optLegalityCheck :
    legalityCheckAll layoutVars optPinRules openVmMemBusId openVmTimestampBound 5
      opt.busInteractions recipes optPartnerList = true := by decide

theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 5 < maxWindow) :
    opt.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound :=
  hasStepLayout_of_legalityCheck (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ _ hacc i hwit _ _ => optWriteOk hacc i hwit)
    optLegalityCheck

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 5 < maxWindow)
    (hi : 15 ≤ maxInteractions) :
    opt.legalGuest apcRules openVmMemAddress maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi
  x0Zero := x0Zero_of_legalityCheck (fun _ halg => optPinRules_hold _ halg) optLegalityCheck

end ApcOptimizer.OpenVM.AndBranch
