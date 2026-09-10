import ApcOptimizer.VmSpec.Audit.Apcs.LoadBranch.Opt
import ApcOptimizer.VmSpec.Audit.Legality.Check

set_option autoImplicit false

/-! **`LoadBranch`'s `opt` against `Circuit.legalGuest`**, by one `decide`.

    A fused two-instruction block, `d = 5`, from the shipped benchmark corpus. Four accesses:
    `0 ↔ 1`, `2 ↔ 3`, `4 ↔ 8` and `6 ↔ 7`. The `4 ↔ 8` pair is the interesting one — a write whose
    old record is received early and whose new one commits late. -/

namespace ApcOptimizer.OpenVM.LoadBranch

open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.LegalityCheck

def optPartnerList : List ℕ :=
  [1, 0, 3, 2, 8, 5, 7, 6, 4, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

theorem optLegalityCheck :
    legalityCheckAll layoutVars optPinRules openVmMemBusId openVmTimestampBound 5
      opt.busInteractions recipes optPartnerList = true := by decide

theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 5 < maxWindow) :
    opt.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound :=
  hasStepLayout_of_legalityCheck (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ _ _ i hi _ _ => by fin_cases i <;> exact absurd hi (by decide))
    optLegalityCheck

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 5 < maxWindow)
    (hi : 20 ≤ maxInteractions) :
    opt.legalGuest apcRules openVmMemAddress maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi
  x0Zero := x0Zero_of_legalityCheck (fun _ halg => optPinRules_hold _ halg) optLegalityCheck

end ApcOptimizer.OpenVM.LoadBranch
