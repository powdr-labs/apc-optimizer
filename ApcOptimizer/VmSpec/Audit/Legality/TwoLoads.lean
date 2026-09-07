import ApcOptimizer.VmSpec.Audit.Apcs.TwoLoads.Opt
import ApcOptimizer.VmSpec.Audit.Legality.Check

set_option autoImplicit false

/-! **`TwoLoads`'s `opt` against `Circuit.legalGuest`**, by one `decide`.

    The APC whose two main-memory accesses may alias: `d = 8`, thirty interactions, six access
    pairs `0 ↔ 1`, `2 ↔ 3`, `4 ↔ 11`, `6 ↔ 7`, `8 ↔ 9`, `10 ↔ 12`. Two of them address *computed*
    pointers, so `sameAddr` cannot fold them to constants and compares linear forms instead — the
    reason the pairing check normalizes rather than evaluates. -/

namespace ApcOptimizer.OpenVM.TwoLoads

open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.LegalityCheck

def optPartnerList : List ℕ :=
  [1, 0, 3, 2, 11, 5, 7, 6, 9, 8, 12, 4, 10, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

theorem optLegalityCheck :
    legalityCheckAll layoutVars optPinRules openVmMemBusId openVmTimestampBound 8
      opt.busInteractions recipes optPartnerList = true := by decide

theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 8 < maxWindow) :
    opt.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound :=
  hasStepLayout_of_legalityCheck (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ halg _ i hwit _ hlow => optWriteOk halg i hwit hlow)
    optLegalityCheck

theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 8 < maxWindow)
    (hi : 30 ≤ maxInteractions) :
    opt.legalGuest apcRules openVmMemAddress maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi
  x0Zero := x0Zero_of_legalityCheck (fun _ halg => optPinRules_hold _ halg) optLegalityCheck

end ApcOptimizer.OpenVM.TwoLoads
