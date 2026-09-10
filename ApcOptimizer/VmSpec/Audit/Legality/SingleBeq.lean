import ApcOptimizer.VmSpec.Audit.Apcs.SingleBeq.Opt
import ApcOptimizer.VmSpec.Audit.Legality.Check

set_option autoImplicit false

/-! **`SingleBeq`'s `opt` against `Circuit.legalGuest`**, by one `decide`.

    One instruction, `if [x8] == [x5] jump +2`: two register reads, no write, `d = 2`. The two
    accesses are `0 ↔ 1` (register `x8`) and `2 ↔ 3` (register `x5`), each a `getPrevious` reaching
    back and a `setNew` committing at a fixed tick. -/

namespace ApcOptimizer.OpenVM.SingleBeq

open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.LegalityCheck

/-- The access pairing, as an index list; entries off the memory bus are unused. -/
def optPartnerList : List ℕ := [1, 0, 3, 2, 4, 5, 6, 7, 8, 9]

theorem optLegalityCheck :
    legalityCheckAll layoutVars optPinRules openVmMemBusId openVmTimestampBound 2
      opt.busInteractions recipes optPartnerList = true := by decide

theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 2 < maxWindow) :
    opt.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound :=
  hasStepLayout_of_legalityCheck (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ _ _ i hi _ _ => by fin_cases i <;> exact absurd hi (by decide))
    optLegalityCheck

/-- **A real APC is a legal guest under the order-free definition.** -/
theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 2 < maxWindow)
    (hi : 10 ≤ maxInteractions) :
    opt.legalGuest apcRules openVmMemAddress maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi
  x0Zero := x0Zero_of_legalityCheck (fun _ halg => optPinRules_hold _ halg) optLegalityCheck

end ApcOptimizer.OpenVM.SingleBeq
