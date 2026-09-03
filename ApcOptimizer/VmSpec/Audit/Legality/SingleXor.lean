import ApcOptimizer.VmSpec.Audit.Apcs.SingleXor.Opt
import ApcOptimizer.VmSpec.Audit.Legality.Check

set_option autoImplicit false

/-! **`SingleXor`'s `opt` against `Circuit.legalGuest`**, by one `decide`.

    One instruction, `[x8] = [x7] ^ [x5]`, `d = 3`. Three accesses — two reads and, unlike
    `SingleBeq`, a **write**, which is §4.6.1's other shape: `4 ↔ 5` reads `x7`, `6 ↔ 7` reads `x5`,
    and `8 ↔ 9` receives `x8`'s previous record and sends the computed value back. Its three ticks
    `0, 1, 2` are distinct and fill `[0, d)` exactly. -/

namespace ApcOptimizer.OpenVM.SingleXor

open ApcOptimizer.OpenVM ApcOptimizer.OpenVM.LegalityCheck

def optPartnerList : List ℕ :=
  [0, 1, 2, 3, 5, 4, 7, 6, 9, 8, 10, 11, 12, 13, 14, 15, 16, 17]

theorem optLegalityCheck :
    legalityCheckAll layoutVars optPinRules openVmMemBusId openVmTimestampBound 3
      opt.busInteractions recipes optPartnerList = true := by decide

theorem opt_hasStepLayout {maxWindow : ℕ} (hw : 3 < maxWindow) :
    opt.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound :=
  hasStepLayout_of_legalityCheck (by norm_num) hw (fun _ halg => optPinRules_hold _ halg) optBaseLin
    (fun asg halg => bridgeCheck_sound optBridgeCheck (optPinRules_hold asg halg))
    optPlaceCheck optOrderCheck optFitsCheck optByteCheck
    (fun _ halg hacc => optLookbacks halg hacc)
    (fun _ _ hacc i hwit _ _ => optWriteOk hacc i hwit)
    optLegalityCheck

/-- **A second real APC — this one with a memory write — is legal under the order-free
    definition.** -/
theorem opt_legalGuest {maxWindow maxInteractions : ℕ} (hw : 3 < maxWindow)
    (hi : 18 ≤ maxInteractions) :
    opt.legalGuest apcRules openVmMemAddress maxWindow openVmTimestampBound maxInteractions where
  sendOnly := opt_legalMultiplicities.1
  polarity := opt_legalMultiplicities.2
  stepLayout := opt_hasStepLayout hw
  size := by simpa [opt] using hi
  x0Zero := x0Zero_of_legalityCheck (fun _ halg => optPinRules_hold _ halg) optLegalityCheck

end ApcOptimizer.OpenVM.SingleXor
