import ApcOptimizer.VmSpec.Audit.AdmissibleGap
import ApcOptimizer.VmSpec.Audit.BridgeCheck
import ApcOptimizer.VmSpec.Audit.BridgeOffsetGap
import ApcOptimizer.VmSpec.Audit.ByteCheck
import ApcOptimizer.VmSpec.Audit.InputTimeGap
import ApcOptimizer.VmSpec.Audit.LinForm
import ApcOptimizer.VmSpec.Audit.OpenVmShapes
import ApcOptimizer.VmSpec.Audit.PlaceCheck
import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity

/-! The part of `VmSpec/Audit/` that CI builds: the gap witnesses and the decidable checkers,
    everything except `Audit/Apcs/` and the `Audit/Legality/` results that rest on it. Those
    check the checkers against real circuit dumps and take ~10 minutes; build them explicitly
    with `lake build ApcOptimizer.VmSpec.Audit.Legality.All`. -/
