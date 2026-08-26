-- Root of the `ApcOptimizer` library.
import ApcOptimizer.Optimizer
import ApcOptimizer.Sp1Semantics
import ApcOptimizer.Implementation.JsonParser
import ApcOptimizer.Utils.Dsl
import ApcOptimizer.Utils.Size

-- `VmSpec` (a separate, still-WIP VM-level audit -- see `ApcOptimizer/VmSpec.lean`) is deliberately
-- not imported here: `ApcOptimizer/VmSpec/Audit/RealApcLegality.lean` alone takes ~5 minutes to
-- compile (large `decide`/`simp` checks against real, non-trivial circuit dumps), and nothing in
-- the audited optimizer pipeline (`Optimizer.lean`, `Main.lean`) depends on it. Lake's default
-- build target for this library is exactly the import closure of this file (`Glob.one`, not a
-- directory sweep), so omitting the import keeps `lake build`/CI fast without disabling `VmSpec`:
-- build it explicitly with `lake build ApcOptimizer.VmSpec`.
