import ApcOptimizer.Implementation.OptimizerPasses.Encoding

set_option autoImplicit false

/-! # Cloning the dense system — runtime definitions (impl-only)

A structural rebuild of the dense system. Semantically the identity (`Proofs/CloneCS.lean`); it
exists for its allocation behaviour, and it is a *diagnostic*, reached only from
`profile --clone-probe`.

It is deliberately not in `cleanupPasses`. `Circuit.clone` (`Implementation/Optimizer.lean`) is the
same rebuild at the pipeline entry and is worth ~18% there, so the obvious next guess is that the
dense system also decays as passes strip it down — the cleanup loop drops keccak from 28.6k
constraints to 186. Measured, it does not: cloning once per cleanup iteration is a wash on keccak
(1745→1769 ms, of which the clone is 38 ms) and clearly negative on sha256 (18.9→22.1 s, of which
the clone is 0.4 s). The dense system is rebuilt by the passes themselves, so it never decays the
way the parser's output has; and copying costs more than its own traversal, because it invalidates
the `withPtrEq` identity shortcuts the degree guard and passes rely on (`Pass.lean`). Keep the probe
so the question can be re-asked when the pipeline changes. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Rebuild a dense expression node by node, so the result is freshly allocated. -/
def DenseExpr.clone : DenseExpr p → DenseExpr p
  | .const c => .const c
  | .var i => .var i
  | .add a b => .add a.clone b.clone
  | .mul a b => .mul a.clone b.clone

def DenseConstraintSystem.clone (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  { algebraicConstraints := d.algebraicConstraints.map (fun e => e.clone),
    busInteractions := d.busInteractions.map (fun bi =>
      { bi with multiplicity := bi.multiplicity.clone,
                payload := bi.payload.map (fun e => e.clone) }) }

end ApcOptimizer.Dense
