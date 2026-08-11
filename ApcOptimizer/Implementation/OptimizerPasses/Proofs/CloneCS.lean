import ApcOptimizer.Implementation.OptimizerPasses.CloneCS
import ApcOptimizer.Implementation.OptimizerPasses.Pass

set_option autoImplicit false

/-! # Cloning the dense system — the identity, and the pass that does it

`DenseConstraintSystem.clone` is the identity, so the pass wrapping it is `DenseVerifiedPassW.id`
with a different allocation behaviour (see `CloneCS.lean` for why that is worth a pass). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

theorem DenseExpr.clone_eq (e : DenseExpr p) : e.clone = e := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [DenseExpr.clone, iha, ihb]
  | mul a b iha ihb => simp [DenseExpr.clone, iha, ihb]

theorem DenseConstraintSystem.clone_eq (d : DenseConstraintSystem p) : d.clone = d := by
  simp [DenseConstraintSystem.clone, DenseExpr.clone_eq]

/-- Rebuild the dense system, changing nothing but where its nodes live. -/
def denseClonePass : DenseVerifiedPassW p :=
  fun reg d hcov bs _ =>
    { reg' := reg, out := d.clone, derivs := [], ext := VarRegistry.Extends.refl reg,
      covered := by rw [DenseConstraintSystem.clone_eq]; exact hcov,
      dcovered := by intro x hx; simp at hx,
      correct := by
        rw [DenseConstraintSystem.clone_eq]
        exact PassCorrect.refl (reg.decodeCS d) bs }

end ApcOptimizer.Dense
