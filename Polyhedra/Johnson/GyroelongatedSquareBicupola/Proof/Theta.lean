import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.GyroelongatedSquareBicupola.Proof.FullDim

set_option linter.style.longLine false

/-!
# The gyroelongated square bicupola: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.GyroelongatedSquareBicupola.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-17/1024, -1/16, 13/32, 3/4, -19/16, -1, 0, 0, 1] θ = 0 ∧
      (0.7007458350045842754210119906852 : ℝ) ≤ θ ∧
      θ ≤ (0.7007458350045842754210119906853 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonGyroelongatedSquareBicupolaDim.root (a := 0.7007458350045842754210119906852) (b := 0.7007458350045842754210119906853) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.GyroelongatedSquareBicupola.Proof
