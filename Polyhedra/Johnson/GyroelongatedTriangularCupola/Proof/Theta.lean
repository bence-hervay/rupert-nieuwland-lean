import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.GyroelongatedTriangularCupola.Proof.FullDim

set_option linter.style.longLine false

/-!
# The gyroelongated triangular cupola: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.GyroelongatedTriangularCupola.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-54767/20736, 631/36, -1181/48, -38/3, -5/72, -4, 1, 0, 1] θ = 0 ∧
      (1.9607713926898911079562381813641 : ℝ) ≤ θ ∧
      θ ≤ (1.9607713926898911079562381813642 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonGyroelongatedTriangularCupolaDim.root (a := 1.9607713926898911079562381813641) (b := 1.9607713926898911079562381813642) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.GyroelongatedTriangularCupola.Proof
