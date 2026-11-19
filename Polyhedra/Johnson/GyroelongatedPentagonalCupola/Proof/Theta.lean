import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.GyroelongatedPentagonalCupola.Proof.FullDim

set_option linter.style.longLine false

/-!
# The gyroelongated pentagonal cupola: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.GyroelongatedPentagonalCupola.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/1600, 1/20, 31/80, 1/4, -49/40, -3/2, 3/2, 0, 1] θ = 0 ∧
      (0.6940640579892960447363608848778 : ℝ) ≤ θ ∧
      θ ≤ (0.6940640579892960447363608848779 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonGyroelongatedPentagonalCupolaDim.root (a := 0.6940640579892960447363608848778) (b := 0.6940640579892960447363608848779) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.GyroelongatedPentagonalCupola.Proof
