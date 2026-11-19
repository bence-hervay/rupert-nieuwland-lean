import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Proof.FullDim

set_option linter.style.longLine false

/-!
# The gyroelongated square dipyramid: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.GyroelongatedSquareDipyramid.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/32, 0, 0, 0, 1] θ = 0 ∧
      (0.4204482076268572715155627381166 : ℝ) ≤ θ ∧
      θ ≤ (0.4204482076268572715155627381167 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonGyroelongatedSquareDipyramidDim.root (a := 0.4204482076268572715155627381166) (b := 0.4204482076268572715155627381167) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.GyroelongatedSquareDipyramid.Proof
