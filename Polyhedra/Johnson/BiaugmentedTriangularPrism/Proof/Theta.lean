import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The biaugmented triangular prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.BiaugmentedTriangularPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/256, 0, -5/8, 0, 1] θ = 0 ∧
      (0.7865660924854930855822837664288 : ℝ) ≤ θ ∧
      θ ≤ (0.7865660924854930855822837664289 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonBiaugmentedTriangularPrismDim.root (a := 0.7865660924854930855822837664288) (b := 0.7865660924854930855822837664289) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.BiaugmentedTriangularPrism.Proof
