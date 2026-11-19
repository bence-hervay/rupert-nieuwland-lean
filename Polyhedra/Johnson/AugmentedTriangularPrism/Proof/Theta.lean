import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.AugmentedTriangularPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The augmented triangular prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.AugmentedTriangularPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/36, 0, -5/3, 0, 1] θ = 0 ∧
      (1.2844570503761732889099931426068 : ℝ) ≤ θ ∧
      θ ≤ (1.2844570503761732889099931426069 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonAugmentedTriangularPrismDim.root (a := 1.2844570503761732889099931426068) (b := 1.2844570503761732889099931426069) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.AugmentedTriangularPrism.Proof
