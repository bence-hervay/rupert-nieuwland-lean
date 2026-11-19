import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.AugmentedPentagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The augmented pentagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.AugmentedPentagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/256, 0, -11/32, 0, 79/16, 0, -9/2, 0, 1] θ = 0 ∧
      (1.6581632974817010965172836954842 : ℝ) ≤ θ ∧
      θ ≤ (1.6581632974817010965172836954843 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonAugmentedPentagonalPrismDim.root (a := 1.6581632974817010965172836954842) (b := 1.6581632974817010965172836954843) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.AugmentedPentagonalPrism.Proof
