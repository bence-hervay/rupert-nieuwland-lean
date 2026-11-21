import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.EnneagonalDipyramid.Proof.FullDim

set_option linter.style.longLine false

/-!
# The enneagonal dipyramid: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.EnneagonalDipyramid.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-3/64, 0, 9/16, 0, -3/2, 0, 1] θ = 0 ∧
      (0.3420201433256687330440996146822 : ℝ) ≤ θ ∧
      θ ≤ (0.3420201433256687330440996146823 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.DipyramidEnneagonalDipyramidDim.root (a := 0.3420201433256687330440996146822) (b := 0.3420201433256687330440996146823) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.EnneagonalDipyramid.Proof
