import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.HeptagonalDipyramid.Proof.FullDim

set_option linter.style.longLine false

/-!
# The heptagonal dipyramid: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.HeptagonalDipyramid.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-7/64, 0, 7/8, 0, -7/4, 0, 1] θ = 0 ∧
      (0.4338837391175581204757683328483 : ℝ) ≤ θ ∧
      θ ≤ (0.4338837391175581204757683328484 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.DipyramidHeptagonalDipyramidDim.root (a := 0.4338837391175581204757683328483) (b := 0.4338837391175581204757683328484) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.HeptagonalDipyramid.Proof
