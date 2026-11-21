import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.DecagonalDipyramid.Proof.FullDim

set_option linter.style.longLine false

/-!
# The decagonal dipyramid: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.DecagonalDipyramid.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/20, 1/2, -3/2, 1, 1] θ = 0 ∧
      (0.4094227023180610640371922534991 : ℝ) ≤ θ ∧
      θ ≤ (0.4094227023180610640371922534992 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.DipyramidDecagonalDipyramidDim.root (a := 0.4094227023180610640371922534991) (b := 0.4094227023180610640371922534992) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.DecagonalDipyramid.Proof
