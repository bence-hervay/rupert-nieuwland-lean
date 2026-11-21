import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.PentagonalDipyramid.Proof.FullDim

set_option linter.style.longLine false

/-!
# The pentagonal dipyramid: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.PentagonalDipyramid.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [5/16, 0, -5/4, 0, 1] θ = 0 ∧
      (0.587785252292473129168705954639 : ℝ) ≤ θ ∧
      θ ≤ (0.5877852522924731291687059546391 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.DipyramidPentagonalDipyramidDim.root (a := 0.587785252292473129168705954639) (b := 0.5877852522924731291687059546391) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.PentagonalDipyramid.Proof
