import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.HendecagonalDipyramid.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hendecagonal dipyramid: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.HendecagonalDipyramid.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-11/1024, 0, 55/256, 0, -77/64, 0, 11/4, 0, -11/4, 0, 1] θ = 0 ∧
      (0.2817325568414296977114179153466 : ℝ) ≤ θ ∧
      θ ≤ (0.2817325568414296977114179153467 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.DipyramidHendecagonalDipyramidDim.root (a := 0.2817325568414296977114179153466) (b := 0.2817325568414296977114179153467) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.HendecagonalDipyramid.Proof
