import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The augmented tridiminished icosahedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.AugmentedTridiminishedIcosahedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-31/144, 19/18, -1/18, -2, 1] θ = 0 ∧
      (1.7167605132909615817369541309803 : ℝ) ≤ θ ∧
      θ ≤ (1.7167605132909615817369541309804 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonAugmentedTridiminishedIcosahedronDim.root (a := 1.7167605132909615817369541309803) (b := 1.7167605132909615817369541309804) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.AugmentedTridiminishedIcosahedron.Proof
