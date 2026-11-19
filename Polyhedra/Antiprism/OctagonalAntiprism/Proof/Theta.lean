import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.OctagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The octagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.OctagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [79/512, 7/16, -69/16, 3, 13/2, -4, -3, 0, 1] θ = 0 ∧
      (1.7367107498078623110777935614292 : ℝ) ≤ θ ∧
      θ ≤ (1.7367107498078623110777935614293 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismOctagonalAntiprismDim.root (a := 1.7367107498078623110777935614292) (b := 1.7367107498078623110777935614293) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.OctagonalAntiprism.Proof
