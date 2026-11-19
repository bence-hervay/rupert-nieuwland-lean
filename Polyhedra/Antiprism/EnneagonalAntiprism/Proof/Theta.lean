import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.EnneagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The enneagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.EnneagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/9, 0, -8, 0, 26, 0, -14, 0, 5, 0, -6, 0, 1] θ = 0 ∧
      (2.3234282873061610765105970184552 : ℝ) ≤ θ ∧
      θ ≤ (2.3234282873061610765105970184553 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismEnneagonalAntiprismDim.root (a := 2.3234282873061610765105970184552) (b := 2.3234282873061610765105970184553) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.EnneagonalAntiprism.Proof
