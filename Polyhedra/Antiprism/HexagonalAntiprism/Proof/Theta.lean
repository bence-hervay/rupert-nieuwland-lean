import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.HexagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hexagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.HexagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/8, 0, 1/2, 0, 1] θ = 0 ∧
      (0.4277998385836760964846178831055 : ℝ) ≤ θ ∧
      θ ≤ (0.4277998385836760964846178831056 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismHexagonalAntiprismDim.root (a := 0.4277998385836760964846178831055) (b := 0.4277998385836760964846178831056) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.HexagonalAntiprism.Proof
