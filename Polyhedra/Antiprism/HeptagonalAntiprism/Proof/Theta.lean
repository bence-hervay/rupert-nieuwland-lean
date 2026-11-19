import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.HeptagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The heptagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.HeptagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/8, -1/2, 1/4, 3/2, -1, -1, 1] θ = 0 ∧
      (0.8937023058307203190453368994365 : ℝ) ≤ θ ∧
      θ ≤ (0.8937023058307203190453368994366 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismHeptagonalAntiprismDim.root (a := 0.8937023058307203190453368994365) (b := 0.8937023058307203190453368994366) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.HeptagonalAntiprism.Proof
