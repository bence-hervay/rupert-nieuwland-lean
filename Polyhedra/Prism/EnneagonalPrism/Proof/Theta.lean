import Modules.Check.Number.ThetaRoot
import Polyhedra.Prism.EnneagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The enneagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Prism.EnneagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/3, 0, 2, 0, -3, 0, 1] θ = 0 ∧
      (1.4619022000815436261163772066831 : ℝ) ≤ θ ∧
      θ ≤ (1.4619022000815436261163772066832 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismEnneagonalPrismDim.root (a := 1.4619022000815436261163772066831) (b := 1.4619022000815436261163772066832) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Prism.EnneagonalPrism.Proof
