import Modules.Check.Number.ThetaRoot
import Polyhedra.Prism.DecagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The decagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Prism.DecagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/16, 2, -9/4, -2, 1] θ = 0 ∧
      (2.569090505045048420321026167745 : ℝ) ≤ θ ∧
      θ ≤ (2.5690905050450484203210261677451 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismDecagonalPrismDim.root (a := 2.569090505045048420321026167745) (b := 2.5690905050450484203210261677451) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Prism.DecagonalPrism.Proof
