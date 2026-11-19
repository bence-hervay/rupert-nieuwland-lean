import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.ParabiaugmentedHexagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The parabiaugmented hexagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.ParabiaugmentedHexagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [25/4, 0, -7, 0, 1] θ = 0 ∧
      (2.4391575887554248179282907036107 : ℝ) ≤ θ ∧
      θ ≤ (2.4391575887554248179282907036108 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonParabiaugmentedHexagonalPrismDim.root (a := 2.4391575887554248179282907036107) (b := 2.4391575887554248179282907036108) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.ParabiaugmentedHexagonalPrism.Proof
