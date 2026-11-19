import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The biaugmented pentagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.BiaugmentedPentagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [121/65536, 0, -119/2048, 0, 139/256, 0, -11/8, 0, 1] θ = 0 ∧
      (0.6940362703719873214578702692175 : ℝ) ≤ θ ∧
      θ ≤ (0.6940362703719873214578702692176 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonBiaugmentedPentagonalPrismDim.root (a := 0.6940362703719873214578702692175) (b := 0.6940362703719873214578702692176) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.BiaugmentedPentagonalPrism.Proof
