import Modules.Check.Number.ThetaRoot
import Polyhedra.Prism.DodecagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The dodecagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Prism.DodecagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1, 0, -4, 0, 1] θ = 0 ∧
      (1.9318516525781365734994863994577 : ℝ) ≤ θ ∧
      θ ≤ (1.9318516525781365734994863994578 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismDodecagonalPrismDim.root (a := 1.9318516525781365734994863994577) (b := 1.9318516525781365734994863994578) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Prism.DodecagonalPrism.Proof
