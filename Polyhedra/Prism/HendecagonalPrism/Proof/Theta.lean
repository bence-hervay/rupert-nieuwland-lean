import Modules.Check.Number.ThetaRoot
import Polyhedra.Prism.HendecagonalPrism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hendecagonal prism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Prism.HendecagonalPrism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/11, 0, 1, 0, -4, 0, 7, 0, -5, 0, 1] θ = 0 ∧
      (1.7747327664421116628568319611689 : ℝ) ≤ θ ∧
      θ ≤ (1.774732766442111662856831961169 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismHendecagonalPrismDim.root (a := 1.7747327664421116628568319611689) (b := 1.774732766442111662856831961169) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Prism.HendecagonalPrism.Proof
