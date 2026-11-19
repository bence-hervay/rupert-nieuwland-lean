import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.SnubSquareAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The snub square antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.SnubSquareAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/8192, 0, -7/512, 0, 11/16, 0, -187/32, 0, 355/32, 0, 9, 0, 1] θ = 0 ∧
      (0.1856070212821798475712036428074 : ℝ) ≤ θ ∧
      θ ≤ (0.1856070212821798475712036428075 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonSnubSquareAntiprismDim.root (a := 0.1856070212821798475712036428074) (b := 0.1856070212821798475712036428075) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.SnubSquareAntiprism.Proof
