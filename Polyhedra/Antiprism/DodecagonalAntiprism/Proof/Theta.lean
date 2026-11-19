import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.DodecagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The dodecagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.DodecagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [71/128, -17/8, -297/16, 11, 229/8, -14, -5, 0, 1] θ = 0 ∧
      (2.3636116857475321235186088937421 : ℝ) ≤ θ ∧
      θ ≤ (2.3636116857475321235186088937422 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismDodecagonalAntiprismDim.root (a := 2.3636116857475321235186088937421) (b := 2.3636116857475321235186088937422) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.DodecagonalAntiprism.Proof
