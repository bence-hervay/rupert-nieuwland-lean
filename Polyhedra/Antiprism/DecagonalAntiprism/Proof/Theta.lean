import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.DecagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The decagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.DecagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [281/256, 59/8, 277/32, -17/2, -211/16, 7, 4, -4, 1] θ = 0 ∧
      (2.0492324906796240899281131768195 : ℝ) ≤ θ ∧
      θ ≤ (2.0492324906796240899281131768196 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismDecagonalAntiprismDim.root (a := 2.0492324906796240899281131768195) (b := 2.0492324906796240899281131768196) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.DecagonalAntiprism.Proof
