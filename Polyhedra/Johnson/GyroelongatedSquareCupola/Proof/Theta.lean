import Modules.Check.Number.ThetaRoot
import Polyhedra.Johnson.GyroelongatedSquareCupola.Proof.FullDim

set_option linter.style.longLine false

/-!
# The gyroelongated square cupola: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Johnson.GyroelongatedSquareCupola.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-1/512, 0, 1/16, 0, -1/2, 0, 1, 0, 1] θ = 0 ∧
      (0.430147784931485783221150388002 : ℝ) ≤ θ ∧
      θ ≤ (0.4301477849314857832211503880021 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.JohnsonGyroelongatedSquareCupolaDim.root (a := 0.430147784931485783221150388002) (b := 0.4301477849314857832211503880021) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Johnson.GyroelongatedSquareCupola.Proof
