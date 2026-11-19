import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.HendecagonalAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hendecagonal antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.HendecagonalAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [1/14641, 0, 2/1331, 0, -349/1331, 0, 694/121, 0, -5728/121, 0, 20792/121, 0, -3147/11,
      0, 2234/11, 0, -49, 0, -2, 0, 1] θ = 0 ∧
      (2.3946955751488308785654099743758 : ℝ) ≤ θ ∧
      θ ≤ (2.3946955751488308785654099743759 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismHendecagonalAntiprismDim.root (a := 2.3946955751488308785654099743758) (b := 2.3946955751488308785654099743759) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.HendecagonalAntiprism.Proof
