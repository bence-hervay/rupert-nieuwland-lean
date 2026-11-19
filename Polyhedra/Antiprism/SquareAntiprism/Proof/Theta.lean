import Modules.Check.Number.ThetaRoot
import Polyhedra.Antiprism.SquareAntiprism.Proof.FullDim

set_option linter.style.longLine false

/-!
# The square antiprism: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Antiprism.SquareAntiprism.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [7/32, -1/2, -1, 0, 1] θ = 0 ∧
      (1.1275549888134047959164071002214 : ℝ) ≤ θ ∧
      θ ≤ (1.1275549888134047959164071002215 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.PrismSquareAntiprismDim.root (a := 1.1275549888134047959164071002214) (b := 1.1275549888134047959164071002215) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Antiprism.SquareAntiprism.Proof
