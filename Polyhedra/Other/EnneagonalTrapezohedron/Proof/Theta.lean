import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.EnneagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The enneagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.EnneagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [64/81, 0, -256/9, 0, 1168/9, 0, 1760/9, 0, -280, 0, 64, 0, 1] θ = 0 ∧
      (0.3894107250291187690117025147923 : ℝ) ≤ θ ∧
      θ ≤ (0.3894107250291187690117025147924 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronEnneagonalTrapezohedronDim.root (a := 0.3894107250291187690117025147923) (b := 0.3894107250291187690117025147924) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.EnneagonalTrapezohedron.Proof
