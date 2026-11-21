import Modules.Check.Number.ThetaRoot
import Polyhedra.Other.HexagonalTrapezohedron.Proof.FullDim

set_option linter.style.longLine false

/-!
# The hexagonal trapezohedron: the root `θ` of its coordinates

`θ` is a root of its polynomial, between two rationals: `Check.Root.theta_isRoot` for the data `root`
of `Proof/FullDim.lean`, whose enclosure of `c θ` lies between the rationals times `c` (the kernel
compares them).
-/

namespace Nieuwland.Other.HexagonalTrapezohedron.Proof

@[inherit_doc] local notation "θ" => theta

theorem theta_isRoot :
    polyEval [-18, 0, 114, 0, 1] θ = 0 ∧
      (0.397085192084709558243302057504 : ℝ) ≤ θ ∧
      θ ≤ (0.3970851920847095582433020575041 : ℝ) := by
  have h := Check.Root.theta_isRoot Polyhedra.TrapezohedronHexagonalTrapezohedronDim.root (a := 0.397085192084709558243302057504) (b := 0.3970851920847095582433020575041) (by decide +kernel)
  push_cast at h
  exact h

end Nieuwland.Other.HexagonalTrapezohedron.Proof
