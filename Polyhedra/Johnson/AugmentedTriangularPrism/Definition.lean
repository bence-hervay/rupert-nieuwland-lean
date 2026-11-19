import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The augmented triangular prism

The polyhedron `Johnson.AugmentedTriangularPrism.polyhedron`: the convex hull of 7 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.AugmentedTriangularPrism

/-- `θ`: the largest root of
`1/36 - 5/3 * x ^ 2 + x ^ 4`
in the interval `(1/2, 2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/36, 0, -5/3, 0, 1] (1/2) 2

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The augmented triangular prism: the convex hull of these 7 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -9/4, 0, 3/2] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -9/4, 0, 3/2] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -9/4, 0, 3/2] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -9/4, 0, 3/2] θ],
    ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, 9/2, 0, -3] θ],
    ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, 9/2, 0, -3] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 13/4, 0, -3/2] θ]].toFinset

end Nieuwland.Johnson.AugmentedTriangularPrism
