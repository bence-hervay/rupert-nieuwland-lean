import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The biaugmented triangular prism

The polyhedron `Johnson.BiaugmentedTriangularPrism.polyhedron`: the convex hull of 8 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.BiaugmentedTriangularPrism

/-- `θ`: the largest root of
`1/256 - 5/8 * x ^ 2 + x ^ 4`
in the interval `(1/2, 5/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/256, 0, -5/8, 0, 1] (1/2) (5/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The biaugmented triangular prism: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, 11/3, 0, -16/3] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, 11/3, 0, -16/3] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, 11/3, 0, -16/3] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, 11/3, 0, -16/3] θ],
    ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, -22/3, 0, 32/3] θ],
    ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, -22/3, 0, 32/3] θ],
    ![polyEval [-3/8, 0, 2] θ, polyEval [0] θ, polyEval [0, 8/3, 0, -16/3] θ],
    ![polyEval [3/8, 0, -2] θ, polyEval [0] θ, polyEval [0, 8/3, 0, -16/3] θ]].toFinset

end Nieuwland.Johnson.BiaugmentedTriangularPrism
