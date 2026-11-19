import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The elongated triangular dipyramid j14

The polyhedron `Johnson.ElongatedTriangularDipyramidJ14.polyhedron`: the convex hull of 8 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.ElongatedTriangularDipyramidJ14

/-- `θ`: the largest root of
`1/36 + x - 2 * x ^ 3 + x ^ 4`
in the interval `(5/4, 2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/36, 1, 0, -2, 1] (5/4) 2

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The elongated triangular dipyramid j14: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [4/7, -2/7, -18/7, 12/7] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [4/7, -2/7, -18/7, 12/7] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-2/7, 8/7, 9/7, -6/7] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [2/7, -8/7, -9/7, 6/7] θ]].toFinset

end Nieuwland.Johnson.ElongatedTriangularDipyramidJ14
