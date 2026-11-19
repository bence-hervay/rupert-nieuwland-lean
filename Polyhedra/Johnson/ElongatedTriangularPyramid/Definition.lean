import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The elongated triangular pyramid

The polyhedron `Johnson.ElongatedTriangularPyramid.polyhedron`: the convex hull of 7 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.ElongatedTriangularPyramid

/-- `θ`: the largest root of
`1/36 + x - 2 * x ^ 3 + x ^ 4`
in the interval `(5/4, 2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/36, 1, 0, -2, 1] (5/4) 2

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The elongated triangular pyramid: the convex hull of these 7 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [-2/7, 1/7, 9/7, -6/7] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [4/7, -2/7, -18/7, 12/7] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [4/7, -2/7, -18/7, 12/7] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-2/7, 8/7, 9/7, -6/7] θ]].toFinset

end Nieuwland.Johnson.ElongatedTriangularPyramid
