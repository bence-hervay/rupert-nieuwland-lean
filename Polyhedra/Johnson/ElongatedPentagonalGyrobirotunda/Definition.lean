import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The elongated pentagonal gyrobirotunda

The polyhedron `Johnson.ElongatedPentagonalGyrobirotunda.polyhedron`: the convex hull of 40 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalGyrobirotunda

/-- `θ`: the largest root of
`1/80 - 1/4 * x ^ 2 + x ^ 4`
in the interval `(3/16, 3/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/80, 0, -1/4, 0, 1] (3/16) (3/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The elongated pentagonal gyrobirotunda: the convex hull of these 40 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [3, 0, -20] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [3, 0, -20] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [-3, 0, 20] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [-3, 0, 20] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [2, 0, -10] θ, polyEval [0, 5, 0, -20] θ, polyEval [1/2] θ],
    ![polyEval [2, 0, -10] θ, polyEval [0, 5, 0, -20] θ, polyEval [-1/2] θ],
    ![polyEval [2, 0, -10] θ, polyEval [0, -5, 0, 20] θ, polyEval [1/2] θ],
    ![polyEval [2, 0, -10] θ, polyEval [0, -5, 0, 20] θ, polyEval [-1/2] θ],
    ![polyEval [-2, 0, 10] θ, polyEval [0, 5, 0, -20] θ, polyEval [1/2] θ],
    ![polyEval [-2, 0, 10] θ, polyEval [0, 5, 0, -20] θ, polyEval [-1/2] θ],
    ![polyEval [-2, 0, 10] θ, polyEval [0, -5, 0, 20] θ, polyEval [1/2] θ],
    ![polyEval [-2, 0, 10] θ, polyEval [0, -5, 0, 20] θ, polyEval [-1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [-1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, 10, 0, -60] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, -10, 0, 60] θ, polyEval [-1/2] θ],
    ![polyEval [3/2, 0, -10] θ, polyEval [0, 1] θ, polyEval [1/2, 8, 0, -40] θ],
    ![polyEval [3/2, 0, -10] θ, polyEval [0, -1] θ, polyEval [-1/2, -8, 0, 40] θ],
    ![polyEval [-3/2, 0, 10] θ, polyEval [0, 1] θ, polyEval [1/2, 8, 0, -40] θ],
    ![polyEval [-3/2, 0, 10] θ, polyEval [0, -1] θ, polyEval [-1/2, -8, 0, 40] θ],
    ![polyEval [1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [1/2, 8, 0, -40] θ],
    ![polyEval [1/2] θ, polyEval [0, 4, 0, -20] θ, polyEval [-1/2, -8, 0, 40] θ],
    ![polyEval [-1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [1/2, 8, 0, -40] θ],
    ![polyEval [-1/2] θ, polyEval [0, 4, 0, -20] θ, polyEval [-1/2, -8, 0, 40] θ],
    ![polyEval [0] θ, polyEval [0, 6, 0, -40] θ, polyEval [1/2, 8, 0, -40] θ],
    ![polyEval [0] θ, polyEval [0, -6, 0, 40] θ, polyEval [-1/2, -8, 0, 40] θ],
    ![polyEval [2, 0, -10] θ, polyEval [0, -3, 0, 20] θ, polyEval [1/2, 6, 0, -40] θ],
    ![polyEval [2, 0, -10] θ, polyEval [0, 3, 0, -20] θ, polyEval [-1/2, -6, 0, 40] θ],
    ![polyEval [-2, 0, 10] θ, polyEval [0, -3, 0, 20] θ, polyEval [1/2, 6, 0, -40] θ],
    ![polyEval [-2, 0, 10] θ, polyEval [0, 3, 0, -20] θ, polyEval [-1/2, -6, 0, 40] θ],
    ![polyEval [3/2, 0, -10] θ, polyEval [0, 7, 0, -40] θ, polyEval [1/2, 6, 0, -40] θ],
    ![polyEval [3/2, 0, -10] θ, polyEval [0, -7, 0, 40] θ, polyEval [-1/2, -6, 0, 40] θ],
    ![polyEval [-3/2, 0, 10] θ, polyEval [0, 7, 0, -40] θ, polyEval [1/2, 6, 0, -40] θ],
    ![polyEval [-3/2, 0, 10] θ, polyEval [0, -7, 0, 40] θ, polyEval [-1/2, -6, 0, 40] θ],
    ![polyEval [0] θ, polyEval [0, -8, 0, 40] θ, polyEval [1/2, 6, 0, -40] θ],
    ![polyEval [0] θ, polyEval [0, 8, 0, -40] θ, polyEval [-1/2, -6, 0, 40] θ]].toFinset

end Nieuwland.Johnson.ElongatedPentagonalGyrobirotunda
