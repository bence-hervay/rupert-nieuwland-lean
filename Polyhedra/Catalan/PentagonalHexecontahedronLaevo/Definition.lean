import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The pentagonal hexecontahedron laevo

The polyhedron `Catalan.PentagonalHexecontahedronLaevo.polyhedron`: the convex hull of 92 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Catalan.PentagonalHexecontahedronLaevo

/-- `θ`: the largest root of
`1 - 2 * x - x ^ 2 - 2 * x ^ 4 + 2 * x ^ 5 + x ^ 6`
in the interval `(1/2, 2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1, -2, -1, 0, -2, 2, 1] (1/2) 2

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The pentagonal hexecontahedron laevo: the convex hull of these 92 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [-1] θ, polyEval [0, -1] θ, polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ],
    ![polyEval [-1] θ, polyEval [0, 1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ],
    ![polyEval [1] θ, polyEval [0, 1] θ, polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ],
    ![polyEval [1] θ, polyEval [0, -1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ],
    ![polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval [-1] θ, polyEval [0, -1] θ],
    ![polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval [1] θ, polyEval [0, 1] θ],
    ![polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [1] θ, polyEval [0, -1] θ],
    ![polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [-1] θ, polyEval [0, 1] θ],
    ![polyEval [0, -1] θ, polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval [-1] θ],
    ![polyEval [0, -1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [-2, 3/2, 1/2, 2, 7/2, 1] θ, polyEval [-1] θ],
    ![polyEval [0, 1] θ, polyEval [2, -3/2, -1/2, -2, -7/2, -1] θ, polyEval [1] θ],
    ![polyEval [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ, polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ],
    ![polyEval [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ, polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ],
    ![polyEval [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ, polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ],
    ![polyEval [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ, polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ],
    ![polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ],
    ![polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ],
    ![polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ, polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ],
    ![polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ, polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ],
    ![polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ, polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval [0] θ],
    ![polyEval [-1/2, -2, 0, -2, 1/2, 1/2] θ, polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ],
    ![polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ, polyEval [1/2, -3/2, -3/2, -2, -2, -1/2] θ, polyEval [0] θ],
    ![polyEval [1/2, 2, 0, 2, -1/2, -1/2] θ, polyEval [-1/2, 3/2, 3/2, 2, 2, 1/2] θ, polyEval [0] θ],
    ![polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ, polyEval [0] θ, polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ],
    ![polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ, polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ],
    ![polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ, polyEval [0] θ, polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ],
    ![polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ, polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ],
    ![polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ, polyEval [0] θ],
    ![polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ, polyEval [0] θ],
    ![polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ, polyEval [0] θ],
    ![polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ],
    ![polyEval [0] θ, polyEval [89/62, -37/31, -28/31, -47/31, -183/62, -55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ],
    ![polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ, polyEval [-41/62, 1/62, -109/62, -9/31, -35/31, -29/62] θ],
    ![polyEval [0] θ, polyEval [-89/62, 37/31, 28/31, 47/31, 183/62, 55/62] θ, polyEval [41/62, -1/62, 109/62, 9/31, 35/31, 29/62] θ],
    ![polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [1, -1, -1, -1, -3, -1] θ],
    ![polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval [1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [-1, 1, 1, 1, 3, 1] θ],
    ![polyEval [3/2, -1/2, 1, 1/2] θ, polyEval [1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [1, -1, -1, -1, -3, -1] θ],
    ![polyEval [3/2, -1/2, 1, 1/2] θ, polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [-1, 1, 1, 1, 3, 1] θ],
    ![polyEval [1, -1, -1, -1, -3, -1] θ, polyEval [3/2, -1/2, 1, 1/2] θ, polyEval [1/2, -1, -1/2, -3/2, -1/2] θ],
    ![polyEval [1, -1, -1, -1, -3, -1] θ, polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ],
    ![polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval [-3/2, 1/2, -1, -1/2] θ, polyEval [1/2, -1, -1/2, -3/2, -1/2] θ],
    ![polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval [3/2, -1/2, 1, 1/2] θ, polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ],
    ![polyEval [1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval [-3/2, 1/2, -1, -1/2] θ],
    ![polyEval [1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [1, -1, -1, -1, -3, -1] θ, polyEval [3/2, -1/2, 1, 1/2] θ],
    ![polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [1, -1, -1, -1, -3, -1] θ, polyEval [-3/2, 1/2, -1, -1/2] θ],
    ![polyEval [-1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [-1, 1, 1, 1, 3, 1] θ, polyEval [3/2, -1/2, 1, 1/2] θ],
    ![polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ],
    ![polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ, polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ],
    ![polyEval [1/2, -1/2, 1, 1/2] θ, polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ],
    ![polyEval [1/2, -1/2, 1, 1/2] θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ, polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ],
    ![polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ],
    ![polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ, polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ],
    ![polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ, polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ],
    ![polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ, polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ],
    ![polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ],
    ![polyEval [1, -1, 1/2, -3/2, -2, -1/2] θ, polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ],
    ![polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ, polyEval [1/2, 1, 2, 1, 3/2, 1/2] θ, polyEval [-1/2, 1/2, -1, -1/2] θ],
    ![polyEval [-1, 1, -1/2, 3/2, 2, 1/2] θ, polyEval [-1/2, -1, -2, -1, -3/2, -1/2] θ, polyEval [1/2, -1/2, 1, 1/2] θ],
    ![polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ],
    ![polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ],
    ![polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ],
    ![polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ],
    ![polyEval [1, 0, -1, -1, -3, -1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ],
    ![polyEval [1, 0, -1, -1, -3, -1] θ, polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ],
    ![polyEval [-1, 0, 1, 1, 3, 1] θ, polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ],
    ![polyEval [-1, 0, 1, 1, 3, 1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ],
    ![polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ],
    ![polyEval [1, -1/2, -1, -1/2, -3/2, -1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ, polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ],
    ![polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [-1, 0, 1, 1, 3, 1] θ, polyEval [-1, 0, -3/2, 1/2, -1, -1/2] θ],
    ![polyEval [-1, 1/2, 1, 1/2, 3/2, 1/2] θ, polyEval [1, 0, -1, -1, -3, -1] θ, polyEval [1, 0, 3/2, -1/2, 1, 1/2] θ],
    ![polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ],
    ![polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ],
    ![polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ],
    ![polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ],
    ![polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ],
    ![polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ],
    ![polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ, polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ],
    ![polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ, polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ],
    ![polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ],
    ![polyEval [3/2, -1/2, 0, -1/2, -3, -1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ],
    ![polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ, polyEval [-1/2, 0, -2, -1, -3/2, -1/2] θ, polyEval [0, 0, -3/2, 1/2, -1, -1/2] θ],
    ![polyEval [-3/2, 1/2, 0, 1/2, 3, 1] θ, polyEval [1/2, 0, 2, 1, 3/2, 1/2] θ, polyEval [0, 0, 3/2, -1/2, 1, 1/2] θ],
    ![polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ],
    ![polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ],
    ![polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ],
    ![polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ],
    ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ],
    ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ],
    ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [1, 1/2, -3/2, 0, -5/2, -1] θ],
    ![polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ, polyEval [-1, -1/2, 3/2, 0, 5/2, 1] θ]].toFinset

end Nieuwland.Catalan.PentagonalHexecontahedronLaevo
