import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The enneagonal dipyramid

The polyhedron `Other.EnneagonalDipyramid.polyhedron`: the convex hull of 11 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.EnneagonalDipyramid

/-- `θ`: the largest root of
`-3/64 + 9/16 * x ^ 2 - 3/2 * x ^ 4 + x ^ 6`
in the interval `(1/8, 1/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-3/64, 0, 9/16, 0, -3/2, 0, 1] (1/8) (1/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The enneagonal dipyramid: the convex hull of these 11 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 0, 2, 0, -8] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [3/2, 0, -12, 0, 16] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, 4, 0, -8] θ, polyEval [0] θ],
    ![polyEval [0, -2, 0, 12, 0, -16] θ, polyEval [0, 0, 2] θ, polyEval [0] θ],
    ![polyEval [0, -2, 0, 8] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [0, -2, 0, 12, 0, -16] θ, polyEval [0, 0, -2] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, -4, 0, 8] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [-3/2, 0, 12, 0, -16] θ, polyEval [0] θ],
    ![polyEval [0, 1] θ, polyEval [0, 0, -2, 0, 8] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.EnneagonalDipyramid
