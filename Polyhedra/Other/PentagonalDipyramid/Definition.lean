import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The pentagonal dipyramid

The polyhedron `Other.PentagonalDipyramid.polyhedron`: the convex hull of 7 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.PentagonalDipyramid

/-- `θ`: the largest root of
`5/16 - 5/4 * x ^ 2 + x ^ 4`
in the interval `(3/8, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [5/16, 0, -5/4, 0, 1] (3/8) (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The pentagonal dipyramid: the convex hull of these 7 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [5/2, 0, -6] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, 2] θ, polyEval [0] θ],
    ![polyEval [0, -4, 0, 8] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, -2] θ, polyEval [0] θ],
    ![polyEval [0, 1] θ, polyEval [-5/2, 0, 6] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.PentagonalDipyramid
