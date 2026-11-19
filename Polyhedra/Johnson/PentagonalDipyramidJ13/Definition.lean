import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The pentagonal dipyramid j13

The polyhedron `Johnson.PentagonalDipyramidJ13.polyhedron`: the convex hull of 7 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.PentagonalDipyramidJ13

/-- `θ`: the largest root of
`1/80 - 1/4 * x ^ 2 + x ^ 4`
in the interval `(3/16, 3/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/80, 0, -1/4, 0, 1] (3/16) (3/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The pentagonal dipyramid j13: the convex hull of these 7 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, -2] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 2] θ],
    ![polyEval [3/2, 0, -10] θ, polyEval [0, 1] θ, polyEval [0] θ],
    ![polyEval [-3/2, 0, 10] θ, polyEval [0, 1] θ, polyEval [0] θ],
    ![polyEval [1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [0] θ],
    ![polyEval [-1/2] θ, polyEval [0, -4, 0, 20] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [0, 6, 0, -40] θ, polyEval [0] θ]].toFinset

end Nieuwland.Johnson.PentagonalDipyramidJ13
