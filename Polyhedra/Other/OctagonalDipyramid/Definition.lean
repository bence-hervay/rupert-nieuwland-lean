import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The octagonal dipyramid

The polyhedron `Other.OctagonalDipyramid.polyhedron`: the convex hull of 10 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.OctagonalDipyramid

/-- `θ`: the largest root of
`1/8 - x ^ 2 + x ^ 4`
in the interval `(0, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/8, 0, -1, 0, 1] 0 (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The octagonal dipyramid: the convex hull of these 10 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 1, 0, -4] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 1] θ, polyEval [0] θ],
    ![polyEval [0, -1, 0, 4] θ, polyEval [0, 1] θ, polyEval [0] θ],
    ![polyEval [0, -1] θ, polyEval [0, 1, 0, -4] θ, polyEval [0] θ],
    ![polyEval [0, -1] θ, polyEval [0, -1, 0, 4] θ, polyEval [0] θ],
    ![polyEval [0, -1, 0, 4] θ, polyEval [0, -1] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, -1] θ, polyEval [0] θ],
    ![polyEval [0, 1] θ, polyEval [0, -1, 0, 4] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.OctagonalDipyramid
