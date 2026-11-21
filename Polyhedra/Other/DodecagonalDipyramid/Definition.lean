import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The dodecagonal dipyramid

The polyhedron `Other.DodecagonalDipyramid.polyhedron`: the convex hull of 14 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.DodecagonalDipyramid

/-- `θ`: the largest root of
`1/16 - x ^ 2 + x ^ 4`
in the interval `(0, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/16, 0, -1, 0, 1] 0 (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The dodecagonal dipyramid: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 0, 0, 4] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 1, 0, -4] θ, polyEval [0] θ],
    ![polyEval [0, 0, 0, 4] θ, polyEval [0, 1] θ, polyEval [0] θ],
    ![polyEval [0, 0, 0, -4] θ, polyEval [0, 1] θ, polyEval [0] θ],
    ![polyEval [0, -1, 0, 4] θ, polyEval [0, 1, 0, -4] θ, polyEval [0] θ],
    ![polyEval [0, -1] θ, polyEval [0, 0, 0, 4] θ, polyEval [0] θ],
    ![polyEval [0, -1] θ, polyEval [0, 0, 0, -4] θ, polyEval [0] θ],
    ![polyEval [0, -1, 0, 4] θ, polyEval [0, -1, 0, 4] θ, polyEval [0] θ],
    ![polyEval [0, 0, 0, -4] θ, polyEval [0, -1] θ, polyEval [0] θ],
    ![polyEval [0, 0, 0, 4] θ, polyEval [0, -1] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, -1, 0, 4] θ, polyEval [0] θ],
    ![polyEval [0, 1] θ, polyEval [0, 0, 0, -4] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.DodecagonalDipyramid
