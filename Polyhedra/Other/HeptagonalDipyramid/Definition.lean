import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The heptagonal dipyramid

The polyhedron `Other.HeptagonalDipyramid.polyhedron`: the convex hull of 9 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.HeptagonalDipyramid

/-- `θ`: the largest root of
`-7/64 + 7/8 * x ^ 2 - 7/4 * x ^ 4 + x ^ 6`
in the interval `(0, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-7/64, 0, 7/8, 0, -7/4, 0, 1] 0 (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The heptagonal dipyramid: the convex hull of these 9 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [7/2, 0, -22, 0, 24] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, 4, 0, -8] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, 2] θ, polyEval [0] θ],
    ![polyEval [0, -6, 0, 32, 0, -32] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, -2] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, -4, 0, 8] θ, polyEval [0] θ],
    ![polyEval [0, 1] θ, polyEval [-7/2, 0, 22, 0, -24] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.HeptagonalDipyramid
