import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The decagonal dipyramid

The polyhedron `Other.DecagonalDipyramid.polyhedron`: the convex hull of 12 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.DecagonalDipyramid

/-- `θ`: the largest root of
`-1/20 + 1/2 * x - 3/2 * x ^ 2 + x ^ 3 + x ^ 4`
in the interval `(5/16, 1/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/20, 1/2, -3/2, 1, 1] (5/16) (1/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The decagonal dipyramid: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [17/2, -55, 65, 50] θ, polyEval [-17/2, 56, -65, -50] θ, polyEval [0] θ],
    ![polyEval [-8, 55, -65, -50] θ, polyEval [-4, 24, -25, -20] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [9, -64, 80, 60] θ, polyEval [0] θ],
    ![polyEval [8, -55, 65, 50] θ, polyEval [-4, 24, -25, -20] θ, polyEval [0] θ],
    ![polyEval [-17/2, 55, -65, -50] θ, polyEval [-17/2, 56, -65, -50] θ, polyEval [0] θ],
    ![polyEval [-17/2, 55, -65, -50] θ, polyEval [17/2, -56, 65, 50] θ, polyEval [0] θ],
    ![polyEval [8, -55, 65, 50] θ, polyEval [4, -24, 25, 20] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [-9, 64, -80, -60] θ, polyEval [0] θ],
    ![polyEval [-8, 55, -65, -50] θ, polyEval [4, -24, 25, 20] θ, polyEval [0] θ],
    ![polyEval [17/2, -55, 65, 50] θ, polyEval [17/2, -56, 65, 50] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.DecagonalDipyramid
