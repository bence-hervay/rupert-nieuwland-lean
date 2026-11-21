import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The pentagonal trapezohedron

The polyhedron `Other.PentagonalTrapezohedron.polyhedron`: the convex hull of 12 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.PentagonalTrapezohedron

/-- `θ`: the largest root of
`-4/25 + 8/5 * x - 12/5 * x ^ 2 + x ^ 4`
in the interval `(11/16, 7/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-4/25, 8/5, -12/5, 0, 1] (11/16) (7/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The pentagonal trapezohedron: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 4, -5/2, -5/2] θ, polyEval [0, -3, 5/2, 5/2] θ, polyEval [-1, 8, -5, -5] θ],
    ![polyEval [-1/2, 6, -15/4, -15/4] θ, polyEval [-3/2, 17/2, -15/4, -5] θ, polyEval [1, -8, 5, 5] θ],
    ![polyEval [1/2, -6, 15/4, 15/4] θ, polyEval [-3/2, 17/2, -15/4, -5] θ, polyEval [-1, 8, -5, -5] θ],
    ![polyEval [0, -4, 5/2, 5/2] θ, polyEval [0, -3, 5/2, 5/2] θ, polyEval [1, -8, 5, 5] θ],
    ![polyEval [-1, 4, -5/2, -5/2] θ, polyEval [0] θ, polyEval [-1, 8, -5, -5] θ],
    ![polyEval [0, -4, 5/2, 5/2] θ, polyEval [0, 3, -5/2, -5/2] θ, polyEval [1, -8, 5, 5] θ],
    ![polyEval [1/2, -6, 15/4, 15/4] θ, polyEval [3/2, -17/2, 15/4, 5] θ, polyEval [-1, 8, -5, -5] θ],
    ![polyEval [-1/2, 6, -15/4, -15/4] θ, polyEval [3/2, -17/2, 15/4, 5] θ, polyEval [1, -8, 5, 5] θ],
    ![polyEval [0, 4, -5/2, -5/2] θ, polyEval [0, 3, -5/2, -5/2] θ, polyEval [-1, 8, -5, -5] θ],
    ![polyEval [1, -4, 5/2, 5/2] θ, polyEval [0] θ, polyEval [1, -8, 5, 5] θ]].toFinset

end Nieuwland.Other.PentagonalTrapezohedron
