import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The heptagonal antiprism

The polyhedron `Antiprism.HeptagonalAntiprism.polyhedron`: the convex hull of 14 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Antiprism.HeptagonalAntiprism

/-- `θ`: the largest root of
`-1/8 - 1/2 * x + 1/4 * x ^ 2 + 3/2 * x ^ 3 - x ^ 4 - x ^ 5 + x ^ 6`
in the interval `(0, 3/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/8, -1/2, 1/4, 3/2, -1, -1, 1] 0 (3/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The heptagonal antiprism: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [0] θ, polyEval [-2, -2, 12, -4, -10, 8] θ],
    ![polyEval [1/2] θ, polyEval [0] θ, polyEval [2, 2, -12, 4, 10, -8] θ],
    ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [-2, -2, 12, -4, -10, 8] θ],
    ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [2, 2, -12, 4, 10, -8] θ],
    ![polyEval [0] θ, polyEval [0, 2, -1, -2, 2] θ, polyEval [-1/2, -1, 5, -2, -4, 4] θ],
    ![polyEval [0] θ, polyEval [0, 2, -1, -2, 2] θ, polyEval [1/2, 1, -5, 2, 4, -4] θ],
    ![polyEval [0] θ, polyEval [0, -2, 1, 2, -2] θ, polyEval [-1/2, -1, 5, -2, -4, 4] θ],
    ![polyEval [0] θ, polyEval [0, -2, 1, 2, -2] θ, polyEval [1/2, 1, -5, 2, 4, -4] θ],
    ![polyEval [-1/2, -1, 5, -2, -4, 4] θ, polyEval [3/2, 2, -7, 2, 6, -4] θ, polyEval [1/2] θ],
    ![polyEval [-1/2, -1, 5, -2, -4, 4] θ, polyEval [3/2, 2, -7, 2, 6, -4] θ, polyEval [-1/2] θ],
    ![polyEval [1/2, 1, -5, 2, 4, -4] θ, polyEval [-3/2, -2, 7, -2, -6, 4] θ, polyEval [1/2] θ],
    ![polyEval [1/2, 1, -5, 2, 4, -4] θ, polyEval [-3/2, -2, 7, -2, -6, 4] θ, polyEval [-1/2] θ],
    ![polyEval [-3/2, -1, 7, -2, -6, 4] θ, polyEval [2, 4, -9, 0, 8, -4] θ, polyEval [0] θ],
    ![polyEval [3/2, 1, -7, 2, 6, -4] θ, polyEval [-2, -4, 9, 0, -8, 4] θ, polyEval [0] θ]].toFinset

end Nieuwland.Antiprism.HeptagonalAntiprism
