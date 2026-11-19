import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The enneagonal prism

The polyhedron `Prism.EnneagonalPrism.polyhedron`: the convex hull of 18 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Prism.EnneagonalPrism

/-- `θ`: the largest root of
`-1/3 + 2 * x ^ 2 - 3 * x ^ 4 + x ^ 6`
in the interval `(1, 7/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/3, 0, 2, 0, -3, 0, 1] 1 (7/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The enneagonal prism: the convex hull of these 18 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [1/2, 0, -3, 0, 3/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [1, 0, -3, 0, 3/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [-3/2, 0, 9/2, 0, -3/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [-1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [3/2, 0, -9/2, 0, 3/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [-1, 0, 3, 0, -3/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [-1/2, 0, 3, 0, -3/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [1/2, 0, -3, 0, 3/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [1, 0, -3, 0, 3/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [-3/2, 0, 9/2, 0, -3/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1/2, 0, 3, 0, -3/2] θ, polyEval [-1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [3/2, 0, -9/2, 0, 3/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 5/2, 0, -15/2, 0, 3] θ, polyEval [-1, 0, 3, 0, -3/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -2, 0, 9/2, 0, -3/2] θ, polyEval [-1/2, 0, 3, 0, -3/2] θ, polyEval [1/2] θ]].toFinset

end Nieuwland.Prism.EnneagonalPrism
