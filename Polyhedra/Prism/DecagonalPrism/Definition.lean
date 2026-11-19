import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The decagonal prism

The polyhedron `Prism.DecagonalPrism.polyhedron`: the convex hull of 20 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Prism.DecagonalPrism

/-- `θ`: the largest root of
`1/16 + 2 * x - 9/4 * x ^ 2 - 2 * x ^ 3 + x ^ 4`
in the interval `(2, 7/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/16, 2, -9/4, -2, 1] 2 (7/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The decagonal prism: the convex hull of these 20 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [-22/41, 112/41, 52/41, -32/41] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [22/41, -71/41, -52/41, 32/41] θ, polyEval [-1/2] θ],
    ![polyEval [1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [-1/2] θ],
    ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [22/41, -71/41, -52/41, 32/41] θ, polyEval [-1/2] θ],
    ![polyEval [22/41, -112/41, -52/41, 32/41] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [-22/41, 71/41, 52/41, -32/41] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [-1/2] θ],
    ![polyEval [1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [-1/2] θ],
    ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [-22/41, 71/41, 52/41, -32/41] θ, polyEval [-1/2] θ],
    ![polyEval [-22/41, 112/41, 52/41, -32/41] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [22/41, -71/41, -52/41, 32/41] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [-17/41, -70/41, -12/41, 20/41] θ, polyEval [1/2] θ],
    ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [22/41, -71/41, -52/41, 32/41] θ, polyEval [1/2] θ],
    ![polyEval [22/41, -112/41, -52/41, 32/41] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [-19/82, -56/41, -26/41, 16/41] θ, polyEval [-22/41, 71/41, 52/41, -32/41] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [17/41, 70/41, 12/41, -20/41] θ, polyEval [1/2] θ],
    ![polyEval [19/82, 56/41, 26/41, -16/41] θ, polyEval [-22/41, 71/41, 52/41, -32/41] θ, polyEval [1/2] θ]].toFinset

end Nieuwland.Prism.DecagonalPrism
