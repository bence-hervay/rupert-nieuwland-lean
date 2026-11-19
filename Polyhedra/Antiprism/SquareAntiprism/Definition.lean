import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The square antiprism

The polyhedron `Antiprism.SquareAntiprism.polyhedron`: the convex hull of 8 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Antiprism.SquareAntiprism

/-- `θ`: the largest root of
`7/32 - 1/2 * x - x ^ 2 + x ^ 4`
in the interval `(1/2, 2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [7/32, -1/2, -1, 0, 1] (1/2) 2

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The square antiprism: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [10/33, 16/11, 4/33, -32/33] θ, polyEval [0] θ, polyEval [10/33, 5/11, 4/33, -32/33] θ],
    ![polyEval [0] θ, polyEval [10/33, 16/11, 4/33, -32/33] θ, polyEval [10/33, 5/11, 4/33, -32/33] θ],
    ![polyEval [-10/33, -16/11, -4/33, 32/33] θ, polyEval [0] θ, polyEval [10/33, 5/11, 4/33, -32/33] θ],
    ![polyEval [0] θ, polyEval [-10/33, -16/11, -4/33, 32/33] θ, polyEval [10/33, 5/11, 4/33, -32/33] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [-10/33, -5/11, -4/33, 32/33] θ]].toFinset

end Nieuwland.Antiprism.SquareAntiprism
