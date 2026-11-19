import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The hexagonal antiprism

The polyhedron `Antiprism.HexagonalAntiprism.polyhedron`: the convex hull of 12 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Antiprism.HexagonalAntiprism

/-- `θ`: the largest root of
`-1/8 + 1/2 * x ^ 2 + x ^ 4`
in the interval `(0, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/8, 0, 1/2, 0, 1] 0 (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The hexagonal antiprism: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1] θ, polyEval [0] θ, polyEval [0, -1] θ],
    ![polyEval [1/2] θ, polyEval [1/2, 0, 2] θ, polyEval [0, -1] θ],
    ![polyEval [-1/2] θ, polyEval [1/2, 0, 2] θ, polyEval [0, -1] θ],
    ![polyEval [-1] θ, polyEval [0] θ, polyEval [0, -1] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2, 0, -2] θ, polyEval [0, -1] θ],
    ![polyEval [1/2] θ, polyEval [-1/2, 0, -2] θ, polyEval [0, -1] θ],
    ![polyEval [1/2, 0, 2] θ, polyEval [1/2] θ, polyEval [0, 1] θ],
    ![polyEval [0] θ, polyEval [1] θ, polyEval [0, 1] θ],
    ![polyEval [-1/2, 0, -2] θ, polyEval [1/2] θ, polyEval [0, 1] θ],
    ![polyEval [-1/2, 0, -2] θ, polyEval [-1/2] θ, polyEval [0, 1] θ],
    ![polyEval [0] θ, polyEval [-1] θ, polyEval [0, 1] θ],
    ![polyEval [1/2, 0, 2] θ, polyEval [-1/2] θ, polyEval [0, 1] θ]].toFinset

end Nieuwland.Antiprism.HexagonalAntiprism
