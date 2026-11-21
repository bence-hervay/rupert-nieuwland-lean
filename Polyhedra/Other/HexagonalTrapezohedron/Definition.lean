import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The hexagonal trapezohedron

The polyhedron `Other.HexagonalTrapezohedron.polyhedron`: the convex hull of 14 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.HexagonalTrapezohedron

/-- `θ`: the largest root of
`-18 + 114 * x ^ 2 + x ^ 4`
in the interval `(0, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-18, 0, 114, 0, 1] 0 (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The hexagonal trapezohedron: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 19/33, 0, 1/99] θ, polyEval [-1/11, 0, 4/33] θ],
    ![polyEval [0, 19/33, 0, 1/99] θ, polyEval [0, 1] θ, polyEval [1/11, 0, -4/33] θ],
    ![polyEval [0] θ, polyEval [0, 38/33, 0, 2/99] θ, polyEval [-1/11, 0, 4/33] θ],
    ![polyEval [0, -19/33, 0, -1/99] θ, polyEval [0, 1] θ, polyEval [1/11, 0, -4/33] θ],
    ![polyEval [0, -1] θ, polyEval [0, 19/33, 0, 1/99] θ, polyEval [-1/11, 0, 4/33] θ],
    ![polyEval [0, -38/33, 0, -2/99] θ, polyEval [0] θ, polyEval [1/11, 0, -4/33] θ],
    ![polyEval [0, -1] θ, polyEval [0, -19/33, 0, -1/99] θ, polyEval [-1/11, 0, 4/33] θ],
    ![polyEval [0, -19/33, 0, -1/99] θ, polyEval [0, -1] θ, polyEval [1/11, 0, -4/33] θ],
    ![polyEval [0] θ, polyEval [0, -38/33, 0, -2/99] θ, polyEval [-1/11, 0, 4/33] θ],
    ![polyEval [0, 19/33, 0, 1/99] θ, polyEval [0, -1] θ, polyEval [1/11, 0, -4/33] θ],
    ![polyEval [0, 1] θ, polyEval [0, -19/33, 0, -1/99] θ, polyEval [-1/11, 0, 4/33] θ],
    ![polyEval [0, 38/33, 0, 2/99] θ, polyEval [0] θ, polyEval [1/11, 0, -4/33] θ]].toFinset

end Nieuwland.Other.HexagonalTrapezohedron
