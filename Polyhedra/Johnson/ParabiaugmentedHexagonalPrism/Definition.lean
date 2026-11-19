import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The parabiaugmented hexagonal prism

The polyhedron `Johnson.ParabiaugmentedHexagonalPrism.polyhedron`: the convex hull of 14 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.ParabiaugmentedHexagonalPrism

/-- `θ`: the largest root of
`25/4 - 7 * x ^ 2 + x ^ 4`
in the interval `(3/2, 3)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [25/4, 0, -7, 0, 1] (3/2) 3

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The parabiaugmented hexagonal prism: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0, 19/20, 0, -1/10] θ, polyEval [1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 19/20, 0, -1/10] θ, polyEval [1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 19/20, 0, -1/10] θ, polyEval [-1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 19/20, 0, -1/10] θ, polyEval [-1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -19/20, 0, 1/10] θ, polyEval [1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -19/20, 0, 1/10] θ, polyEval [1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -19/20, 0, 1/10] θ, polyEval [-1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -19/20, 0, 1/10] θ, polyEval [-1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [1] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [1] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [-1] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [-1] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1/20, 0, 1/10] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [0, -1/20, 0, -1/10] θ, polyEval [0] θ, polyEval [0] θ]].toFinset

end Nieuwland.Johnson.ParabiaugmentedHexagonalPrism
