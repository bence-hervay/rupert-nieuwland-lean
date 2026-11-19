import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The metabiaugmented hexagonal prism

The polyhedron `Johnson.MetabiaugmentedHexagonalPrism.polyhedron`: the convex hull of 14 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.MetabiaugmentedHexagonalPrism

/-- `θ`: the largest root of
`1/256 - 5/8 * x ^ 2 + x ^ 4`
in the interval `(1/2, 5/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/256, 0, -5/8, 0, 1] (1/2) (5/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The metabiaugmented hexagonal prism: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1] θ, polyEval [1/2] θ, polyEval [0] θ],
    ![polyEval [1] θ, polyEval [-1/2] θ, polyEval [0] θ],
    ![polyEval [-1] θ, polyEval [1/2] θ, polyEval [0] θ],
    ![polyEval [-1] θ, polyEval [-1/2] θ, polyEval [0] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, 11, 0, -16] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -11, 0, 16] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, 11, 0, -16] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -11, 0, 16] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, 11, 0, -16] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -11, 0, 16] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, 11, 0, -16] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -11, 0, 16] θ],
    ![polyEval [1/8, 0, 2] θ, polyEval [0] θ, polyEval [0, 1] θ],
    ![polyEval [-1/8, 0, -2] θ, polyEval [0] θ, polyEval [0, 1] θ]].toFinset

end Nieuwland.Johnson.MetabiaugmentedHexagonalPrism
