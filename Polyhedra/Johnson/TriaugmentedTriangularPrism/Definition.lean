import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The triaugmented triangular prism

The polyhedron `Johnson.TriaugmentedTriangularPrism.polyhedron`: the convex hull of 9 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.TriaugmentedTriangularPrism

/-- `θ`: the largest root of
`1/256 - 5/8 * x ^ 2 + x ^ 4`
in the interval `(1/2, 5/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/256, 0, -5/8, 0, 1] (1/2) (5/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The triaugmented triangular prism: the convex hull of these 9 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, -11/3, 0, 16/3] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [0, 22/3, 0, -32/3] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [0, 22/3, 0, -32/3] θ, polyEval [-1/2] θ],
    ![polyEval [-3/8, 0, 2] θ, polyEval [0, -8/3, 0, 16/3] θ, polyEval [0] θ],
    ![polyEval [3/8, 0, -2] θ, polyEval [0, -8/3, 0, 16/3] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [0, 16/3, 0, -32/3] θ, polyEval [0] θ]].toFinset

end Nieuwland.Johnson.TriaugmentedTriangularPrism
