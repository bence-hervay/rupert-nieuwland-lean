import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The dodecagonal prism

The polyhedron `Prism.DodecagonalPrism.polyhedron`: the convex hull of 24 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Prism.DodecagonalPrism

/-- `θ`: the largest root of
`1 - 4 * x ^ 2 + x ^ 4`
in the interval `(1, 5/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1, 0, -4, 0, 1] 1 (5/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The dodecagonal prism: the convex hull of these 24 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, 1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [0, 1] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, 1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, -1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [0, -1] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, -1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, 1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [0, 1] θ, polyEval [1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [0, -1, 0, 1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, 1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [0, 1, 0, -1/2] θ, polyEval [0, -1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [0, -1] θ, polyEval [1/2] θ],
    ![polyEval [0, 1/2] θ, polyEval [0, 1, 0, -1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -1, 0, 1/2] θ, polyEval [0, -1/2] θ, polyEval [1/2] θ]].toFinset

end Nieuwland.Prism.DodecagonalPrism
