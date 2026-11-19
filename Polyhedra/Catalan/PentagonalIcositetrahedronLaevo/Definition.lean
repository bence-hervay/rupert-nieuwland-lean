import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The pentagonal icositetrahedron laevo

The polyhedron `Catalan.PentagonalIcositetrahedronLaevo.polyhedron`: the convex hull of 38 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Catalan.PentagonalIcositetrahedronLaevo

/-- `θ`: the largest root of
`-1 - x - 3 * x ^ 2 + x ^ 3`
in the interval `(5/2, 4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1, -1, -3, 1] (5/2) 4

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The pentagonal icositetrahedron laevo: the convex hull of these 38 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1/2, 0, -1/2] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1/2, 0, 1/2] θ],
    ![polyEval [-1/2, 0, -1/2] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [1/2, 0, 1/2] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [-1/2, 0, -1/2] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [1/2, 0, 1/2] θ, polyEval [0] θ],
    ![polyEval [0, -1] θ, polyEval [1] θ, polyEval [0, 2, -1] θ],
    ![polyEval [0, -1] θ, polyEval [-1] θ, polyEval [0, -2, 1] θ],
    ![polyEval [0, 1] θ, polyEval [-1] θ, polyEval [0, 2, -1] θ],
    ![polyEval [0, 1] θ, polyEval [1] θ, polyEval [0, -2, 1] θ],
    ![polyEval [0, 2, -1] θ, polyEval [0, 1] θ, polyEval [-1] θ],
    ![polyEval [0, 2, -1] θ, polyEval [0, -1] θ, polyEval [1] θ],
    ![polyEval [0, -2, 1] θ, polyEval [0, -1] θ, polyEval [-1] θ],
    ![polyEval [0, -2, 1] θ, polyEval [0, 1] θ, polyEval [1] θ],
    ![polyEval [-1] θ, polyEval [0, -2, 1] θ, polyEval [0, -1] θ],
    ![polyEval [-1] θ, polyEval [0, 2, -1] θ, polyEval [0, 1] θ],
    ![polyEval [1] θ, polyEval [0, 2, -1] θ, polyEval [0, -1] θ],
    ![polyEval [1] θ, polyEval [0, -2, 1] θ, polyEval [0, 1] θ],
    ![polyEval [-1] θ, polyEval [0, -1] θ, polyEval [0, 2, -1] θ],
    ![polyEval [-1] θ, polyEval [0, 1] θ, polyEval [0, -2, 1] θ],
    ![polyEval [1] θ, polyEval [0, 1] θ, polyEval [0, 2, -1] θ],
    ![polyEval [1] θ, polyEval [0, -1] θ, polyEval [0, -2, 1] θ],
    ![polyEval [0, 2, -1] θ, polyEval [-1] θ, polyEval [0, -1] θ],
    ![polyEval [0, 2, -1] θ, polyEval [1] θ, polyEval [0, 1] θ],
    ![polyEval [0, -2, 1] θ, polyEval [1] θ, polyEval [0, -1] θ],
    ![polyEval [0, -2, 1] θ, polyEval [-1] θ, polyEval [0, 1] θ],
    ![polyEval [0, -1] θ, polyEval [0, 2, -1] θ, polyEval [-1] θ],
    ![polyEval [0, -1] θ, polyEval [0, -2, 1] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [0, -2, 1] θ, polyEval [-1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 2, -1] θ, polyEval [1] θ],
    ![polyEval [0, -1] θ, polyEval [0, -1] θ, polyEval [0, -1] θ],
    ![polyEval [0, -1] θ, polyEval [0, -1] θ, polyEval [0, 1] θ],
    ![polyEval [0, -1] θ, polyEval [0, 1] θ, polyEval [0, -1] θ],
    ![polyEval [0, -1] θ, polyEval [0, 1] θ, polyEval [0, 1] θ],
    ![polyEval [0, 1] θ, polyEval [0, -1] θ, polyEval [0, -1] θ],
    ![polyEval [0, 1] θ, polyEval [0, -1] θ, polyEval [0, 1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 1] θ, polyEval [0, -1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 1] θ, polyEval [0, 1] θ]].toFinset

end Nieuwland.Catalan.PentagonalIcositetrahedronLaevo
