import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The snub dodecahedron laevo

The polyhedron `Archimedean.SnubDodecahedronLaevo.polyhedron`: the convex hull of 60 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Archimedean.SnubDodecahedronLaevo

/-- `θ`: the largest root of
`-1 + 2 * x + 4 * x ^ 2 - x ^ 3 - 4 * x ^ 4 + x ^ 6`
in the interval `(3431/2000, 4289/2500)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1, 2, 4, -1, -4, 0, 1] (3431/2000) (4289/2500)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The snub dodecahedron laevo: the convex hull of these 60 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, -2] θ, polyEval [-2, 0, 2] θ],
    ![polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, 2] θ, polyEval [2, 0, -2] θ],
    ![polyEval [-4, -8, 2, 8, 0, -2] θ, polyEval [-2, 0, 4, 0, -2] θ, polyEval [2, 2, -2, -2] θ],
    ![polyEval [-4, -8, 2, 8, 0, -2] θ, polyEval [2, 0, -4, 0, 2] θ, polyEval [-2, -2, 2, 2] θ],
    ![polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval [-2] θ, polyEval [-2, -4, -2, 2, 2] θ],
    ![polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval [2] θ, polyEval [2, 4, 2, -2, -2] θ],
    ![polyEval [-4, -4, 2, 2] θ, polyEval [-4, -4, 6, 6, -2, -2] θ, polyEval [0, -2, 0, 2] θ],
    ![polyEval [-4, -4, 2, 2] θ, polyEval [4, 4, -6, -6, 2, 2] θ, polyEval [0, 2, 0, -2] θ],
    ![polyEval [-4, -4, 2, 6, 0, -2] θ, polyEval [0, -4, -4, 2, 2] θ, polyEval [4, 2, -2, -2] θ],
    ![polyEval [-4, -4, 2, 6, 0, -2] θ, polyEval [0, 4, 4, -2, -2] θ, polyEval [-4, -2, 2, 2] θ],
    ![polyEval [-4, -4, 6, 6, -2, -2] θ, polyEval [0, -2, 0, 2] θ, polyEval [-4, -4, 2, 2] θ],
    ![polyEval [-4, -4, 6, 6, -2, -2] θ, polyEval [0, 2, 0, -2] θ, polyEval [4, 4, -2, -2] θ],
    ![polyEval [-4, -2, 2, 2] θ, polyEval [-4, -4, 2, 6, 0, -2] θ, polyEval [0, 4, 4, -2, -2] θ],
    ![polyEval [-4, -2, 2, 2] θ, polyEval [4, 4, -2, -6, 0, 2] θ, polyEval [0, -4, -4, 2, 2] θ],
    ![polyEval [-2, -4, -2, 2, 2] θ, polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval [-2] θ],
    ![polyEval [-2, -4, -2, 2, 2] θ, polyEval [4, 6, -2, -8, 0, 2] θ, polyEval [2] θ],
    ![polyEval [-2, -2, 2, 2] θ, polyEval [-4, -8, 2, 8, 0, -2] θ, polyEval [2, 0, -4, 0, 2] θ],
    ![polyEval [-2, -2, 2, 2] θ, polyEval [4, 8, -2, -8, 0, 2] θ, polyEval [-2, 0, 4, 0, -2] θ],
    ![polyEval [-2] θ, polyEval [-2, -4, -2, 2, 2] θ, polyEval [-4, -6, 2, 8, 0, -2] θ],
    ![polyEval [-2] θ, polyEval [2, 4, 2, -2, -2] θ, polyEval [4, 6, -2, -8, 0, 2] θ],
    ![polyEval [-2, 0, 2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, -2] θ],
    ![polyEval [-2, 0, 2] θ, polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, 2] θ],
    ![polyEval [-2, 0, 4, 0, -2] θ, polyEval [-2, -2, 2, 2] θ, polyEval [4, 8, -2, -8, 0, 2] θ],
    ![polyEval [-2, 0, 4, 0, -2] θ, polyEval [2, 2, -2, -2] θ, polyEval [-4, -8, 2, 8, 0, -2] θ],
    ![polyEval [0, -4, -4, 2, 2] θ, polyEval [-4, -2, 2, 2] θ, polyEval [4, 4, -2, -6, 0, 2] θ],
    ![polyEval [0, -4, -4, 2, 2] θ, polyEval [4, 2, -2, -2] θ, polyEval [-4, -4, 2, 6, 0, -2] θ],
    ![polyEval [0, -2] θ, polyEval [-2, 0, 2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ],
    ![polyEval [0, -2] θ, polyEval [2, 0, -2] θ, polyEval [6, 4, -6, -6, 2, 2] θ],
    ![polyEval [0, -2, 0, 2] θ, polyEval [-4, -4, 2, 2] θ, polyEval [-4, -4, 6, 6, -2, -2] θ],
    ![polyEval [0, -2, 0, 2] θ, polyEval [4, 4, -2, -2] θ, polyEval [4, 4, -6, -6, 2, 2] θ],
    ![polyEval [0, 2, 0, -2] θ, polyEval [-4, -4, 2, 2] θ, polyEval [4, 4, -6, -6, 2, 2] θ],
    ![polyEval [0, 2, 0, -2] θ, polyEval [4, 4, -2, -2] θ, polyEval [-4, -4, 6, 6, -2, -2] θ],
    ![polyEval [0, 2] θ, polyEval [-2, 0, 2] θ, polyEval [6, 4, -6, -6, 2, 2] θ],
    ![polyEval [0, 2] θ, polyEval [2, 0, -2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ],
    ![polyEval [0, 4, 4, -2, -2] θ, polyEval [-4, -2, 2, 2] θ, polyEval [-4, -4, 2, 6, 0, -2] θ],
    ![polyEval [0, 4, 4, -2, -2] θ, polyEval [4, 2, -2, -2] θ, polyEval [4, 4, -2, -6, 0, 2] θ],
    ![polyEval [2, 0, -4, 0, 2] θ, polyEval [-2, -2, 2, 2] θ, polyEval [-4, -8, 2, 8, 0, -2] θ],
    ![polyEval [2, 0, -4, 0, 2] θ, polyEval [2, 2, -2, -2] θ, polyEval [4, 8, -2, -8, 0, 2] θ],
    ![polyEval [2, 0, -2] θ, polyEval [-6, -4, 6, 6, -2, -2] θ, polyEval [0, 2] θ],
    ![polyEval [2, 0, -2] θ, polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, -2] θ],
    ![polyEval [2] θ, polyEval [-2, -4, -2, 2, 2] θ, polyEval [4, 6, -2, -8, 0, 2] θ],
    ![polyEval [2] θ, polyEval [2, 4, 2, -2, -2] θ, polyEval [-4, -6, 2, 8, 0, -2] θ],
    ![polyEval [2, 2, -2, -2] θ, polyEval [-4, -8, 2, 8, 0, -2] θ, polyEval [-2, 0, 4, 0, -2] θ],
    ![polyEval [2, 2, -2, -2] θ, polyEval [4, 8, -2, -8, 0, 2] θ, polyEval [2, 0, -4, 0, 2] θ],
    ![polyEval [2, 4, 2, -2, -2] θ, polyEval [-4, -6, 2, 8, 0, -2] θ, polyEval [2] θ],
    ![polyEval [2, 4, 2, -2, -2] θ, polyEval [4, 6, -2, -8, 0, 2] θ, polyEval [-2] θ],
    ![polyEval [4, 2, -2, -2] θ, polyEval [-4, -4, 2, 6, 0, -2] θ, polyEval [0, -4, -4, 2, 2] θ],
    ![polyEval [4, 2, -2, -2] θ, polyEval [4, 4, -2, -6, 0, 2] θ, polyEval [0, 4, 4, -2, -2] θ],
    ![polyEval [4, 4, -6, -6, 2, 2] θ, polyEval [0, -2, 0, 2] θ, polyEval [4, 4, -2, -2] θ],
    ![polyEval [4, 4, -6, -6, 2, 2] θ, polyEval [0, 2, 0, -2] θ, polyEval [-4, -4, 2, 2] θ],
    ![polyEval [4, 4, -2, -6, 0, 2] θ, polyEval [0, -4, -4, 2, 2] θ, polyEval [-4, -2, 2, 2] θ],
    ![polyEval [4, 4, -2, -6, 0, 2] θ, polyEval [0, 4, 4, -2, -2] θ, polyEval [4, 2, -2, -2] θ],
    ![polyEval [4, 4, -2, -2] θ, polyEval [-4, -4, 6, 6, -2, -2] θ, polyEval [0, 2, 0, -2] θ],
    ![polyEval [4, 4, -2, -2] θ, polyEval [4, 4, -6, -6, 2, 2] θ, polyEval [0, -2, 0, 2] θ],
    ![polyEval [4, 6, -2, -8, 0, 2] θ, polyEval [-2] θ, polyEval [2, 4, 2, -2, -2] θ],
    ![polyEval [4, 6, -2, -8, 0, 2] θ, polyEval [2] θ, polyEval [-2, -4, -2, 2, 2] θ],
    ![polyEval [4, 8, -2, -8, 0, 2] θ, polyEval [-2, 0, 4, 0, -2] θ, polyEval [-2, -2, 2, 2] θ],
    ![polyEval [4, 8, -2, -8, 0, 2] θ, polyEval [2, 0, -4, 0, 2] θ, polyEval [2, 2, -2, -2] θ],
    ![polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, -2] θ, polyEval [2, 0, -2] θ],
    ![polyEval [6, 4, -6, -6, 2, 2] θ, polyEval [0, 2] θ, polyEval [-2, 0, 2] θ]].toFinset

end Nieuwland.Archimedean.SnubDodecahedronLaevo
