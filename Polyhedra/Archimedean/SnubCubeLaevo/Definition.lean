import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The snub cube laevo

The polyhedron `Archimedean.SnubCubeLaevo.polyhedron`: the convex hull of 24 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Archimedean.SnubCubeLaevo

/-- `θ`: the largest root of
`-1 - x - x ^ 2 + x ^ 3`
in the interval `(9/5, 19/10)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1, -1, -1, 1] (9/5) (19/10)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The snub cube laevo: the convex hull of these 24 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1] θ, polyEval [-1, -1, 1] θ, polyEval [0, 1] θ],
    ![polyEval [-1] θ, polyEval [1, 1, -1] θ, polyEval [0, 1] θ],
    ![polyEval [-1] θ, polyEval [-1, -1, 1] θ, polyEval [0, -1] θ],
    ![polyEval [1] θ, polyEval [1, 1, -1] θ, polyEval [0, -1] θ],
    ![polyEval [-1, -1, 1] θ, polyEval [0, 1] θ, polyEval [1] θ],
    ![polyEval [1, 1, -1] θ, polyEval [0, -1] θ, polyEval [1] θ],
    ![polyEval [1, 1, -1] θ, polyEval [0, 1] θ, polyEval [-1] θ],
    ![polyEval [-1, -1, 1] θ, polyEval [0, -1] θ, polyEval [-1] θ],
    ![polyEval [0, 1] θ, polyEval [1] θ, polyEval [-1, -1, 1] θ],
    ![polyEval [0, -1] θ, polyEval [-1] θ, polyEval [-1, -1, 1] θ],
    ![polyEval [0, -1] θ, polyEval [1] θ, polyEval [1, 1, -1] θ],
    ![polyEval [0, 1] θ, polyEval [-1] θ, polyEval [1, 1, -1] θ],
    ![polyEval [-1] θ, polyEval [0, 1] θ, polyEval [-1, -1, 1] θ],
    ![polyEval [1] θ, polyEval [0, -1] θ, polyEval [-1, -1, 1] θ],
    ![polyEval [1] θ, polyEval [0, 1] θ, polyEval [1, 1, -1] θ],
    ![polyEval [-1] θ, polyEval [0, -1] θ, polyEval [1, 1, -1] θ],
    ![polyEval [0, -1] θ, polyEval [-1, -1, 1] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [1, 1, -1] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [-1, -1, 1] θ, polyEval [-1] θ],
    ![polyEval [0, -1] θ, polyEval [1, 1, -1] θ, polyEval [-1] θ],
    ![polyEval [1, 1, -1] θ, polyEval [1] θ, polyEval [0, 1] θ],
    ![polyEval [-1, -1, 1] θ, polyEval [-1] θ, polyEval [0, 1] θ],
    ![polyEval [-1, -1, 1] θ, polyEval [1] θ, polyEval [0, -1] θ],
    ![polyEval [1, 1, -1] θ, polyEval [-1] θ, polyEval [0, -1] θ]].toFinset

end Nieuwland.Archimedean.SnubCubeLaevo
