import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The augmented tridiminished icosahedron

The polyhedron `Johnson.AugmentedTridiminishedIcosahedron.polyhedron`: the convex hull of 10 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.AugmentedTridiminishedIcosahedron

/-- `θ`: the largest root of
`-31/144 + 19/18 * x - 1/18 * x ^ 2 - 2 * x ^ 3 + x ^ 4`
in the interval `(1, 5/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-31/144, 19/18, -1/18, -2, 1] 1 (5/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The augmented tridiminished icosahedron: the convex hull of these 10 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [-43/64, 41/32, 27/16, -9/8] θ, polyEval [1/2] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [-43/64, 41/32, 27/16, -9/8] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [0] θ, polyEval [-43/64, 41/32, 27/16, -9/8] θ],
    ![polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [1/2] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ],
    ![polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [-1/2] θ, polyEval [0] θ],
    ![polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [43/64, -41/32, -27/16, 9/8] θ],
    ![polyEval [43/64, -9/32, -27/16, 9/8] θ, polyEval [43/64, -9/32, -27/16, 9/8] θ, polyEval [43/64, -9/32, -27/16, 9/8] θ]].toFinset

end Nieuwland.Johnson.AugmentedTridiminishedIcosahedron
