import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The snub disphenoid

The polyhedron `Johnson.SnubDisphenoid.polyhedron`: the convex hull of 8 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.SnubDisphenoid

/-- `θ`: the largest root of
`-1/128 + 1/8 * x ^ 2 + 11/8 * x ^ 4 + x ^ 6`
in the interval `(0, 3/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/128, 0, 1/8, 0, 11/8, 0, 1] 0 (3/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The snub disphenoid: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [1/2] θ, polyEval [0] θ, polyEval [0, -13/4, 0, -13, 0, -8] θ],
    ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [0, -13/4, 0, -13, 0, -8] θ],
    ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, 13/4, 0, 13, 0, 8] θ],
    ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, 13/4, 0, 13, 0, 8] θ],
    ![polyEval [1/4, 0, 9, 0, 8] θ, polyEval [0] θ, polyEval [0, 1] θ],
    ![polyEval [-1/4, 0, -9, 0, -8] θ, polyEval [0] θ, polyEval [0, 1] θ],
    ![polyEval [0] θ, polyEval [1/4, 0, 9, 0, 8] θ, polyEval [0, -1] θ],
    ![polyEval [0] θ, polyEval [-1/4, 0, -9, 0, -8] θ, polyEval [0, -1] θ]].toFinset

end Nieuwland.Johnson.SnubDisphenoid
