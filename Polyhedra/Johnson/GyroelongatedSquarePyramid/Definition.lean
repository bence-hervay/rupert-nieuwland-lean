import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The gyroelongated square pyramid

The polyhedron `Johnson.GyroelongatedSquarePyramid.polyhedron`: the convex hull of 9 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.GyroelongatedSquarePyramid

/-- `θ`: the largest root of
`-1/32 + x ^ 4`
in the interval `(0, 3/4)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/32, 0, 0, 0, 1] 0 (3/4)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The gyroelongated square pyramid: the convex hull of these 9 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0, 0, 4] θ, polyEval [0, 1] θ],
    ![polyEval [0] θ, polyEval [0, 0, -4] θ, polyEval [0, 1] θ],
    ![polyEval [0, 0, 4] θ, polyEval [0] θ, polyEval [0, 1] θ],
    ![polyEval [0, 0, -4] θ, polyEval [0] θ, polyEval [0, 1] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -1] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -1] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -1] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 1, 4] θ]].toFinset

end Nieuwland.Johnson.GyroelongatedSquarePyramid
