import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The sphenocorona

The polyhedron `Johnson.Sphenocorona.polyhedron`: the convex hull of 10 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.Sphenocorona

/-- `θ`: the largest root of
`1/16 - 1/150 * x ^ 2 - 397/450 * x ^ 4 - 2/75 * x ^ 6 + x ^ 8`
in the interval `(3/4, 9/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/16, 0, -1/150, 0, -397/450, 0, -2/75, 0, 1] (3/4) (9/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The sphenocorona: the convex hull of these 10 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [2681/4320, 0, -22249/6480, 0, -1289/1080, 0, 205/36] θ, polyEval [1/2] θ, polyEval [0] θ],
    ![polyEval [2681/4320, 0, -22249/6480, 0, -1289/1080, 0, 205/36] θ, polyEval [-1/2] θ, polyEval [0] θ],
    ![polyEval [-2681/4320, 0, 22249/6480, 0, 1289/1080, 0, -205/36] θ, polyEval [1/2] θ, polyEval [0] θ],
    ![polyEval [-2681/4320, 0, 22249/6480, 0, 1289/1080, 0, -205/36] θ, polyEval [-1/2] θ, polyEval [0] θ],
    ![polyEval [1/2] θ, polyEval [0] θ, polyEval [0, 7343/21600, 0, 35423/32400, 0, 5893/5400, 0, -67/36] θ],
    ![polyEval [-1/2] θ, polyEval [0] θ, polyEval [0, 7343/21600, 0, 35423/32400, 0, 5893/5400, 0, -67/36] θ],
    ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, -4/75, 0, -1588/225, 0, -16/75, 0, 8] θ],
    ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, -4/75, 0, -1588/225, 0, -16/75, 0, 8] θ],
    ![polyEval [0] θ, polyEval [23/32, 0, -65/16, 0, -29/24, 0, 25/4] θ, polyEval [0, 71/75, 0, -1588/225, 0, -16/75, 0, 8] θ],
    ![polyEval [0] θ, polyEval [-23/32, 0, 65/16, 0, 29/24, 0, -25/4] θ, polyEval [0, 71/75, 0, -1588/225, 0, -16/75, 0, 8] θ]].toFinset

end Nieuwland.Johnson.Sphenocorona
