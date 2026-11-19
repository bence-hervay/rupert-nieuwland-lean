import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The gyroelongated square cupola

The polyhedron `Johnson.GyroelongatedSquareCupola.polyhedron`: the convex hull of 20 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.GyroelongatedSquareCupola

/-- `θ`: the largest root of
`-1/512 + 1/16 * x ^ 2 - 1/2 * x ^ 4 + x ^ 6 + x ^ 8`
in the interval `(13/32, 29/64)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/512, 0, 1/16, 0, -1/2, 0, 1, 0, 1] (13/32) (29/64)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The gyroelongated square cupola: the convex hull of these 20 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [1/2] θ, polyEval [0, 1] θ],
    ![polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [-1/2] θ, polyEval [0, 1] θ],
    ![polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [1/2] θ, polyEval [0, 1] θ],
    ![polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [-1/2] θ, polyEval [0, 1] θ],
    ![polyEval [1/2] θ, polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [0, 1] θ],
    ![polyEval [1/2] θ, polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [0, 1] θ],
    ![polyEval [-1/2] θ, polyEval [5/2, 0, -72, 0, 304, 0, 256] θ, polyEval [0, 1] θ],
    ![polyEval [-1/2] θ, polyEval [-5/2, 0, 72, 0, -304, 0, -256] θ, polyEval [0, 1] θ],
    ![polyEval [5, 0, -116, 0, 448, 0, 384] θ, polyEval [0] θ, polyEval [0, -1] θ],
    ![polyEval [-5, 0, 116, 0, -448, 0, -384] θ, polyEval [0] θ, polyEval [0, -1] θ],
    ![polyEval [0] θ, polyEval [5, 0, -116, 0, 448, 0, 384] θ, polyEval [0, -1] θ],
    ![polyEval [0] θ, polyEval [-5, 0, 116, 0, -448, 0, -384] θ, polyEval [0, -1] θ],
    ![polyEval [0, 0, -12, 0, 80, 0, 64] θ, polyEval [0, 0, -12, 0, 80, 0, 64] θ, polyEval [0, -1] θ],
    ![polyEval [0, 0, -12, 0, 80, 0, 64] θ, polyEval [0, 0, 12, 0, -80, 0, -64] θ, polyEval [0, -1] θ],
    ![polyEval [0, 0, 12, 0, -80, 0, -64] θ, polyEval [0, 0, -12, 0, 80, 0, 64] θ, polyEval [0, -1] θ],
    ![polyEval [0, 0, 12, 0, -80, 0, -64] θ, polyEval [0, 0, 12, 0, -80, 0, -64] θ, polyEval [0, -1] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [2, 1, -72, 0, 304, 0, 256] θ]].toFinset

end Nieuwland.Johnson.GyroelongatedSquareCupola
