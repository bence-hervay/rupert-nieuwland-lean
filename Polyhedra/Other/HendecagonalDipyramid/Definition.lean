import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The hendecagonal dipyramid

The polyhedron `Other.HendecagonalDipyramid.polyhedron`: the convex hull of 13 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.HendecagonalDipyramid

/-- `θ`: the largest root of
`-11/1024 + 55/256 * x ^ 2 - 77/64 * x ^ 4 + 11/4 * x ^ 6 - 11/4 * x ^ 8 + x ^ 10`
in the interval `(1/8, 1/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-11/1024, 0, 55/256, 0, -77/64, 0, 11/4, 0, -11/4, 0, 1] (1/8) (1/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The hendecagonal dipyramid: the convex hull of these 13 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [11/2, 0, -100, 0, 456, 0, -736, 0, 384] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, 8, 0, -80, 0, 192, 0, -128] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, 6, 0, -32, 0, 32] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -24, 0, 80, 0, -64] θ, polyEval [0, 0, 4, 0, -8] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -40, 0, 240, 0, -448, 0, 256] θ, polyEval [0, 0, 2] θ, polyEval [0] θ],
    ![polyEval [0, -10, 0, 160, 0, -672, 0, 1024, 0, -512] θ, polyEval [0] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -40, 0, 240, 0, -448, 0, 256] θ, polyEval [0, 0, -2] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -24, 0, 80, 0, -64] θ, polyEval [0, 0, -4, 0, 8] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -12, 0, 16] θ, polyEval [0, 0, -6, 0, 32, 0, -32] θ, polyEval [0] θ],
    ![polyEval [0, 1, 0, -4] θ, polyEval [0, 0, -8, 0, 80, 0, -192, 0, 128] θ, polyEval [0] θ],
    ![polyEval [0, 1] θ, polyEval [-11/2, 0, 100, 0, -456, 0, 736, 0, -384] θ, polyEval [0] θ]].toFinset

end Nieuwland.Other.HendecagonalDipyramid
