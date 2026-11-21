import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The octagonal trapezohedron

The polyhedron `Other.OctagonalTrapezohedron.polyhedron`: the convex hull of 18 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Other.OctagonalTrapezohedron

/-- `θ`: the largest root of
`-2 + 40 * x ^ 2 - 248 * x ^ 4 + 480 * x ^ 6 + x ^ 8`
in the interval `(9/32, 3/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-2, 0, 40, 0, -248, 0, 480, 0, 1] (9/32) (3/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The octagonal trapezohedron: the convex hull of these 18 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0] θ, polyEval [0] θ, polyEval [-1] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [1] θ],
    ![polyEval [0, 1] θ, polyEval [0, 159/17, 0, -2000/17, 0, 4801/17, 0, 10/17] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0, 1670/119, 0, -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [0, 1670/119, 0, -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, 159/17, 0, -2000/17, 0, 4801/17, 0, 10/17] θ, polyEval [0, 1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0] θ, polyEval [0, -1290/119, 0, 21058/119, 0, -9810/17, 0, -143/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, -159/17, 0, 2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [0, 1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0, -1670/119, 0, 22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [0, 1670/119, 0, -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, -1] θ, polyEval [0, 159/17, 0, -2000/17, 0, 4801/17, 0, 10/17] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0, 1290/119, 0, -21058/119, 0, 9810/17, 0, 143/119] θ, polyEval [0] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, -1] θ, polyEval [0, -159/17, 0, 2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0, -1670/119, 0, 22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [0, -1670/119, 0, 22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, -159/17, 0, 2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [0, -1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0] θ, polyEval [0, 1290/119, 0, -21058/119, 0, 9810/17, 0, 143/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, 159/17, 0, -2000/17, 0, 4801/17, 0, 10/17] θ, polyEval [0, -1] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0, 1670/119, 0, -22467/119, 0, 9535/17, 0, 139/119] θ, polyEval [0, -1670/119, 0, 22467/119, 0, -9535/17, 0, -139/119] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ],
    ![polyEval [0, 1] θ, polyEval [0, -159/17, 0, 2000/17, 0, -4801/17, 0, -10/17] θ, polyEval [-141/119, 0, 2612/119, 0, -1784/17, 0, -26/119] θ],
    ![polyEval [0, -1290/119, 0, 21058/119, 0, -9810/17, 0, -143/119] θ, polyEval [0] θ, polyEval [141/119, 0, -2612/119, 0, 1784/17, 0, 26/119] θ]].toFinset

end Nieuwland.Other.OctagonalTrapezohedron
