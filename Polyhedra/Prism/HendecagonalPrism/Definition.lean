import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The hendecagonal prism

The polyhedron `Prism.HendecagonalPrism.polyhedron`: the convex hull of 22 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Prism.HendecagonalPrism

/-- `θ`: the largest root of
`-1/11 + x ^ 2 - 4 * x ^ 4 + 7 * x ^ 6 - 5 * x ^ 8 + x ^ 10`
in the interval `(1, 5/2)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/11, 0, 1, 0, -4, 0, 7, 0, -5, 0, 1] 1 (5/2)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The hendecagonal prism: the convex hull of these 22 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [-1/2] θ],
    ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [21, 0, -165, 0, 825/2, 0, -715/2, 0, 77] θ, polyEval [-1/2] θ],
    ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [-24, 0, 363/2, 0, -869/2, 0, 363, 0, -77] θ, polyEval [-1/2] θ],
    ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval [27/2, 0, -187/2, 0, 407/2, 0, -319/2, 0, 33] θ, polyEval [-1/2] θ],
    ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [-4, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -21, 0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -21, 0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [-1/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [4, 0, -22, 0, 77/2, 0, -55/2, 0, 11/2] θ, polyEval [-1/2] θ],
    ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval [-27/2, 0, 187/2, 0, -407/2, 0, 319/2, 0, -33] θ, polyEval [-1/2] θ],
    ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [24, 0, -363/2, 0, 869/2, 0, -363, 0, 77] θ, polyEval [-1/2] θ],
    ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [-21, 0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [-1/2] θ],
    ![polyEval [0, 1] θ, polyEval [0] θ, polyEval [1/2] θ],
    ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [21, 0, -165, 0, 825/2, 0, -715/2, 0, 77] θ, polyEval [1/2] θ],
    ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [-24, 0, 363/2, 0, -869/2, 0, 363, 0, -77] θ, polyEval [1/2] θ],
    ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval [27/2, 0, -187/2, 0, 407/2, 0, -319/2, 0, 33] θ, polyEval [1/2] θ],
    ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [-4, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -21, 0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -21, 0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [-1/2] θ, polyEval [1/2] θ],
    ![polyEval [0, 45, 0, -693/2, 0, 847, 0, -1441/2, 0, 154] θ, polyEval [4, 0, -22, 0, 77/2, 0, -55/2, 0, 11/2] θ, polyEval [1/2] θ],
    ![polyEval [0, -75/2, 0, 275, 0, -638, 0, 1045/2, 0, -110] θ, polyEval [-27/2, 0, 187/2, 0, -407/2, 0, 319/2, 0, -33] θ, polyEval [1/2] θ],
    ![polyEval [0, 35/2, 0, -231/2, 0, 242, 0, -187, 0, 77/2] θ, polyEval [24, 0, -363/2, 0, 869/2, 0, -363, 0, 77] θ, polyEval [1/2] θ],
    ![polyEval [0, -9/2, 0, 22, 0, -77/2, 0, 55/2, 0, -11/2] θ, polyEval [-21, 0, 165, 0, -825/2, 0, 715/2, 0, -77] θ, polyEval [1/2] θ]].toFinset

end Nieuwland.Prism.HendecagonalPrism
