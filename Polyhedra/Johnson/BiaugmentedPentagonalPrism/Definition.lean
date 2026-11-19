import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The biaugmented pentagonal prism

The polyhedron `Johnson.BiaugmentedPentagonalPrism.polyhedron`: the convex hull of 12 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.BiaugmentedPentagonalPrism

/-- `θ`: the largest root of
`121/65536 - 119/2048 * x ^ 2 + 139/256 * x ^ 4 - 11/8 * x ^ 6 + x ^ 8`
in the interval `(5/8, 13/16)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [121/65536, 0, -119/2048, 0, 139/256, 0, -11/8, 0, 1] (5/8) (13/16)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The biaugmented pentagonal prism: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [19/2, 0, -1776/11, 0, 5248/11, 0, -4096/11] θ, polyEval [1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ],
    ![polyEval [19/2, 0, -1776/11, 0, 5248/11, 0, -4096/11] θ, polyEval [-1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ],
    ![polyEval [-19/2, 0, 1776/11, 0, -5248/11, 0, 4096/11] θ, polyEval [1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ],
    ![polyEval [-19/2, 0, 1776/11, 0, -5248/11, 0, 4096/11] θ, polyEval [-1/2] θ, polyEval [0, 1142/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -1533/55, 0, 25648/55, 0, -74496/55, 0, 57344/55] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -1533/55, 0, 25648/55, 0, -74496/55, 0, 57344/55] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -1533/55, 0, 25648/55, 0, -74496/55, 0, 57344/55] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -1533/55, 0, 25648/55, 0, -74496/55, 0, 57344/55] θ],
    ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, 782/55, 0, -11072/55, 0, 31744/55, 0, -24576/55] θ],
    ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, 782/55, 0, -11072/55, 0, 31744/55, 0, -24576/55] θ],
    ![polyEval [-4, 0, 798/11, 0, -2144/11, 0, 1536/11] θ, polyEval [0] θ, polyEval [0, 1087/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ],
    ![polyEval [4, 0, -798/11, 0, 2144/11, 0, -1536/11] θ, polyEval [0] θ, polyEval [0, 1087/55, 0, -20112/55, 0, 58624/55, 0, -4096/5] θ]].toFinset

end Nieuwland.Johnson.BiaugmentedPentagonalPrism
