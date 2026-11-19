import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The augmented pentagonal prism

The polyhedron `Johnson.AugmentedPentagonalPrism.polyhedron`: the convex hull of 11 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Johnson.AugmentedPentagonalPrism

/-- `θ`: the largest root of
`1/256 - 11/32 * x ^ 2 + 79/16 * x ^ 4 - 9/2 * x ^ 6 + x ^ 8`
in the interval `(3/2, 15/8)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [1/256, 0, -11/32, 0, 79/16, 0, -9/2, 0, 1] (3/2) (15/8)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The augmented pentagonal prism: the convex hull of these 11 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [-15/22, 0, 292/11, 0, -280/11, 0, 64/11] θ, polyEval [1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ],
    ![polyEval [-15/22, 0, 292/11, 0, -280/11, 0, 64/11] θ, polyEval [-1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ],
    ![polyEval [15/22, 0, -292/11, 0, 280/11, 0, -64/11] θ, polyEval [1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ],
    ![polyEval [15/22, 0, -292/11, 0, 280/11, 0, -64/11] θ, polyEval [-1/2] θ, polyEval [0, 281/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ],
    ![polyEval [1/2] θ, polyEval [1/2] θ, polyEval [0, -303/110, 0, 5454/55, 0, -5128/55, 0, 1152/55] θ],
    ![polyEval [1/2] θ, polyEval [-1/2] θ, polyEval [0, -303/110, 0, 5454/55, 0, -5128/55, 0, 1152/55] θ],
    ![polyEval [-1/2] θ, polyEval [1/2] θ, polyEval [0, -303/110, 0, 5454/55, 0, -5128/55, 0, 1152/55] θ],
    ![polyEval [-1/2] θ, polyEval [-1/2] θ, polyEval [0, -303/110, 0, 5454/55, 0, -5128/55, 0, 1152/55] θ],
    ![polyEval [0] θ, polyEval [1/2] θ, polyEval [0, -259/55, 0, 1184/55, 0, -928/55, 0, 192/55] θ],
    ![polyEval [0] θ, polyEval [-1/2] θ, polyEval [0, -259/55, 0, 1184/55, 0, -928/55, 0, 192/55] θ],
    ![polyEval [0] θ, polyEval [0] θ, polyEval [0, 336/55, 0, -6046/55, 0, 5592/55, 0, -1248/55] θ]].toFinset

end Nieuwland.Johnson.AugmentedPentagonalPrism
