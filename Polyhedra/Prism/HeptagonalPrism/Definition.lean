import Definitions.Polyhedra
import Definitions.Polynomials

/-!
# The heptagonal prism

The polyhedron `Prism.HeptagonalPrism.polyhedron`: the convex hull of 14 points,
with coordinates in `ℚ(θ)` (`polyEval c θ` is `∑ cᵢ θⁱ`).
-/

namespace Nieuwland.Prism.HeptagonalPrism

/-- `θ`: the largest root of
`-1/448 + 1/16 * x ^ 2 - 1/2 * x ^ 4 + x ^ 6`
in the interval `(7/32, 5/16)` (`realRoot`, `Definitions/Polynomials.lean`). -/
noncomputable def theta : ℝ :=
  realRoot [-1/448, 0, 1/16, 0, -1/2, 0, 1] (7/32) (5/16)

@[inherit_doc] local notation "θ" => theta

open Classical in
/-- The heptagonal prism: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![polyEval [5, 0, -70, 0, 168] θ, polyEval [0, -1] θ, polyEval [1/2] θ],
    ![polyEval [5, 0, -70, 0, 168] θ, polyEval [0, -1] θ, polyEval [-1/2] θ],
    ![polyEval [-5, 0, 70, 0, -168] θ, polyEval [0, -1] θ, polyEval [1/2] θ],
    ![polyEval [-5, 0, 70, 0, -168] θ, polyEval [0, -1] θ, polyEval [-1/2] θ],
    ![polyEval [5/2, 0, -28, 0, 56] θ, polyEval [0, 6, 0, -56, 0, 112] θ, polyEval [1/2] θ],
    ![polyEval [5/2, 0, -28, 0, 56] θ, polyEval [0, 6, 0, -56, 0, 112] θ, polyEval [-1/2] θ],
    ![polyEval [-5/2, 0, 28, 0, -56] θ, polyEval [0, 6, 0, -56, 0, 112] θ, polyEval [1/2] θ],
    ![polyEval [-5/2, 0, 28, 0, -56] θ, polyEval [0, 6, 0, -56, 0, 112] θ, polyEval [-1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [1/2] θ],
    ![polyEval [1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [-1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [1/2] θ],
    ![polyEval [-1/2] θ, polyEval [0, -15, 0, 196, 0, -448] θ, polyEval [-1/2] θ],
    ![polyEval [0] θ, polyEval [0, 20, 0, -280, 0, 672] θ, polyEval [1/2] θ],
    ![polyEval [0] θ, polyEval [0, 20, 0, -280, 0, 672] θ, polyEval [-1/2] θ]].toFinset

end Nieuwland.Prism.HeptagonalPrism
