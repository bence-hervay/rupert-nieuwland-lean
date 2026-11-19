import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The solid `K_α` with `α = √3 / 3`

The polyhedron `Other.KAlphaSqrt3_3.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlphaSqrt3_3

open Classical in
/-- The solid `K_α` with `α = √3 / 3`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-(1/3 * √3), -(1/3 * √3), -(1/3 * √3)],
    ![-(1/3 * √3), 1/3 * √3, 1/3 * √3],
    ![1/3 * √3, -(1/3 * √3), 1/3 * √3],
    ![1/3 * √3, 1/3 * √3, -(1/3 * √3)]].toFinset

end Nieuwland.Other.KAlphaSqrt3_3
