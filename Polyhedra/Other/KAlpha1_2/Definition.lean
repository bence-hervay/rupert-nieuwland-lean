import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 1 / 2`

The polyhedron `Other.KAlpha1_2.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha1_2

open Classical in
/-- The solid `K_α` with `α = 1 / 2`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-1/2, -1/2, -1/2],
    ![-1/2, 1/2, 1/2],
    ![1/2, -1/2, 1/2],
    ![1/2, 1/2, -1/2]].toFinset

end Nieuwland.Other.KAlpha1_2
