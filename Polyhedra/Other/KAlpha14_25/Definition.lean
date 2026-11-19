import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 14 / 25`

The polyhedron `Other.KAlpha14_25.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha14_25

open Classical in
/-- The solid `K_α` with `α = 14 / 25`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-14/25, -14/25, -14/25],
    ![-14/25, 14/25, 14/25],
    ![14/25, -14/25, 14/25],
    ![14/25, 14/25, -14/25]].toFinset

end Nieuwland.Other.KAlpha14_25
