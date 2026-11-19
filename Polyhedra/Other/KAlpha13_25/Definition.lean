import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 13 / 25`

The polyhedron `Other.KAlpha13_25.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha13_25

open Classical in
/-- The solid `K_α` with `α = 13 / 25`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-13/25, -13/25, -13/25],
    ![-13/25, 13/25, 13/25],
    ![13/25, -13/25, 13/25],
    ![13/25, 13/25, -13/25]].toFinset

end Nieuwland.Other.KAlpha13_25
