import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 57 / 100`

The polyhedron `Other.KAlpha57_100.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha57_100

open Classical in
/-- The solid `K_α` with `α = 57 / 100`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-57/100, -57/100, -57/100],
    ![-57/100, 57/100, 57/100],
    ![57/100, -57/100, 57/100],
    ![57/100, 57/100, -57/100]].toFinset

end Nieuwland.Other.KAlpha57_100
