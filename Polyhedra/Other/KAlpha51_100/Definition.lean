import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 51 / 100`

The polyhedron `Other.KAlpha51_100.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha51_100

open Classical in
/-- The solid `K_α` with `α = 51 / 100`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-51/100, -51/100, -51/100],
    ![-51/100, 51/100, 51/100],
    ![51/100, -51/100, 51/100],
    ![51/100, 51/100, -51/100]].toFinset

end Nieuwland.Other.KAlpha51_100
