import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 27 / 50`

The polyhedron `Other.KAlpha27_50.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha27_50

open Classical in
/-- The solid `K_α` with `α = 27 / 50`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-27/50, -27/50, -27/50],
    ![-27/50, 27/50, 27/50],
    ![27/50, -27/50, 27/50],
    ![27/50, 27/50, -27/50]].toFinset

end Nieuwland.Other.KAlpha27_50
