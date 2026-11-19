import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 53 / 100`

The polyhedron `Other.KAlpha53_100.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha53_100

open Classical in
/-- The solid `K_α` with `α = 53 / 100`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-53/100, -53/100, -53/100],
    ![-53/100, 53/100, 53/100],
    ![53/100, -53/100, 53/100],
    ![53/100, 53/100, -53/100]].toFinset

end Nieuwland.Other.KAlpha53_100
