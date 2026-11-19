import Definitions.Polyhedra

/-!
# The solid `K_α` with `α = 11 / 20`

The polyhedron `Other.KAlpha11_20.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.KAlpha11_20

open Classical in
/-- The solid `K_α` with `α = 11 / 20`: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 1, 1],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-11/20, -11/20, -11/20],
    ![-11/20, 11/20, 11/20],
    ![11/20, -11/20, 11/20],
    ![11/20, 11/20, -11/20]].toFinset

end Nieuwland.Other.KAlpha11_20
