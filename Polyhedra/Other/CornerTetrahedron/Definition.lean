import Definitions.Polyhedra

/-!
# The corner tetrahedron

The polyhedron `Other.CornerTetrahedron.polyhedron`: the convex hull of 4 points.
-/

namespace Nieuwland.Other.CornerTetrahedron

open Classical in
/-- The corner tetrahedron: the convex hull of these 4 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 0],
    ![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1]].toFinset

end Nieuwland.Other.CornerTetrahedron
