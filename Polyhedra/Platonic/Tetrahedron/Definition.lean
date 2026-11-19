import Definitions.Polyhedra

/-!
# The tetrahedron

The polyhedron `Platonic.Tetrahedron.polyhedron`: the convex hull of 4 points.
-/

namespace Nieuwland.Platonic.Tetrahedron

open Classical in
/-- The tetrahedron: the convex hull of these 4 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, -1, 1],
    ![1, 1, -1],
    ![-1, 1, 1],
    ![-1, -1, -1]].toFinset

end Nieuwland.Platonic.Tetrahedron
