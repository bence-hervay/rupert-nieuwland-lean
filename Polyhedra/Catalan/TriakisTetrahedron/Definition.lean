import Definitions.Polyhedra

/-!
# The triakis tetrahedron

The polyhedron `Catalan.TriakisTetrahedron.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Catalan.TriakisTetrahedron

open Classical in
/-- The triakis tetrahedron: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![5/3, 5/3, 5/3],
    ![5/3, -5/3, -5/3],
    ![-5/3, -5/3, 5/3],
    ![-5/3, 5/3, -5/3],
    ![1, -1, 1],
    ![1, 1, -1],
    ![-1, 1, 1],
    ![-1, -1, -1]].toFinset

end Nieuwland.Catalan.TriakisTetrahedron
