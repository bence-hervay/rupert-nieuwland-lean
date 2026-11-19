import Definitions.Polyhedra

/-!
# The truncated tetrahedron

The polyhedron `Archimedean.TruncatedTetrahedron.polyhedron`: the convex hull of 12 points.
-/

namespace Nieuwland.Archimedean.TruncatedTetrahedron

open Classical in
/-- The truncated tetrahedron: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, -1, 3],
    ![1, 1, -3],
    ![-1, 1, 3],
    ![-1, -1, -3],
    ![3, -1, 1],
    ![3, 1, -1],
    ![-3, 1, 1],
    ![-3, -1, -1],
    ![1, -3, 1],
    ![1, 3, -1],
    ![-1, 3, 1],
    ![-1, -3, -1]].toFinset

end Nieuwland.Archimedean.TruncatedTetrahedron
