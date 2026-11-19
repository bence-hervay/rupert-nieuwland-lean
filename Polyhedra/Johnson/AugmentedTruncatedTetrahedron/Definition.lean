import Definitions.Polyhedra

/-!
# The augmented truncated tetrahedron

The polyhedron `Johnson.AugmentedTruncatedTetrahedron.polyhedron`: the convex hull of 15 points.
-/

namespace Nieuwland.Johnson.AugmentedTruncatedTetrahedron

open Classical in
/-- The augmented truncated tetrahedron: the convex hull of these 15 points. -/
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
    ![-1, -3, -1],
    ![5/3, 5/3, 11/3],
    ![11/3, 5/3, 5/3],
    ![5/3, 11/3, 5/3]].toFinset

end Nieuwland.Johnson.AugmentedTruncatedTetrahedron
