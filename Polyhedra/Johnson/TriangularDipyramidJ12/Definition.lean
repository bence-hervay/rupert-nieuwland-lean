import Definitions.Polyhedra

/-!
# The triangular dipyramid j12

The polyhedron `Johnson.TriangularDipyramidJ12.polyhedron`: the convex hull of 5 points.
-/

namespace Nieuwland.Johnson.TriangularDipyramidJ12

open Classical in
/-- The triangular dipyramid j12: the convex hull of these 5 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![2, 2, 2],
    ![-2, -2, -2],
    ![2, -1, -1],
    ![-1, 2, -1],
    ![-1, -1, 2]].toFinset

end Nieuwland.Johnson.TriangularDipyramidJ12
