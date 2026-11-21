import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The triangular dipyramid

The polyhedron `Other.TriangularDipyramid.polyhedron`: the convex hull of 5 points.
-/

namespace Nieuwland.Other.TriangularDipyramid

open Classical in
/-- The triangular dipyramid: the convex hull of these 5 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, -1],
    ![0, 0, 1],
    ![1/2 * √3, 3/2, 0],
    ![-(√3), 0, 0],
    ![1/2 * √3, -3/2, 0]].toFinset

end Nieuwland.Other.TriangularDipyramid
