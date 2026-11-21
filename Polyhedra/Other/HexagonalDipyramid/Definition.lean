import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The hexagonal dipyramid

The polyhedron `Other.HexagonalDipyramid.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Other.HexagonalDipyramid

open Classical in
/-- The hexagonal dipyramid: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, -1],
    ![0, 0, 1],
    ![1/2, 1/6 * √3, 0],
    ![0, 1/3 * √3, 0],
    ![-1/2, 1/6 * √3, 0],
    ![-1/2, -(1/6 * √3), 0],
    ![0, -(1/3 * √3), 0],
    ![1/2, -(1/6 * √3), 0]].toFinset

end Nieuwland.Other.HexagonalDipyramid
