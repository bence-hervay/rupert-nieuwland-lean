import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The gyroelongated pentagonal pyramid

The polyhedron `Johnson.GyroelongatedPentagonalPyramid.polyhedron`: the convex hull of 11 points.
-/

namespace Nieuwland.Johnson.GyroelongatedPentagonalPyramid

open Classical in
/-- The gyroelongated pentagonal pyramid: the convex hull of these 11 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 0, 1/4 + 1/4 * √5],
    ![1/2, 0, -1/4 - 1/4 * √5],
    ![-1/2, 0, 1/4 + 1/4 * √5],
    ![-1/2, 0, -1/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, 0],
    ![1/4 + 1/4 * √5, -1/2, 0],
    ![-1/4 - 1/4 * √5, 1/2, 0],
    ![-1/4 - 1/4 * √5, -1/2, 0],
    ![0, 1/4 + 1/4 * √5, 1/2],
    ![0, 1/4 + 1/4 * √5, -1/2],
    ![0, -1/4 - 1/4 * √5, -1/2]].toFinset

end Nieuwland.Johnson.GyroelongatedPentagonalPyramid
