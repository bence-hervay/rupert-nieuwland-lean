import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The pentagonal rotunda

The polyhedron `Johnson.PentagonalRotunda.polyhedron`: the convex hull of 20 points.
-/

namespace Nieuwland.Johnson.PentagonalRotunda

open Classical in
/-- The pentagonal rotunda: the convex hull of these 20 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2 + 1/2 * √5, 0, 0],
    ![-1/2 - 1/2 * √5, 0, 0],
    ![0, 0, 1/2 + 1/2 * √5],
    ![0, 1/2 + 1/2 * √5, 0],
    ![3/4 + 1/4 * √5, 1/2, 1/4 + 1/4 * √5],
    ![3/4 + 1/4 * √5, 1/2, -1/4 - 1/4 * √5],
    ![3/4 + 1/4 * √5, -1/2, 1/4 + 1/4 * √5],
    ![-3/4 - 1/4 * √5, 1/2, 1/4 + 1/4 * √5],
    ![-3/4 - 1/4 * √5, 1/2, -1/4 - 1/4 * √5],
    ![-3/4 - 1/4 * √5, -1/2, 1/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, 3/4 + 1/4 * √5, 1/2],
    ![1/4 + 1/4 * √5, 3/4 + 1/4 * √5, -1/2],
    ![-1/4 - 1/4 * √5, 3/4 + 1/4 * √5, 1/2],
    ![-1/4 - 1/4 * √5, 3/4 + 1/4 * √5, -1/2],
    ![1/2, 1/4 + 1/4 * √5, 3/4 + 1/4 * √5],
    ![1/2, 1/4 + 1/4 * √5, -3/4 - 1/4 * √5],
    ![1/2, -1/4 - 1/4 * √5, 3/4 + 1/4 * √5],
    ![-1/2, 1/4 + 1/4 * √5, 3/4 + 1/4 * √5],
    ![-1/2, 1/4 + 1/4 * √5, -3/4 - 1/4 * √5],
    ![-1/2, -1/4 - 1/4 * √5, 3/4 + 1/4 * √5]].toFinset

end Nieuwland.Johnson.PentagonalRotunda
