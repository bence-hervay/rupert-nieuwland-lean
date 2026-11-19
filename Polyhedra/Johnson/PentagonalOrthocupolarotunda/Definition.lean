import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The pentagonal orthocupolarotunda

The polyhedron `Johnson.PentagonalOrthocupolarotunda.polyhedron`: the convex hull of 25 points.
-/

namespace Nieuwland.Johnson.PentagonalOrthocupolarotunda

open Classical in
/-- The pentagonal orthocupolarotunda: the convex hull of these 25 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 1/2 + 1/2 * √5],
    ![0, 0, -1/2 - 1/2 * √5],
    ![1/2 + 1/2 * √5, 0, 0],
    ![0, 1/2 + 1/2 * √5, 0],
    ![-1/4 - 1/4 * √5, 1/2, 3/4 + 1/4 * √5],
    ![-1/4 - 1/4 * √5, 1/2, -3/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, -1/2, 3/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, -1/2, -3/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, 3/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, -3/4 - 1/4 * √5],
    ![-3/4 - 1/4 * √5, 1/4 + 1/4 * √5, 1/2],
    ![-3/4 - 1/4 * √5, 1/4 + 1/4 * √5, -1/2],
    ![3/4 + 1/4 * √5, -1/4 - 1/4 * √5, 1/2],
    ![3/4 + 1/4 * √5, -1/4 - 1/4 * √5, -1/2],
    ![3/4 + 1/4 * √5, 1/4 + 1/4 * √5, 1/2],
    ![3/4 + 1/4 * √5, 1/4 + 1/4 * √5, -1/2],
    ![-1/2, 3/4 + 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/2, 3/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![1/2, 3/4 + 1/4 * √5, 1/4 + 1/4 * √5],
    ![1/2, 3/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![-1, 0, 0],
    ![-1/2, 1/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/2, 1/4 - 1/4 * √5, -1/4 - 1/4 * √5],
    ![-1/4 + 1/4 * √5, -1/4 - 1/4 * √5, 1/2],
    ![-1/4 + 1/4 * √5, -1/4 - 1/4 * √5, -1/2]].toFinset

end Nieuwland.Johnson.PentagonalOrthocupolarotunda
