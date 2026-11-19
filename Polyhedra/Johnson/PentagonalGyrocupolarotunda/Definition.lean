import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The pentagonal gyrocupolarotunda

The polyhedron `Johnson.PentagonalGyrocupolarotunda.polyhedron`: the convex hull of 25 points.
-/

namespace Nieuwland.Johnson.PentagonalGyrocupolarotunda

open Classical in
/-- The pentagonal gyrocupolarotunda: the convex hull of these 25 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 1/2 + 1/2 * √5],
    ![0, 0, -1/2 - 1/2 * √5],
    ![1/2 + 1/2 * √5, 0, 0],
    ![0, 1/2 + 1/2 * √5, 0],
    ![1/4 + 1/4 * √5, 1/2, 3/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, -3/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, -1/2, 3/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, -1/2, -3/4 - 1/4 * √5],
    ![-1/4 - 1/4 * √5, 1/2, 3/4 + 1/4 * √5],
    ![-1/4 - 1/4 * √5, 1/2, -3/4 - 1/4 * √5],
    ![3/4 + 1/4 * √5, 1/4 + 1/4 * √5, 1/2],
    ![3/4 + 1/4 * √5, 1/4 + 1/4 * √5, -1/2],
    ![3/4 + 1/4 * √5, -1/4 - 1/4 * √5, 1/2],
    ![3/4 + 1/4 * √5, -1/4 - 1/4 * √5, -1/2],
    ![-3/4 - 1/4 * √5, 1/4 + 1/4 * √5, 1/2],
    ![-3/4 - 1/4 * √5, 1/4 + 1/4 * √5, -1/2],
    ![1/2, 3/4 + 1/4 * √5, 1/4 + 1/4 * √5],
    ![1/2, 3/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![-1/2, 3/4 + 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/2, 3/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![1/5 * √5, -(2/5 * √5), 0],
    ![-3/4 - 1/20 * √5, 1/4 - 3/20 * √5, 1/2],
    ![-3/4 - 1/20 * √5, 1/4 - 3/20 * √5, -1/2],
    ![-1/2 + 1/5 * √5, -1/4 - 3/20 * √5, 1/4 + 1/4 * √5],
    ![-1/2 + 1/5 * √5, -1/4 - 3/20 * √5, -1/4 - 1/4 * √5]].toFinset

end Nieuwland.Johnson.PentagonalGyrocupolarotunda
