import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The pentagonal cupola

The polyhedron `Johnson.PentagonalCupola.polyhedron`: the convex hull of 15 points.
-/

namespace Nieuwland.Johnson.PentagonalCupola

open Classical in
/-- The pentagonal cupola: the convex hull of these 15 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2 + 1/2 * √5, 0, 0],
    ![-1/2 - 1/2 * √5, 0, 0],
    ![3/4 + 1/4 * √5, -1/4 - 1/4 * √5, 1/2],
    ![3/4 + 1/4 * √5, 1/4 + 1/4 * √5, -1/2],
    ![-3/4 - 1/4 * √5, -1/4 - 1/4 * √5, 1/2],
    ![-3/4 - 1/4 * √5, 1/4 + 1/4 * √5, -1/2],
    ![1/2, -3/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![1/2, 3/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![-1/2, -3/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/2, 3/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, -1/4 + 1/4 * √5],
    ![-1/4 - 1/4 * √5, 1/2, -1/4 + 1/4 * √5],
    ![1/2, 1/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/2, 1/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![0, 1, 0]].toFinset

end Nieuwland.Johnson.PentagonalCupola
