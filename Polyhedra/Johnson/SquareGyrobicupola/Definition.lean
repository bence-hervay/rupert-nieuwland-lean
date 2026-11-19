import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The square gyrobicupola

The polyhedron `Johnson.SquareGyrobicupola.polyhedron`: the convex hull of 16 points.
-/

namespace Nieuwland.Johnson.SquareGyrobicupola

open Classical in
/-- The square gyrobicupola: the convex hull of these 16 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2 + 1/2 * √2, 1/2, 0],
    ![1/2 + 1/2 * √2, -1/2, 0],
    ![-1/2 - 1/2 * √2, 1/2, 0],
    ![-1/2 - 1/2 * √2, -1/2, 0],
    ![1/2, 1/2 + 1/2 * √2, 0],
    ![1/2, -1/2 - 1/2 * √2, 0],
    ![-1/2, 1/2 + 1/2 * √2, 0],
    ![-1/2, -1/2 - 1/2 * √2, 0],
    ![1/2 * √2, 0, 1/2 * √2],
    ![-(1/2 * √2), 0, 1/2 * √2],
    ![0, 1/2 * √2, 1/2 * √2],
    ![0, -(1/2 * √2), 1/2 * √2],
    ![1/2, 1/2, -(1/2 * √2)],
    ![1/2, -1/2, -(1/2 * √2)],
    ![-1/2, 1/2, -(1/2 * √2)],
    ![-1/2, -1/2, -(1/2 * √2)]].toFinset

end Nieuwland.Johnson.SquareGyrobicupola
