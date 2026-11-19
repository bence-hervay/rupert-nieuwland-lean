import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The square orthobicupola

The polyhedron `Johnson.SquareOrthobicupola.polyhedron`: the convex hull of 16 points.
-/

namespace Nieuwland.Johnson.SquareOrthobicupola

open Classical in
/-- The square orthobicupola: the convex hull of these 16 points. -/
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
    ![1/2, 1/2, 1/2 * √2],
    ![1/2, 1/2, -(1/2 * √2)],
    ![1/2, -1/2, 1/2 * √2],
    ![1/2, -1/2, -(1/2 * √2)],
    ![-1/2, 1/2, 1/2 * √2],
    ![-1/2, 1/2, -(1/2 * √2)],
    ![-1/2, -1/2, 1/2 * √2],
    ![-1/2, -1/2, -(1/2 * √2)]].toFinset

end Nieuwland.Johnson.SquareOrthobicupola
