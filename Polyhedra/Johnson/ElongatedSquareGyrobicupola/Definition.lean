import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated square gyrobicupola

The polyhedron `Johnson.ElongatedSquareGyrobicupola.polyhedron`: the convex hull of 24 points.
-/

namespace Nieuwland.Johnson.ElongatedSquareGyrobicupola

open Classical in
/-- The elongated square gyrobicupola: the convex hull of these 24 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2 * √2, 0, 1/2 + 1/2 * √2],
    ![-(1/2 * √2), 0, 1/2 + 1/2 * √2],
    ![0, 1/2 * √2, 1/2 + 1/2 * √2],
    ![0, -(1/2 * √2), 1/2 + 1/2 * √2],
    ![1/2, 1/2, -1/2 - 1/2 * √2],
    ![1/2, -1/2, -1/2 - 1/2 * √2],
    ![-1/2, 1/2, -1/2 - 1/2 * √2],
    ![-1/2, -1/2, -1/2 - 1/2 * √2],
    ![1/2 + 1/2 * √2, 1/2, 1/2],
    ![1/2 + 1/2 * √2, 1/2, -1/2],
    ![1/2 + 1/2 * √2, -1/2, 1/2],
    ![1/2 + 1/2 * √2, -1/2, -1/2],
    ![-1/2 - 1/2 * √2, 1/2, 1/2],
    ![-1/2 - 1/2 * √2, 1/2, -1/2],
    ![-1/2 - 1/2 * √2, -1/2, 1/2],
    ![-1/2 - 1/2 * √2, -1/2, -1/2],
    ![1/2, 1/2 + 1/2 * √2, 1/2],
    ![1/2, 1/2 + 1/2 * √2, -1/2],
    ![1/2, -1/2 - 1/2 * √2, 1/2],
    ![1/2, -1/2 - 1/2 * √2, -1/2],
    ![-1/2, 1/2 + 1/2 * √2, 1/2],
    ![-1/2, 1/2 + 1/2 * √2, -1/2],
    ![-1/2, -1/2 - 1/2 * √2, 1/2],
    ![-1/2, -1/2 - 1/2 * √2, -1/2]].toFinset

end Nieuwland.Johnson.ElongatedSquareGyrobicupola
