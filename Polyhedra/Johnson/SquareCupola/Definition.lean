import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The square cupola

The polyhedron `Johnson.SquareCupola.polyhedron`: the convex hull of 12 points.
-/

namespace Nieuwland.Johnson.SquareCupola

open Classical in
/-- The square cupola: the convex hull of these 12 points. -/
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
    ![1/2, -1/2, 1/2 * √2],
    ![-1/2, 1/2, 1/2 * √2],
    ![-1/2, -1/2, 1/2 * √2]].toFinset

end Nieuwland.Johnson.SquareCupola
