import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated square cupola

The polyhedron `Johnson.ElongatedSquareCupola.polyhedron`: the convex hull of 20 points.
-/

namespace Nieuwland.Johnson.ElongatedSquareCupola

open Classical in
/-- The elongated square cupola: the convex hull of these 20 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
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
    ![-1/2, -1/2 - 1/2 * √2, -1/2],
    ![1/2, 1/2, 1/2 + 1/2 * √2],
    ![1/2, -1/2, 1/2 + 1/2 * √2],
    ![-1/2, 1/2, 1/2 + 1/2 * √2],
    ![-1/2, -1/2, 1/2 + 1/2 * √2]].toFinset

end Nieuwland.Johnson.ElongatedSquareCupola
