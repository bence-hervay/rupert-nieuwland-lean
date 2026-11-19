import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The gyrobifastigium

The polyhedron `Johnson.Gyrobifastigium.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Johnson.Gyrobifastigium

open Classical in
/-- The gyrobifastigium: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 0, 1/2 * √3],
    ![-1/2, 0, 1/2 * √3],
    ![0, 1/2, -(1/2 * √3)],
    ![0, -1/2, -(1/2 * √3)],
    ![1/2, 1/2, 0],
    ![1/2, -1/2, 0],
    ![-1/2, 1/2, 0],
    ![-1/2, -1/2, 0]].toFinset

end Nieuwland.Johnson.Gyrobifastigium
