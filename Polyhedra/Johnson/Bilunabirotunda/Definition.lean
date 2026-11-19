import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The bilunabirotunda

The polyhedron `Johnson.Bilunabirotunda.polyhedron`: the convex hull of 14 points.
-/

namespace Nieuwland.Johnson.Bilunabirotunda

open Classical in
/-- The bilunabirotunda: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 1/4 + 1/4 * √5, 1/2],
    ![1/2, 1/4 + 1/4 * √5, -1/2],
    ![1/2, -1/4 - 1/4 * √5, 1/2],
    ![1/2, -1/4 - 1/4 * √5, -1/2],
    ![-1/2, 1/4 + 1/4 * √5, 1/2],
    ![-1/2, 1/4 + 1/4 * √5, -1/2],
    ![-1/2, -1/4 - 1/4 * √5, 1/2],
    ![-1/2, -1/4 - 1/4 * √5, -1/2],
    ![3/4 + 1/4 * √5, 1/2, 0],
    ![3/4 + 1/4 * √5, -1/2, 0],
    ![-3/4 - 1/4 * √5, 1/2, 0],
    ![-3/4 - 1/4 * √5, -1/2, 0],
    ![0, 0, 1/4 + 1/4 * √5],
    ![0, 0, -1/4 - 1/4 * √5]].toFinset

end Nieuwland.Johnson.Bilunabirotunda
