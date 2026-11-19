import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated square pyramid

The polyhedron `Johnson.ElongatedSquarePyramid.polyhedron`: the convex hull of 9 points.
-/

namespace Nieuwland.Johnson.ElongatedSquarePyramid

open Classical in
/-- The elongated square pyramid: the convex hull of these 9 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 1/2, 1/2],
    ![1/2, 1/2, -1/2],
    ![1/2, -1/2, 1/2],
    ![1/2, -1/2, -1/2],
    ![-1/2, 1/2, 1/2],
    ![-1/2, 1/2, -1/2],
    ![-1/2, -1/2, 1/2],
    ![-1/2, -1/2, -1/2],
    ![0, 0, 1/2 + 1/2 * √2]].toFinset

end Nieuwland.Johnson.ElongatedSquarePyramid
