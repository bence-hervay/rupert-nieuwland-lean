import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated square dipyramid

The polyhedron `Johnson.ElongatedSquareDipyramid.polyhedron`: the convex hull of 10 points.
-/

namespace Nieuwland.Johnson.ElongatedSquareDipyramid

open Classical in
/-- The elongated square dipyramid: the convex hull of these 10 points. -/
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
    ![0, 0, 1/2 + 1/2 * √2],
    ![0, 0, -1/2 - 1/2 * √2]].toFinset

end Nieuwland.Johnson.ElongatedSquareDipyramid
