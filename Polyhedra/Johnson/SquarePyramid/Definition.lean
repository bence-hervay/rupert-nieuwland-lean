import Definitions.Polyhedra

/-!
# The square pyramid

The polyhedron `Johnson.SquarePyramid.polyhedron`: the convex hull of 5 points.
-/

namespace Nieuwland.Johnson.SquarePyramid

open Classical in
/-- The square pyramid: the convex hull of these 5 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 0, 0],
    ![-1, 0, 0],
    ![0, 1, 0],
    ![0, -1, 0],
    ![0, 0, 1]].toFinset

end Nieuwland.Johnson.SquarePyramid
