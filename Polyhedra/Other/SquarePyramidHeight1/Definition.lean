import Definitions.Polyhedra

/-!
# The square pyramid height 1

The polyhedron `Other.SquarePyramidHeight1.polyhedron`: the convex hull of 5 points.
-/

namespace Nieuwland.Other.SquarePyramidHeight1

open Classical in
/-- The square pyramid height 1: the convex hull of these 5 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![-1, -1, 0],
    ![-1, 1, 0],
    ![0, 0, 1],
    ![1, -1, 0],
    ![1, 1, 0]].toFinset

end Nieuwland.Other.SquarePyramidHeight1
