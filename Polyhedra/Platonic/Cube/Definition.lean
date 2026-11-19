import Definitions.Polyhedra

/-!
# The cube

The polyhedron `Platonic.Cube.polyhedron`: the convex hull of 8 points.
-/

namespace Nieuwland.Platonic.Cube

open Classical in
/-- The cube: the convex hull of these 8 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![-1, -1, -1],
    ![-1, -1, 1],
    ![-1, 1, -1],
    ![-1, 1, 1],
    ![1, -1, -1],
    ![1, -1, 1],
    ![1, 1, -1],
    ![1, 1, 1]].toFinset

end Nieuwland.Platonic.Cube
