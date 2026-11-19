import Definitions.Polyhedra

/-!
# The tetrakis hexahedron

The polyhedron `Catalan.TetrakisHexahedron.polyhedron`: the convex hull of 14 points.
-/

namespace Nieuwland.Catalan.TetrakisHexahedron

open Classical in
/-- The tetrakis hexahedron: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 3/2],
    ![0, 0, -3/2],
    ![3/2, 0, 0],
    ![-3/2, 0, 0],
    ![0, 3/2, 0],
    ![0, -3/2, 0],
    ![1, 1, 1],
    ![1, 1, -1],
    ![1, -1, 1],
    ![1, -1, -1],
    ![-1, 1, 1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-1, -1, -1]].toFinset

end Nieuwland.Catalan.TetrakisHexahedron
