import Definitions.Polyhedra

/-!
# The rhombic dodecahedron

The polyhedron `Catalan.RhombicDodecahedron.polyhedron`: the convex hull of 14 points.
-/

namespace Nieuwland.Catalan.RhombicDodecahedron

open Classical in
/-- The rhombic dodecahedron: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 2],
    ![0, 0, -2],
    ![2, 0, 0],
    ![-2, 0, 0],
    ![0, 2, 0],
    ![0, -2, 0],
    ![1, 1, 1],
    ![1, 1, -1],
    ![1, -1, 1],
    ![1, -1, -1],
    ![-1, 1, 1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-1, -1, -1]].toFinset

end Nieuwland.Catalan.RhombicDodecahedron
