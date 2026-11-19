import Definitions.Polyhedra

/-!
# The cuboctahedron

The polyhedron `Archimedean.Cuboctahedron.polyhedron`: the convex hull of 12 points.
-/

namespace Nieuwland.Archimedean.Cuboctahedron

open Classical in
/-- The cuboctahedron: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 0, 1],
    ![1, 0, -1],
    ![-1, 0, 1],
    ![-1, 0, -1],
    ![1, 1, 0],
    ![1, -1, 0],
    ![-1, 1, 0],
    ![-1, -1, 0],
    ![0, 1, 1],
    ![0, 1, -1],
    ![0, -1, 1],
    ![0, -1, -1]].toFinset

end Nieuwland.Archimedean.Cuboctahedron
