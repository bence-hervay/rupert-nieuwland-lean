import Definitions.Polyhedra

/-!
# The octahedron

The polyhedron `Platonic.Octahedron.polyhedron`: the convex hull of 6 points.
-/

namespace Nieuwland.Platonic.Octahedron

open Classical in
/-- The octahedron: the convex hull of these 6 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 1],
    ![0, 0, -1],
    ![1, 0, 0],
    ![-1, 0, 0],
    ![0, 1, 0],
    ![0, -1, 0]].toFinset

end Nieuwland.Platonic.Octahedron
