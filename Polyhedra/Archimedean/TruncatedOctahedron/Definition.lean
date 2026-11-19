import Definitions.Polyhedra

/-!
# The truncated octahedron

The polyhedron `Archimedean.TruncatedOctahedron.polyhedron`: the convex hull of 24 points.
-/

namespace Nieuwland.Archimedean.TruncatedOctahedron

open Classical in
/-- The truncated octahedron: the convex hull of these 24 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 0, 2],
    ![1, 0, -2],
    ![-1, 0, 2],
    ![-1, 0, -2],
    ![2, 1, 0],
    ![2, -1, 0],
    ![-2, 1, 0],
    ![-2, -1, 0],
    ![0, 2, 1],
    ![0, 2, -1],
    ![0, -2, 1],
    ![0, -2, -1],
    ![0, 1, 2],
    ![0, 1, -2],
    ![0, -1, 2],
    ![0, -1, -2],
    ![2, 0, 1],
    ![2, 0, -1],
    ![-2, 0, 1],
    ![-2, 0, -1],
    ![1, 2, 0],
    ![1, -2, 0],
    ![-1, 2, 0],
    ![-1, -2, 0]].toFinset

end Nieuwland.Archimedean.TruncatedOctahedron
