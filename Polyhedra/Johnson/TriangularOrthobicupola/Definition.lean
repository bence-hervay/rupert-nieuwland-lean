import Definitions.Polyhedra

/-!
# The triangular orthobicupola

The polyhedron `Johnson.TriangularOrthobicupola.polyhedron`: the convex hull of 12 points.
-/

namespace Nieuwland.Johnson.TriangularOrthobicupola

open Classical in
/-- The triangular orthobicupola: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![-1, -1, -4],
    ![-1, -4, -1],
    ![-4, -1, -1],
    ![3, 0, 3],
    ![3, 0, -3],
    ![-3, 0, 3],
    ![3, 3, 0],
    ![3, -3, 0],
    ![-3, 3, 0],
    ![0, 3, 3],
    ![0, 3, -3],
    ![0, -3, 3]].toFinset

end Nieuwland.Johnson.TriangularOrthobicupola
