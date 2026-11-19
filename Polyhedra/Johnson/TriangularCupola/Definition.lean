import Definitions.Polyhedra

/-!
# The triangular cupola

The polyhedron `Johnson.TriangularCupola.polyhedron`: the convex hull of 9 points.
-/

namespace Nieuwland.Johnson.TriangularCupola

open Classical in
/-- The triangular cupola: the convex hull of these 9 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 0, 1],
    ![1, 0, -1],
    ![-1, 0, 1],
    ![1, 1, 0],
    ![1, -1, 0],
    ![-1, 1, 0],
    ![0, 1, 1],
    ![0, 1, -1],
    ![0, -1, 1]].toFinset

end Nieuwland.Johnson.TriangularCupola
