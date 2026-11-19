import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated triangular cupola

The polyhedron `Johnson.ElongatedTriangularCupola.polyhedron`: the convex hull of 15 points.
-/

namespace Nieuwland.Johnson.ElongatedTriangularCupola

open Classical in
/-- The elongated triangular cupola: the convex hull of these 15 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1 + √6, 1 - √6, 1],
    ![-1 - √6, -1 + √6, -1],
    ![-1, -1 - √6, -1 + √6],
    ![1, 1 + √6, 1 - √6],
    ![1 - √6, 1, 1 + √6],
    ![-1 + √6, -1, -1 - √6],
    ![-1 - √6, -1, -1 + √6],
    ![1 + √6, 1, 1 - √6],
    ![1 - √6, 1 + √6, 1],
    ![-1 + √6, -1 - √6, -1],
    ![1, 1 - √6, 1 + √6],
    ![-1, -1 + √6, -1 - √6],
    ![1, 1 + √6, 1 + √6],
    ![1 + √6, 1, 1 + √6],
    ![1 + √6, 1 + √6, 1]].toFinset

end Nieuwland.Johnson.ElongatedTriangularCupola
