import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated triangular gyrobicupola

The polyhedron `Johnson.ElongatedTriangularGyrobicupola.polyhedron`: the convex hull of 18 points.
-/

namespace Nieuwland.Johnson.ElongatedTriangularGyrobicupola

open Classical in
/-- The elongated triangular gyrobicupola: the convex hull of these 18 points. -/
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
    ![-1, -1 - √6, -1 - √6],
    ![1 + √6, 1, 1 + √6],
    ![-1 - √6, -1, -1 - √6],
    ![1 + √6, 1 + √6, 1],
    ![-1 - √6, -1 - √6, -1]].toFinset

end Nieuwland.Johnson.ElongatedTriangularGyrobicupola
