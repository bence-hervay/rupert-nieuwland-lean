import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The elongated triangular orthobicupola

The polyhedron `Johnson.ElongatedTriangularOrthobicupola.polyhedron`: the convex hull of 18 points.
-/

namespace Nieuwland.Johnson.ElongatedTriangularOrthobicupola

open Classical in
/-- The elongated triangular orthobicupola: the convex hull of these 18 points. -/
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
    ![1 + √6, 1 + √6, 1],
    ![-1 - 4/3 * √6, -1 - 1/3 * √6, -1 - 1/3 * √6],
    ![-1 - 1/3 * √6, -1 - 4/3 * √6, -1 - 1/3 * √6],
    ![-1 - 1/3 * √6, -1 - 1/3 * √6, -1 - 4/3 * √6]].toFinset

end Nieuwland.Johnson.ElongatedTriangularOrthobicupola
