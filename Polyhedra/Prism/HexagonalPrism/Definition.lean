import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The hexagonal prism

The polyhedron `Prism.HexagonalPrism.polyhedron`: the convex hull of 12 points.
-/

namespace Nieuwland.Prism.HexagonalPrism

open Classical in
/-- The hexagonal prism: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1, 0, 1/2],
    ![1, 0, -1/2],
    ![-1, 0, 1/2],
    ![-1, 0, -1/2],
    ![1/2, 1/2 * √3, 1/2],
    ![1/2, 1/2 * √3, -1/2],
    ![1/2, -(1/2 * √3), 1/2],
    ![1/2, -(1/2 * √3), -1/2],
    ![-1/2, 1/2 * √3, 1/2],
    ![-1/2, 1/2 * √3, -1/2],
    ![-1/2, -(1/2 * √3), 1/2],
    ![-1/2, -(1/2 * √3), -1/2]].toFinset

end Nieuwland.Prism.HexagonalPrism
