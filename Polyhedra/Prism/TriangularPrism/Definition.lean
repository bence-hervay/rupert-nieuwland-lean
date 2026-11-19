import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The triangular prism

The polyhedron `Prism.TriangularPrism.polyhedron`: the convex hull of 6 points.
-/

namespace Nieuwland.Prism.TriangularPrism

open Classical in
/-- The triangular prism: the convex hull of these 6 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/3 * √3, 0, -1/2],
    ![-(1/6 * √3), 1/2, -1/2],
    ![-(1/6 * √3), -1/2, -1/2],
    ![1/3 * √3, 0, 1/2],
    ![-(1/6 * √3), 1/2, 1/2],
    ![-(1/6 * √3), -1/2, 1/2]].toFinset

end Nieuwland.Prism.TriangularPrism
