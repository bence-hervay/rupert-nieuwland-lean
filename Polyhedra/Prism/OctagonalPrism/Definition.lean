import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The octagonal prism

The polyhedron `Prism.OctagonalPrism.polyhedron`: the convex hull of 16 points.
-/

namespace Nieuwland.Prism.OctagonalPrism

open Classical in
/-- The octagonal prism: the convex hull of these 16 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2 + 1/2 * √2, 1/2, 1/2],
    ![1/2 + 1/2 * √2, 1/2, -1/2],
    ![1/2 + 1/2 * √2, -1/2, 1/2],
    ![1/2 + 1/2 * √2, -1/2, -1/2],
    ![-1/2 - 1/2 * √2, 1/2, 1/2],
    ![-1/2 - 1/2 * √2, 1/2, -1/2],
    ![-1/2 - 1/2 * √2, -1/2, 1/2],
    ![-1/2 - 1/2 * √2, -1/2, -1/2],
    ![1/2, 1/2 + 1/2 * √2, 1/2],
    ![1/2, 1/2 + 1/2 * √2, -1/2],
    ![1/2, -1/2 - 1/2 * √2, 1/2],
    ![1/2, -1/2 - 1/2 * √2, -1/2],
    ![-1/2, 1/2 + 1/2 * √2, 1/2],
    ![-1/2, 1/2 + 1/2 * √2, -1/2],
    ![-1/2, -1/2 - 1/2 * √2, 1/2],
    ![-1/2, -1/2 - 1/2 * √2, -1/2]].toFinset

end Nieuwland.Prism.OctagonalPrism
