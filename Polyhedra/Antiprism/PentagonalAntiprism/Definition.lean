import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The pentagonal antiprism

The polyhedron `Antiprism.PentagonalAntiprism.polyhedron`: the convex hull of 10 points.
-/

namespace Nieuwland.Antiprism.PentagonalAntiprism

open Classical in
/-- The pentagonal antiprism: the convex hull of these 10 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 0, 1/4 + 1/4 * √5],
    ![1/2, 0, -1/4 - 1/4 * √5],
    ![-1/2, 0, 1/4 + 1/4 * √5],
    ![-1/2, 0, -1/4 - 1/4 * √5],
    ![0, 1/4 + 1/4 * √5, 1/2],
    ![0, 1/4 + 1/4 * √5, -1/2],
    ![0, -1/4 - 1/4 * √5, 1/2],
    ![0, -1/4 - 1/4 * √5, -1/2],
    ![1/4 + 1/4 * √5, 1/2, 0],
    ![-1/4 - 1/4 * √5, -1/2, 0]].toFinset

end Nieuwland.Antiprism.PentagonalAntiprism
