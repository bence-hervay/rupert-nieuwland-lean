import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The deltoidal icositetrahedron

The polyhedron `Catalan.DeltoidalIcositetrahedron.polyhedron`: the convex hull of 26 points.
-/

namespace Nieuwland.Catalan.DeltoidalIcositetrahedron

open Classical in
/-- The deltoidal icositetrahedron: the convex hull of these 26 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, √2],
    ![0, 0, -(√2)],
    ![√2, 0, 0],
    ![-(√2), 0, 0],
    ![0, √2, 0],
    ![0, -(√2), 0],
    ![1, 0, 1],
    ![1, 0, -1],
    ![-1, 0, 1],
    ![-1, 0, -1],
    ![1, 1, 0],
    ![1, -1, 0],
    ![-1, 1, 0],
    ![-1, -1, 0],
    ![0, 1, 1],
    ![0, 1, -1],
    ![0, -1, 1],
    ![0, -1, -1],
    ![4/7 + 1/7 * √2, 4/7 + 1/7 * √2, 4/7 + 1/7 * √2],
    ![4/7 + 1/7 * √2, 4/7 + 1/7 * √2, -4/7 - 1/7 * √2],
    ![4/7 + 1/7 * √2, -4/7 - 1/7 * √2, 4/7 + 1/7 * √2],
    ![4/7 + 1/7 * √2, -4/7 - 1/7 * √2, -4/7 - 1/7 * √2],
    ![-4/7 - 1/7 * √2, 4/7 + 1/7 * √2, 4/7 + 1/7 * √2],
    ![-4/7 - 1/7 * √2, 4/7 + 1/7 * √2, -4/7 - 1/7 * √2],
    ![-4/7 - 1/7 * √2, -4/7 - 1/7 * √2, 4/7 + 1/7 * √2],
    ![-4/7 - 1/7 * √2, -4/7 - 1/7 * √2, -4/7 - 1/7 * √2]].toFinset

end Nieuwland.Catalan.DeltoidalIcositetrahedron
