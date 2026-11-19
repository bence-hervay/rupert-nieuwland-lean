import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The truncated cube

The polyhedron `Archimedean.TruncatedCube.polyhedron`: the convex hull of 24 points.
-/

namespace Nieuwland.Archimedean.TruncatedCube

open Classical in
/-- The truncated cube: the convex hull of these 24 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2 + 1/2 * √2, 1/2, 1/2 + 1/2 * √2],
    ![1/2 + 1/2 * √2, 1/2, -1/2 - 1/2 * √2],
    ![1/2 + 1/2 * √2, -1/2, 1/2 + 1/2 * √2],
    ![1/2 + 1/2 * √2, -1/2, -1/2 - 1/2 * √2],
    ![-1/2 - 1/2 * √2, 1/2, 1/2 + 1/2 * √2],
    ![-1/2 - 1/2 * √2, 1/2, -1/2 - 1/2 * √2],
    ![-1/2 - 1/2 * √2, -1/2, 1/2 + 1/2 * √2],
    ![-1/2 - 1/2 * √2, -1/2, -1/2 - 1/2 * √2],
    ![1/2 + 1/2 * √2, 1/2 + 1/2 * √2, 1/2],
    ![1/2 + 1/2 * √2, 1/2 + 1/2 * √2, -1/2],
    ![1/2 + 1/2 * √2, -1/2 - 1/2 * √2, 1/2],
    ![1/2 + 1/2 * √2, -1/2 - 1/2 * √2, -1/2],
    ![-1/2 - 1/2 * √2, 1/2 + 1/2 * √2, 1/2],
    ![-1/2 - 1/2 * √2, 1/2 + 1/2 * √2, -1/2],
    ![-1/2 - 1/2 * √2, -1/2 - 1/2 * √2, 1/2],
    ![-1/2 - 1/2 * √2, -1/2 - 1/2 * √2, -1/2],
    ![1/2, 1/2 + 1/2 * √2, 1/2 + 1/2 * √2],
    ![1/2, 1/2 + 1/2 * √2, -1/2 - 1/2 * √2],
    ![1/2, -1/2 - 1/2 * √2, 1/2 + 1/2 * √2],
    ![1/2, -1/2 - 1/2 * √2, -1/2 - 1/2 * √2],
    ![-1/2, 1/2 + 1/2 * √2, 1/2 + 1/2 * √2],
    ![-1/2, 1/2 + 1/2 * √2, -1/2 - 1/2 * √2],
    ![-1/2, -1/2 - 1/2 * √2, 1/2 + 1/2 * √2],
    ![-1/2, -1/2 - 1/2 * √2, -1/2 - 1/2 * √2]].toFinset

end Nieuwland.Archimedean.TruncatedCube
