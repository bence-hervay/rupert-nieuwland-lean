import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The rhombicuboctahedron

The polyhedron `Archimedean.Rhombicuboctahedron.polyhedron`: the convex hull of 24 points.
-/

namespace Nieuwland.Archimedean.Rhombicuboctahedron

open Classical in
/-- The rhombicuboctahedron: the convex hull of these 24 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 1/2, 1/2 + 1/2 * √2],
    ![1/2, 1/2, -1/2 - 1/2 * √2],
    ![1/2, -1/2, 1/2 + 1/2 * √2],
    ![1/2, -1/2, -1/2 - 1/2 * √2],
    ![-1/2, 1/2, 1/2 + 1/2 * √2],
    ![-1/2, 1/2, -1/2 - 1/2 * √2],
    ![-1/2, -1/2, 1/2 + 1/2 * √2],
    ![-1/2, -1/2, -1/2 - 1/2 * √2],
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

end Nieuwland.Archimedean.Rhombicuboctahedron
