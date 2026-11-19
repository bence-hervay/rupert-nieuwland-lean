import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The icosahedron

The polyhedron `Platonic.Icosahedron.polyhedron`: the convex hull of 12 points.
-/

namespace Nieuwland.Platonic.Icosahedron

open Classical in
/-- The icosahedron: the convex hull of these 12 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 0, 1/4 + 1/4 * √5],
    ![1/2, 0, -1/4 - 1/4 * √5],
    ![-1/2, 0, 1/4 + 1/4 * √5],
    ![-1/2, 0, -1/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, 0],
    ![1/4 + 1/4 * √5, -1/2, 0],
    ![-1/4 - 1/4 * √5, 1/2, 0],
    ![-1/4 - 1/4 * √5, -1/2, 0],
    ![0, 1/4 + 1/4 * √5, 1/2],
    ![0, 1/4 + 1/4 * √5, -1/2],
    ![0, -1/4 - 1/4 * √5, 1/2],
    ![0, -1/4 - 1/4 * √5, -1/2]].toFinset

end Nieuwland.Platonic.Icosahedron
