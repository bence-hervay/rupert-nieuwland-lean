import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The dodecahedron

The polyhedron `Platonic.Dodecahedron.polyhedron`: the convex hull of 20 points.
-/

namespace Nieuwland.Platonic.Dodecahedron

open Classical in
/-- The dodecahedron: the convex hull of these 20 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 1/2, 3/4 + 1/4 * √5],
    ![0, 1/2, -3/4 - 1/4 * √5],
    ![0, -1/2, 3/4 + 1/4 * √5],
    ![0, -1/2, -3/4 - 1/4 * √5],
    ![3/4 + 1/4 * √5, 0, 1/2],
    ![3/4 + 1/4 * √5, 0, -1/2],
    ![-3/4 - 1/4 * √5, 0, 1/2],
    ![-3/4 - 1/4 * √5, 0, -1/2],
    ![1/2, 3/4 + 1/4 * √5, 0],
    ![1/2, -3/4 - 1/4 * √5, 0],
    ![-1/2, 3/4 + 1/4 * √5, 0],
    ![-1/2, -3/4 - 1/4 * √5, 0],
    ![1/4 + 1/4 * √5, 1/4 + 1/4 * √5, 1/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, -1/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![1/4 + 1/4 * √5, -1/4 - 1/4 * √5, -1/4 - 1/4 * √5],
    ![-1/4 - 1/4 * √5, 1/4 + 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/4 - 1/4 * √5, 1/4 + 1/4 * √5, -1/4 - 1/4 * √5],
    ![-1/4 - 1/4 * √5, -1/4 - 1/4 * √5, 1/4 + 1/4 * √5],
    ![-1/4 - 1/4 * √5, -1/4 - 1/4 * √5, -1/4 - 1/4 * √5]].toFinset

end Nieuwland.Platonic.Dodecahedron
