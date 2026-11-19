import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The augmented dodecahedron

The polyhedron `Johnson.AugmentedDodecahedron.polyhedron`: the convex hull of 21 points.
-/

namespace Nieuwland.Johnson.AugmentedDodecahedron

open Classical in
/-- The augmented dodecahedron: the convex hull of these 21 points. -/
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
    ![-1/4 - 1/4 * √5, -1/4 - 1/4 * √5, -1/4 - 1/4 * √5],
    ![0, 1/2 + 2/5 * √5, 3/4 + 1/20 * √5]].toFinset

end Nieuwland.Johnson.AugmentedDodecahedron
