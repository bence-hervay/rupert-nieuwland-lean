import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The triaugmented dodecahedron

The polyhedron `Johnson.TriaugmentedDodecahedron.polyhedron`: the convex hull of 23 points.
-/

namespace Nieuwland.Johnson.TriaugmentedDodecahedron

open Classical in
/-- The triaugmented dodecahedron: the convex hull of these 23 points. -/
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
    ![1/2 + 2/5 * √5, 3/4 + 1/20 * √5, 0],
    ![-1/2 - 2/5 * √5, 3/4 + 1/20 * √5, 0],
    ![0, -1/2 - 2/5 * √5, 3/4 + 1/20 * √5]].toFinset

end Nieuwland.Johnson.TriaugmentedDodecahedron
