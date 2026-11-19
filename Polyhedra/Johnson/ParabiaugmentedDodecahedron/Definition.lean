import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The parabiaugmented dodecahedron

The polyhedron `Johnson.ParabiaugmentedDodecahedron.polyhedron`: the convex hull of 22 points.
-/

namespace Nieuwland.Johnson.ParabiaugmentedDodecahedron

open Classical in
/-- The parabiaugmented dodecahedron: the convex hull of these 22 points. -/
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
    ![0, 1/2 + 2/5 * √5, -3/4 - 1/20 * √5],
    ![0, -1/2 - 2/5 * √5, 3/4 + 1/20 * √5]].toFinset

end Nieuwland.Johnson.ParabiaugmentedDodecahedron
