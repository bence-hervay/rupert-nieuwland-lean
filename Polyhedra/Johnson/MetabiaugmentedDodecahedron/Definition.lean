import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The metabiaugmented dodecahedron

The polyhedron `Johnson.MetabiaugmentedDodecahedron.polyhedron`: the convex hull of 22 points.
-/

namespace Nieuwland.Johnson.MetabiaugmentedDodecahedron

open Classical in
/-- The metabiaugmented dodecahedron: the convex hull of these 22 points. -/
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
    ![0, 1/2 + 2/5 * √5, 3/4 + 1/20 * √5],
    ![0, -1/2 - 2/5 * √5, 3/4 + 1/20 * √5]].toFinset

end Nieuwland.Johnson.MetabiaugmentedDodecahedron
