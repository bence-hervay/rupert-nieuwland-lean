import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The tridiminished icosahedron

The polyhedron `Johnson.TridiminishedIcosahedron.polyhedron`: the convex hull of 9 points.
-/

namespace Nieuwland.Johnson.TridiminishedIcosahedron

open Classical in
/-- The tridiminished icosahedron: the convex hull of these 9 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![1/2, 0, 1/4 + 1/4 * √5],
    ![1/2, 0, -1/4 - 1/4 * √5],
    ![-1/2, 0, 1/4 + 1/4 * √5],
    ![-1/2, 0, -1/4 - 1/4 * √5],
    ![1/4 + 1/4 * √5, 1/2, 0],
    ![-1/4 - 1/4 * √5, 1/2, 0],
    ![0, -1/4 - 1/4 * √5, 1/2],
    ![0, -1/4 - 1/4 * √5, -1/2],
    ![0, 1/4 + 1/4 * √5, -1/2]].toFinset

end Nieuwland.Johnson.TridiminishedIcosahedron
