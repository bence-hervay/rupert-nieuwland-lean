import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The metabidiminished icosahedron

The polyhedron `Johnson.MetabidiminishedIcosahedron.polyhedron`: the convex hull of 10 points.
-/

namespace Nieuwland.Johnson.MetabidiminishedIcosahedron

open Classical in
/-- The metabidiminished icosahedron: the convex hull of these 10 points. -/
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
    ![0, 1/4 + 1/4 * √5, -1/2],
    ![0, -1/4 - 1/4 * √5, -1/2]].toFinset

end Nieuwland.Johnson.MetabidiminishedIcosahedron
