import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The triakis octahedron

The polyhedron `Catalan.TriakisOctahedron.polyhedron`: the convex hull of 14 points.
-/

namespace Nieuwland.Catalan.TriakisOctahedron

open Classical in
/-- The triakis octahedron: the convex hull of these 14 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 1 + √2],
    ![0, 0, -1 - √2],
    ![1 + √2, 0, 0],
    ![-1 - √2, 0, 0],
    ![0, 1 + √2, 0],
    ![0, -1 - √2, 0],
    ![1, 1, 1],
    ![1, 1, -1],
    ![1, -1, 1],
    ![1, -1, -1],
    ![-1, 1, 1],
    ![-1, 1, -1],
    ![-1, -1, 1],
    ![-1, -1, -1]].toFinset

end Nieuwland.Catalan.TriakisOctahedron
