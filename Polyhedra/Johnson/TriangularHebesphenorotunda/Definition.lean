import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The triangular hebesphenorotunda

The polyhedron `Johnson.TriangularHebesphenorotunda.polyhedron`: the convex hull of 18 points.
-/

namespace Nieuwland.Johnson.TriangularHebesphenorotunda

open Classical in
/-- The triangular hebesphenorotunda: the convex hull of these 18 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![15/32 + 11/32 * √5, -1/32 - 5/32 * √5, -1/32 - 5/32 * √5],
    ![-1/32 - 5/32 * √5, 15/32 + 11/32 * √5, -1/32 - 5/32 * √5],
    ![-1/32 - 5/32 * √5, -1/32 - 5/32 * √5, 15/32 + 11/32 * √5],
    ![23/32 + 3/32 * √5, 7/32 + 3/32 * √5, -17/32 - 5/32 * √5],
    ![-17/32 - 5/32 * √5, 23/32 + 3/32 * √5, 7/32 + 3/32 * √5],
    ![7/32 + 3/32 * √5, -17/32 - 5/32 * √5, 23/32 + 3/32 * √5],
    ![7/32 + 3/32 * √5, -17/32 - 5/32 * √5, 7/32 - 13/32 * √5],
    ![7/32 - 13/32 * √5, 7/32 + 3/32 * √5, -17/32 - 5/32 * √5],
    ![-17/32 - 5/32 * √5, 7/32 - 13/32 * √5, 7/32 + 3/32 * √5],
    ![15/32 - 5/32 * √5, -9/32 + 3/32 * √5, -9/32 - 13/32 * √5],
    ![-9/32 - 13/32 * √5, 15/32 - 5/32 * √5, -9/32 + 3/32 * √5],
    ![-9/32 + 3/32 * √5, -9/32 - 13/32 * √5, 15/32 - 5/32 * √5],
    ![23/32 + 3/32 * √5, 7/32 + 3/32 * √5, 15/32 - 5/32 * √5],
    ![15/32 - 5/32 * √5, 23/32 + 3/32 * √5, 7/32 + 3/32 * √5],
    ![7/32 + 3/32 * √5, 15/32 - 5/32 * √5, 23/32 + 3/32 * √5],
    ![23/32 + 3/32 * √5, -9/32 - 13/32 * √5, 15/32 - 5/32 * √5],
    ![15/32 - 5/32 * √5, 23/32 + 3/32 * √5, -9/32 - 13/32 * √5],
    ![-9/32 - 13/32 * √5, 15/32 - 5/32 * √5, 23/32 + 3/32 * √5]].toFinset

end Nieuwland.Johnson.TriangularHebesphenorotunda
