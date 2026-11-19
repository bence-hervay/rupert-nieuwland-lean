import Definitions.Polyhedra
import Mathlib.Analysis.Real.Sqrt

/-!
# The disdyakis dodecahedron

The polyhedron `Catalan.DisdyakisDodecahedron.polyhedron`: the convex hull of 26 points.
-/

namespace Nieuwland.Catalan.DisdyakisDodecahedron

open Classical in
/-- The disdyakis dodecahedron: the convex hull of these 26 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![0, 0, 6/7 + 9/7 * √2],
    ![0, 0, -6/7 - 9/7 * √2],
    ![6/7 + 9/7 * √2, 0, 0],
    ![-6/7 - 9/7 * √2, 0, 0],
    ![0, 6/7 + 9/7 * √2, 0],
    ![0, -6/7 - 9/7 * √2, 0],
    ![3/7 + 6/7 * √2, 0, 3/7 + 6/7 * √2],
    ![3/7 + 6/7 * √2, 0, -3/7 - 6/7 * √2],
    ![-3/7 - 6/7 * √2, 0, 3/7 + 6/7 * √2],
    ![-3/7 - 6/7 * √2, 0, -3/7 - 6/7 * √2],
    ![3/7 + 6/7 * √2, 3/7 + 6/7 * √2, 0],
    ![3/7 + 6/7 * √2, -3/7 - 6/7 * √2, 0],
    ![-3/7 - 6/7 * √2, 3/7 + 6/7 * √2, 0],
    ![-3/7 - 6/7 * √2, -3/7 - 6/7 * √2, 0],
    ![0, 3/7 + 6/7 * √2, 3/7 + 6/7 * √2],
    ![0, 3/7 + 6/7 * √2, -3/7 - 6/7 * √2],
    ![0, -3/7 - 6/7 * √2, 3/7 + 6/7 * √2],
    ![0, -3/7 - 6/7 * √2, -3/7 - 6/7 * √2],
    ![√2, √2, √2],
    ![√2, √2, -(√2)],
    ![√2, -(√2), √2],
    ![√2, -(√2), -(√2)],
    ![-(√2), √2, √2],
    ![-(√2), √2, -(√2)],
    ![-(√2), -(√2), √2],
    ![-(√2), -(√2), -(√2)]].toFinset

end Nieuwland.Catalan.DisdyakisDodecahedron
