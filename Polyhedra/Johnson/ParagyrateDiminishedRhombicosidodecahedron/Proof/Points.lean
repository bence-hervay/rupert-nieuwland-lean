import Polyhedra.Johnson.ParagyrateDiminishedRhombicosidodecahedron.Definition
import Polyhedra.Johnson.ParagyrateDiminishedRhombicosidodecahedron.Certificates.Shared

set_option linter.style.longLine false

/-!
# The paragyrate diminished rhombicosidodecahedron: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Results.Gen.JohnsonParagyrateDiminishedRhombicosidodecahedron

open Check Cert

theorem eq_smul : Johnson.ParagyrateDiminishedRhombicosidodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 20) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37, pt38, pt39, pt40,
    pt41, pt42, pt43, pt44, pt45, pt46, pt47, pt48, pt49, pt50, pt51, pt52, pt53, pt54]

end Nieuwland.Results.Gen.JohnsonParagyrateDiminishedRhombicosidodecahedron
