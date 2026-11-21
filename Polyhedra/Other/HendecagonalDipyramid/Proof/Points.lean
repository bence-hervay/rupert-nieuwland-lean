import Polyhedra.Other.HendecagonalDipyramid.Definition
import Polyhedra.Other.HendecagonalDipyramid.Certificates.Shared

set_option linter.style.longLine false

/-!
# The hendecagonal dipyramid: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandDipyramidHendecagonalDipyramid

open Check Cert

theorem eq_smul : Other.HendecagonalDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Other.HendecagonalDipyramid.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12]

end Nieuwland.Certs.NieuwlandDipyramidHendecagonalDipyramid
