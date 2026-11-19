import Polyhedra.Johnson.PentagonalDipyramidJ13.Definition
import Polyhedra.Johnson.PentagonalDipyramidJ13.Certificates.Shared

set_option linter.style.longLine false

/-!
# The pentagonal dipyramid j13: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13

open Check Cert

theorem eq_smul : Johnson.PentagonalDipyramidJ13.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.PentagonalDipyramidJ13.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6]

end Nieuwland.Certs.NieuwlandJohnsonPentagonalDipyramidJ13
