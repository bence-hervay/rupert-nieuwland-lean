import Polyhedra.Johnson.ElongatedPentagonalDipyramidJ16.Definition
import Polyhedra.Johnson.ElongatedPentagonalDipyramidJ16.Certificates.Shared

set_option linter.style.longLine false

/-!
# The elongated pentagonal dipyramid j16: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalDipyramidJ16

open Check Cert

theorem eq_smul : Johnson.ElongatedPentagonalDipyramidJ16.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.ElongatedPentagonalDipyramidJ16.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalDipyramidJ16
