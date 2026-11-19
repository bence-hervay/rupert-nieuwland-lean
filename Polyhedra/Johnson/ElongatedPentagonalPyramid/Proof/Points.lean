import Polyhedra.Johnson.ElongatedPentagonalPyramid.Definition
import Polyhedra.Johnson.ElongatedPentagonalPyramid.Certificates.Shared

set_option linter.style.longLine false

/-!
# The elongated pentagonal pyramid: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalPyramid

open Check Cert

theorem eq_smul : Johnson.ElongatedPentagonalPyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.ElongatedPentagonalPyramid.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10]

end Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalPyramid
