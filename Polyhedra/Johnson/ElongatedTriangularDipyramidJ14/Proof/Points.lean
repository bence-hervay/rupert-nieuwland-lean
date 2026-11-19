import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Definition
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Certificates.Shared

set_option linter.style.longLine false

/-!
# The elongated triangular dipyramid j14: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14

open Check Cert

theorem eq_smul : Johnson.ElongatedTriangularDipyramidJ14.polyhedron = (Polyhedron.ofPoints points).smul (1 / 252) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.ElongatedTriangularDipyramidJ14.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Certs.NieuwlandJohnsonElongatedTriangularDipyramidJ14
