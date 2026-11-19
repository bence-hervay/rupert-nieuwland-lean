import Polyhedra.Johnson.GyroelongatedTriangularBicupola.Definition
import Polyhedra.Johnson.GyroelongatedTriangularBicupola.Certificates.Shared

set_option linter.style.longLine false

/-!
# The gyroelongated triangular bicupola: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonGyroelongatedTriangularBicupola

open Check Cert

theorem eq_smul : Johnson.GyroelongatedTriangularBicupola.polyhedron = (Polyhedron.ofPoints points).smul (1 / 132881278464) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.GyroelongatedTriangularBicupola.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17]

end Nieuwland.Certs.NieuwlandJohnsonGyroelongatedTriangularBicupola
