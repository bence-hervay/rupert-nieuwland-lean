import Polyhedra.Johnson.TriangularDipyramidJ12.Definition
import Polyhedra.Johnson.TriangularDipyramidJ12.Certificates.Shared

set_option linter.style.longLine false

/-!
# The triangular dipyramid j12: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonTriangularDipyramidJ12

open Check Cert

theorem eq_smul : Johnson.TriangularDipyramidJ12.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4]

end Nieuwland.Certs.NieuwlandJohnsonTriangularDipyramidJ12
