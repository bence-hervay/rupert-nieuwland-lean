import Polyhedra.Other.TriangularDipyramid.Definition
import Polyhedra.Other.TriangularDipyramid.Certificates.Shared

set_option linter.style.longLine false

/-!
# The triangular dipyramid: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandDipyramidTriangularDipyramid

open Check Cert

theorem eq_smul : Other.TriangularDipyramid.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4]

end Nieuwland.Certs.NieuwlandDipyramidTriangularDipyramid
