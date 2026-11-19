import Polyhedra.Prism.TriangularPrism.Definition
import Polyhedra.Prism.TriangularPrism.Certificates.Shared

set_option linter.style.longLine false

/-!
# The triangular prism: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandPrismTriangularPrism

open Check Cert

theorem eq_smul : Prism.TriangularPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 6) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5]

end Nieuwland.Certs.NieuwlandPrismTriangularPrism
