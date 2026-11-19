import Polyhedra.Prism.PentagonalPrism.Definition
import Polyhedra.Prism.PentagonalPrism.Certificates.Shared

set_option linter.style.longLine false

/-!
# The pentagonal prism: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandPrismPentagonalPrism

open Check Cert

theorem eq_smul : Prism.PentagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Prism.PentagonalPrism.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Certs.NieuwlandPrismPentagonalPrism
