import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Definition
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Certificates.Shared

set_option linter.style.longLine false

/-!
# The pentagonal icositetrahedron laevo: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandCatalanPentagonalIcositetrahedronLaevo

open Check Cert

theorem eq_smul : Catalan.PentagonalIcositetrahedronLaevo.polyhedron = (Polyhedron.ofPoints points).smul (1 / 2) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Catalan.PentagonalIcositetrahedronLaevo.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34, pt35, pt36, pt37]

end Nieuwland.Certs.NieuwlandCatalanPentagonalIcositetrahedronLaevo
