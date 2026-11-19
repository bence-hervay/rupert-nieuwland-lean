import Polyhedra.Johnson.MetabiaugmentedHexagonalPrism.Definition
import Polyhedra.Johnson.MetabiaugmentedHexagonalPrism.Certificates.Shared

set_option linter.style.longLine false

/-!
# The metabiaugmented hexagonal prism: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonMetabiaugmentedHexagonalPrism

open Check Cert

theorem eq_smul : Johnson.MetabiaugmentedHexagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 8) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.MetabiaugmentedHexagonalPrism.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Certs.NieuwlandJohnsonMetabiaugmentedHexagonalPrism
