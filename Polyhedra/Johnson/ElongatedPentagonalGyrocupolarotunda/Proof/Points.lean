import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Definition
import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Certificates.Shared

set_option linter.style.longLine false

/-!
# The elongated pentagonal gyrocupolarotunda: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrocupolarotunda

open Check Cert

theorem eq_smul : Johnson.ElongatedPentagonalGyrocupolarotunda.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.ElongatedPentagonalGyrocupolarotunda.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19, pt20, pt21, pt22, pt23, pt24,
    pt25, pt26, pt27, pt28, pt29, pt30, pt31, pt32, pt33, pt34]

end Nieuwland.Certs.NieuwlandJohnsonElongatedPentagonalGyrocupolarotunda
