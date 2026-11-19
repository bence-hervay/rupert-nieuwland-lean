import Polyhedra.Johnson.Hebesphenomegacorona.Definition
import Polyhedra.Johnson.Hebesphenomegacorona.Certificates.Shared

set_option linter.style.longLine false

/-!
# The hebesphenomegacorona: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonHebesphenomegacorona

open Check Cert

theorem eq_smul : Johnson.Hebesphenomegacorona.polyhedron = (Polyhedron.ofPoints points).smul (1 / 926613804714872827110506303438711437137781125381978932157738594780944793600000000000000000) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.Hebesphenomegacorona.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13]

end Nieuwland.Certs.NieuwlandJohnsonHebesphenomegacorona
