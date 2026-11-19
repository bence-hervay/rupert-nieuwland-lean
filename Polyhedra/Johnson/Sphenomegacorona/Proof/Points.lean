import Polyhedra.Johnson.Sphenomegacorona.Definition
import Polyhedra.Johnson.Sphenomegacorona.Certificates.Shared

set_option linter.style.longLine false

/-!
# The sphenomegacorona: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonSphenomegacorona

open Check Cert

theorem eq_smul : Johnson.Sphenomegacorona.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1888264263803826003739599711025604898277004939146768087406735920629109963294687916648594149841308593750000000000000) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.Sphenomegacorona.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11]

end Nieuwland.Certs.NieuwlandJohnsonSphenomegacorona
