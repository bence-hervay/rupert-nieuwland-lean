import Polyhedra.Johnson.AugmentedSphenocorona.Definition
import Polyhedra.Johnson.AugmentedSphenocorona.Certificates.Shared

set_option linter.style.longLine false

/-!
# The augmented sphenocorona: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonAugmentedSphenocorona

open Check Cert

theorem eq_smul : Johnson.AugmentedSphenocorona.polyhedron = (Polyhedron.ofPoints points).smul (1 / 50157345418081908189426201600000000000000) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.AugmentedSphenocorona.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10]

end Nieuwland.Certs.NieuwlandJohnsonAugmentedSphenocorona
