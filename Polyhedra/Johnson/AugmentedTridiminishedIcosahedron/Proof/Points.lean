import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Definition
import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Certificates.Shared

set_option linter.style.longLine false

/-!
# The augmented tridiminished icosahedron: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonAugmentedTridiminishedIcosahedron

open Check Cert

theorem eq_smul : Johnson.AugmentedTridiminishedIcosahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 192) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.AugmentedTridiminishedIcosahedron.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Certs.NieuwlandJohnsonAugmentedTridiminishedIcosahedron
