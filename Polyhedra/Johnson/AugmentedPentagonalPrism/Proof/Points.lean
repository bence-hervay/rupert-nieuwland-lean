import Polyhedra.Johnson.AugmentedPentagonalPrism.Definition
import Polyhedra.Johnson.AugmentedPentagonalPrism.Certificates.Shared

set_option linter.style.longLine false

/-!
# The augmented pentagonal prism: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism

open Check

theorem eq_smul : Johnson.AugmentedPentagonalPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 220) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.AugmentedPentagonalPrism.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10]

end Nieuwland.Certs.NieuwlandJohnsonAugmentedPentagonalPrism
