import Polyhedra.Johnson.AugmentedTriangularPrism.Definition
import Polyhedra.Johnson.AugmentedTriangularPrism.Certificates.Shared

set_option linter.style.longLine false

/-!
# The augmented triangular prism: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandJohnsonAugmentedTriangularPrism

open Check Cert

theorem eq_smul : Johnson.AugmentedTriangularPrism.polyhedron = (Polyhedron.ofPoints points).smul (1 / 144) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Johnson.AugmentedTriangularPrism.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6]

end Nieuwland.Certs.NieuwlandJohnsonAugmentedTriangularPrism
