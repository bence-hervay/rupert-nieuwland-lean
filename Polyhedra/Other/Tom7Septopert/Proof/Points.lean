import Polyhedra.Other.Tom7Septopert.Definition
import Polyhedra.Other.Tom7Septopert.Certificates.Shared

set_option linter.style.longLine false

/-!
# The septopert of Tom 7: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert

open Check Cert

theorem eq_smul : Other.Tom7Septopert.polyhedron = (Polyhedron.ofPoints points).smul (1 / 1048576) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6]

end Nieuwland.Results.Gen.ExternalTom7Septopert
