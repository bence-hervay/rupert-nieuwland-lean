import Polyhedra.Platonic.Dodecahedron.Definition
import Polyhedra.Platonic.Dodecahedron.Certificates.Shared

set_option linter.style.longLine false

/-!
# The dodecahedron: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandPlatonicDodecahedron

open Check Cert

theorem eq_smul : Platonic.Dodecahedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18, pt19]

end Nieuwland.Certs.NieuwlandPlatonicDodecahedron
