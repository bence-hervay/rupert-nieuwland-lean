import Polyhedra.Other.SquareTrapezohedron.Definition
import Polyhedra.Other.SquareTrapezohedron.Certificates.Shared

set_option linter.style.longLine false

/-!
# The square trapezohedron: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Certs.NieuwlandTrapezohedronSquareTrapezohedron

open Check Cert

theorem eq_smul : Other.SquareTrapezohedron.polyhedron = (Polyhedron.ofPoints points).smul (1 / 3) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [Nieuwland.Other.SquareTrapezohedron.theta, points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9]

end Nieuwland.Certs.NieuwlandTrapezohedronSquareTrapezohedron
