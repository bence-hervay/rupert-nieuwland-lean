import Polyhedra.Other.KAlphaSqrt3_3.Definition
import Polyhedra.Other.KAlphaSqrt3_3.Certificates.Shared

set_option linter.style.longLine false

/-!
# The solid `K_α` with `α = √3 / 3`: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Results.Gen.KAlphaSqrt3_3

open Check Cert

theorem eq_smul : Other.KAlphaSqrt3_3.polyhedron = (Polyhedron.ofPoints points).smul (1 / 3) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Results.Gen.KAlphaSqrt3_3
