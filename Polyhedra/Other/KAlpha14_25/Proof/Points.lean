import Polyhedra.Other.KAlpha14_25.Definition
import Polyhedra.Other.KAlpha14_25.Certificates.Shared

set_option linter.style.longLine false

/-!
# The solid `K_α` with `α = 14 / 25`: the certificate's points

The points of the certificate are the polyhedron's (cut from the certificate's shared data,
whose other modules do not name the polyhedron).
-/

namespace Nieuwland.Results.Gen.KAlpha14_25

open Check Cert

theorem eq_smul : Other.KAlpha14_25.polyhedron = (Polyhedron.ofPoints points).smul (1 / 25) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7]

end Nieuwland.Results.Gen.KAlpha14_25
