import Polyhedra.Archimedean.SnubDodecahedronLaevo.Proof.Nopert
import Polyhedra.Archimedean.SnubDodecahedronLaevo.Proof.Theta

/-!
# The snub dodecahedron laevo: the result

The snub dodecahedron laevo is a Nopert: no copy of it fits through a hole in it.
-/

namespace Nieuwland.Archimedean.SnubDodecahedronLaevo

open Notation

/-- **The snub dodecahedron laevo is a Nopert**: it is not Rupert. -/
theorem isNopert : polyhedron.IsNopert :=
  Proof.isNopert

/-- Its Nieuwland number is `1`: every smaller copy of the polyhedron fits through it, and no
larger one does. -/
theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Proof.nieuwland_eq_one

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

@[inherit_doc] local notation "θ" => theta

/-- **`θ` is a root of its polynomial**, and it lies between these two rationals, which are at most
`2 ^ -100` apart. -/
theorem theta_isRoot :
    polyEval [-1, 2, 4, -1, -4, 0, 1] θ = 0 ∧
      (1.7155614996973678346812788888899 : ℝ) ≤ θ ∧
      θ ≤ (1.71556149969736783468127888889 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Archimedean.SnubDodecahedronLaevo
