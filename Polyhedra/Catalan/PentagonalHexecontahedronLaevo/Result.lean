import Polyhedra.Catalan.PentagonalHexecontahedronLaevo.Proof.Nopert
import Polyhedra.Catalan.PentagonalHexecontahedronLaevo.Proof.Theta

/-!
# The pentagonal hexecontahedron laevo: the result

The pentagonal hexecontahedron laevo is a Nopert: no copy of it fits through a hole in it.
-/

namespace Nieuwland.Catalan.PentagonalHexecontahedronLaevo

open Notation

/-- **The pentagonal hexecontahedron laevo is a Nopert**: it is not Rupert. -/
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
    polyEval [1, -2, -1, 0, -2, 2, 1] θ = 0 ∧
      (1.1326619649523854202571098116849 : ℝ) ≤ θ ∧
      θ ≤ (1.132661964952385420257109811685 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Catalan.PentagonalHexecontahedronLaevo
