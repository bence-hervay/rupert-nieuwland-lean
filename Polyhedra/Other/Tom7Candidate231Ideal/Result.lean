import Polyhedra.Other.Tom7Candidate231Ideal.Proof.Nopert
import Polyhedra.Other.Tom7Candidate231Ideal.Proof.Theta

/-!
# The candidate 231 of Tom 7 (ideal coordinates): the result

The candidate 231 of Tom 7 (ideal coordinates) is a Nopert: no copy of it fits through a hole in it.
-/

namespace Nieuwland.Other.Tom7Candidate231Ideal

open Notation

/-- **The candidate 231 of Tom 7 (ideal coordinates) is a Nopert**: it is not Rupert. -/
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
    polyEval [5/16, 0, -5/4, 0, 1] θ = 0 ∧
      (0.9510565162951535721164393333793 : ℝ) ≤ θ ∧
      θ ≤ (0.9510565162951535721164393333794 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.Tom7Candidate231Ideal
