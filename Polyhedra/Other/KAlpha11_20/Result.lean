import Polyhedra.Other.KAlpha11_20.Proof.Nopert

/-!
# The solid `K_α` with `α = 11 / 20`: the result

The solid `K_α` with `α = 11 / 20` is a Nopert: no copy of it fits through a hole in it.
-/

namespace Nieuwland.Other.KAlpha11_20

open Notation

/-- **The solid `K_α` with `α = 11 / 20` is a Nopert**: it is not Rupert. -/
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

end Nieuwland.Other.KAlpha11_20
