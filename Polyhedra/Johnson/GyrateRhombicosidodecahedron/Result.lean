import Polyhedra.Johnson.GyrateRhombicosidodecahedron.Proof.Nopert

/-!
# The gyrate rhombicosidodecahedron: the result

The gyrate rhombicosidodecahedron is a Nopert: no copy of it fits through a hole in it.
-/

namespace Nieuwland.Johnson.GyrateRhombicosidodecahedron

open Notation

/-- **The gyrate rhombicosidodecahedron is a Nopert**: it is not Rupert. -/
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

end Nieuwland.Johnson.GyrateRhombicosidodecahedron
