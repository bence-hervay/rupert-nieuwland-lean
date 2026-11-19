import Polyhedra.Johnson.MetabigyrateRhombicosidodecahedron.Proof.Nopert

/-!
# The metabigyrate rhombicosidodecahedron: the result

The metabigyrate rhombicosidodecahedron is a Nopert: no copy of it fits through a hole in it.
-/

namespace Nieuwland.Johnson.MetabigyrateRhombicosidodecahedron

open Notation

/-- **The metabigyrate rhombicosidodecahedron is a Nopert**: it is not Rupert. -/
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

end Nieuwland.Johnson.MetabigyrateRhombicosidodecahedron
