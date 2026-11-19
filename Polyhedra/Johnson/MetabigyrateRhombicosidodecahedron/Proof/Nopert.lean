import Modules.Pose.Optimum
import Polyhedra.Johnson.MetabigyrateRhombicosidodecahedron.Proof.Certificate
import Polyhedra.Johnson.MetabigyrateRhombicosidodecahedron.Proof.FullDim

/-!
# The metabigyrate rhombicosidodecahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Johnson.MetabigyrateRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonMetabigyrateRhombicosidodecahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.johnsonMetabigyrateRhombicosidodecahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Johnson.MetabigyrateRhombicosidodecahedron.Proof
