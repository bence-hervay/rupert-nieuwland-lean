import Modules.Pose.Optimum
import Polyhedra.Johnson.ParabigyrateRhombicosidodecahedron.Proof.Certificate
import Polyhedra.Johnson.ParabigyrateRhombicosidodecahedron.Proof.FullDim

/-!
# The parabigyrate rhombicosidodecahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Johnson.ParabigyrateRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonParabigyrateRhombicosidodecahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.johnsonParabigyrateRhombicosidodecahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Johnson.ParabigyrateRhombicosidodecahedron.Proof
