import Modules.Pose.Optimum
import Polyhedra.Johnson.GyrateRhombicosidodecahedron.Proof.Certificate
import Polyhedra.Johnson.GyrateRhombicosidodecahedron.Proof.FullDim

/-!
# The gyrate rhombicosidodecahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Johnson.GyrateRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyrateRhombicosidodecahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.johnsonGyrateRhombicosidodecahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Johnson.GyrateRhombicosidodecahedron.Proof
