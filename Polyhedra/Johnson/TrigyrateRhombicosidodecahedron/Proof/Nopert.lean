import Modules.Pose.Optimum
import Polyhedra.Johnson.TrigyrateRhombicosidodecahedron.Proof.Certificate
import Polyhedra.Johnson.TrigyrateRhombicosidodecahedron.Proof.FullDim

/-!
# The trigyrate rhombicosidodecahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Johnson.TrigyrateRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonTrigyrateRhombicosidodecahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.johnsonTrigyrateRhombicosidodecahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Johnson.TrigyrateRhombicosidodecahedron.Proof
