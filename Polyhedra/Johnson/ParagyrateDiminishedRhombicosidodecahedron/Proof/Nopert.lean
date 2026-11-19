import Modules.Pose.Optimum
import Polyhedra.Johnson.ParagyrateDiminishedRhombicosidodecahedron.Proof.Certificate
import Polyhedra.Johnson.ParagyrateDiminishedRhombicosidodecahedron.Proof.FullDim

/-!
# The paragyrate diminished rhombicosidodecahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Johnson.ParagyrateDiminishedRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonParagyrateDiminishedRhombicosidodecahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.johnsonParagyrateDiminishedRhombicosidodecahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Johnson.ParagyrateDiminishedRhombicosidodecahedron.Proof
