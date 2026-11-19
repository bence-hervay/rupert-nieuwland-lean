import Modules.Pose.Optimum
import Polyhedra.Archimedean.Rhombicosidodecahedron.Proof.Certificate
import Polyhedra.Archimedean.Rhombicosidodecahedron.Proof.FullDim

/-!
# The rhombicosidodecahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Archimedean.Rhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanRhombicosidodecahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.archimedeanRhombicosidodecahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Archimedean.Rhombicosidodecahedron.Proof
