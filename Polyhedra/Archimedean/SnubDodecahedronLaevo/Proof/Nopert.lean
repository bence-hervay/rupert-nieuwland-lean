import Modules.Pose.Optimum
import Polyhedra.Archimedean.SnubDodecahedronLaevo.Proof.Certificate
import Polyhedra.Archimedean.SnubDodecahedronLaevo.Proof.FullDim

/-!
# The snub dodecahedron laevo: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Archimedean.SnubDodecahedronLaevo.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanSnubDodecahedronLaevo_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.archimedeanSnubDodecahedronLaevo_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Archimedean.SnubDodecahedronLaevo.Proof
