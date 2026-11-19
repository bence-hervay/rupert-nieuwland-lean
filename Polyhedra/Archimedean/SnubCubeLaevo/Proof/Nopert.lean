import Modules.Pose.Optimum
import Polyhedra.Archimedean.SnubCubeLaevo.Proof.Certificate
import Polyhedra.Archimedean.SnubCubeLaevo.Proof.FullDim

/-!
# The snub cube laevo: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Archimedean.SnubCubeLaevo.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanSnubCubeLaevo_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.archimedeanSnubCubeLaevo_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Archimedean.SnubCubeLaevo.Proof
