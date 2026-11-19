import Modules.Pose.Optimum
import Polyhedra.Catalan.DeltoidalHexecontahedron.Proof.Certificate
import Polyhedra.Catalan.DeltoidalHexecontahedron.Proof.FullDim

/-!
# The deltoidal hexecontahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Catalan.DeltoidalHexecontahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.catalanDeltoidalHexecontahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.catalanDeltoidalHexecontahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Catalan.DeltoidalHexecontahedron.Proof
