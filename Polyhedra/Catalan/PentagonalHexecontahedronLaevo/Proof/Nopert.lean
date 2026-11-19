import Modules.Pose.Optimum
import Polyhedra.Catalan.PentagonalHexecontahedronLaevo.Proof.Certificate
import Polyhedra.Catalan.PentagonalHexecontahedronLaevo.Proof.FullDim

/-!
# The pentagonal hexecontahedron laevo: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Catalan.PentagonalHexecontahedronLaevo.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.catalanPentagonalHexecontahedronLaevo_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.catalanPentagonalHexecontahedronLaevo_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Catalan.PentagonalHexecontahedronLaevo.Proof
