import Modules.Pose.Optimum
import Polyhedra.Other.Tom7Septopert.Proof.Certificate
import Polyhedra.Other.Tom7Septopert.Proof.FullDim

/-!
# The septopert of Tom 7: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.Tom7Septopert.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.externalTom7Septopert_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.externalTom7Septopert_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.Tom7Septopert.Proof
