import Modules.Pose.Optimum
import Polyhedra.Other.Noperthedron.Proof.Certificate
import Polyhedra.Other.Noperthedron.Proof.FullDim

/-!
# The Noperthedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.Noperthedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.externalNoperthedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.externalNoperthedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.Noperthedron.Proof
