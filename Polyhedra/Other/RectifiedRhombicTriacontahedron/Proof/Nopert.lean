import Modules.Pose.Optimum
import Polyhedra.Other.RectifiedRhombicTriacontahedron.Proof.Certificate
import Polyhedra.Other.RectifiedRhombicTriacontahedron.Proof.FullDim

/-!
# The rectified rhombic triacontahedron: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.RectifiedRhombicTriacontahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.otherRectifiedRhombicTriacontahedron_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.otherRectifiedRhombicTriacontahedron_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.RectifiedRhombicTriacontahedron.Proof
