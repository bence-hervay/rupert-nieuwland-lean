import Modules.Pose.Optimum
import Polyhedra.Other.KAlpha1_2.Proof.Certificate
import Polyhedra.Other.KAlpha1_2.Proof.FullDim

/-!
# The solid `K_α` with `α = 1 / 2`: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.KAlpha1_2.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.kAlpha1_2_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.kAlpha1_2_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.KAlpha1_2.Proof
