import Modules.Pose.Optimum
import Polyhedra.Other.KAlpha11_20.Proof.Certificate
import Polyhedra.Other.KAlpha11_20.Proof.FullDim

/-!
# The solid `K_α` with `α = 11 / 20`: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.KAlpha11_20.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.kAlpha11_20_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.kAlpha11_20_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.KAlpha11_20.Proof
