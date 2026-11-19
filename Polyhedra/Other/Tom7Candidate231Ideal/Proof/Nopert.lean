import Modules.Pose.Optimum
import Polyhedra.Other.Tom7Candidate231Ideal.Proof.Certificate
import Polyhedra.Other.Tom7Candidate231Ideal.Proof.FullDim

/-!
# The candidate 231 of Tom 7 (ideal coordinates): a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.Tom7Candidate231Ideal.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.externalTom7Candidate231Ideal_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.externalTom7Candidate231Ideal_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.Tom7Candidate231Ideal.Proof
