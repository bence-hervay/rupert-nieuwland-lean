import Modules.Pose.Optimum
import Polyhedra.Johnson.PentagonalOrthobicupola.Polynomials
import Polyhedra.Johnson.PentagonalOrthobicupola.Proof.Representatives
import Polyhedra.Johnson.PentagonalOrthobicupola.Proof.Pose

/-!
# The pentagonal orthobicupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.PentagonalOrthobicupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonPentagonalOrthobicupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonPentagonalOrthobicupola_pose_of_reps Polyhedra.johnsonPentagonalOrthobicupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.PentagonalOrthobicupola.Proof
