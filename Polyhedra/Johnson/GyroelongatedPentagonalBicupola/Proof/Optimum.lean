import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalBicupola.Polynomials
import Polyhedra.Johnson.GyroelongatedPentagonalBicupola.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedPentagonalBicupola.Proof.Pose

/-!
# The gyroelongated pentagonal bicupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedPentagonalBicupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedPentagonalBicupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 61 52 70 :=
  Polyhedra.johnsonGyroelongatedPentagonalBicupola_pose_of_reps Polyhedra.johnsonGyroelongatedPentagonalBicupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedPentagonalBicupola.Proof
