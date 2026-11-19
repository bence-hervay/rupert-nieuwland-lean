import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalCupolarotunda.Polynomials
import Polyhedra.Johnson.GyroelongatedPentagonalCupolarotunda.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedPentagonalCupolarotunda.Proof.Pose

/-!
# The gyroelongated pentagonal cupolarotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedPentagonalCupolarotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedPentagonalCupolarotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 58 49 67 :=
  Polyhedra.johnsonGyroelongatedPentagonalCupolarotunda_pose_of_reps Polyhedra.johnsonGyroelongatedPentagonalCupolarotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedPentagonalCupolarotunda.Proof
