import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalBirotunda.Polynomials
import Polyhedra.Johnson.GyroelongatedPentagonalBirotunda.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedPentagonalBirotunda.Proof.Pose

/-!
# The gyroelongated pentagonal birotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedPentagonalBirotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedPentagonalBirotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 52 43 61 :=
  Polyhedra.johnsonGyroelongatedPentagonalBirotunda_pose_of_reps Polyhedra.johnsonGyroelongatedPentagonalBirotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedPentagonalBirotunda.Proof
