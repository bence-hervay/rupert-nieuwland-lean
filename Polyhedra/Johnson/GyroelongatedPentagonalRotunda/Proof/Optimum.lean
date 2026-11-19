import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalRotunda.Polynomials
import Polyhedra.Johnson.GyroelongatedPentagonalRotunda.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedPentagonalRotunda.Proof.Pose

/-!
# The gyroelongated pentagonal rotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedPentagonalRotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedPentagonalRotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 48 39 57 :=
  Polyhedra.johnsonGyroelongatedPentagonalRotunda_pose_of_reps Polyhedra.johnsonGyroelongatedPentagonalRotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedPentagonalRotunda.Proof
