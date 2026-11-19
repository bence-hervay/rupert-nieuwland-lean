import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedSquarePyramid.Polynomials
import Polyhedra.Johnson.GyroelongatedSquarePyramid.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedSquarePyramid.Proof.Pose

/-!
# The gyroelongated square pyramid: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedSquarePyramid.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedSquarePyramid_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 53 44 62 :=
  Polyhedra.johnsonGyroelongatedSquarePyramid_pose_of_reps Polyhedra.johnsonGyroelongatedSquarePyramid_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedSquarePyramid.Proof
