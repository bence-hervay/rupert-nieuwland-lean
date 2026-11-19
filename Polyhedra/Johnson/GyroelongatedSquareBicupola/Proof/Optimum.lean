import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedSquareBicupola.Polynomials
import Polyhedra.Johnson.GyroelongatedSquareBicupola.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedSquareBicupola.Proof.Pose

/-!
# The gyroelongated square bicupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedSquareBicupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedSquareBicupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 61 52 70 :=
  Polyhedra.johnsonGyroelongatedSquareBicupola_pose_of_reps Polyhedra.johnsonGyroelongatedSquareBicupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedSquareBicupola.Proof
