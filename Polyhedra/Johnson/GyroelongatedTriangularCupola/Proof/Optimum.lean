import Modules.Pose.Optimum
import Polyhedra.Johnson.GyroelongatedTriangularCupola.Polynomials
import Polyhedra.Johnson.GyroelongatedTriangularCupola.Proof.Representatives
import Polyhedra.Johnson.GyroelongatedTriangularCupola.Proof.Pose

/-!
# The gyroelongated triangular cupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyroelongatedTriangularCupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyroelongatedTriangularCupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 55 46 64 :=
  Polyhedra.johnsonGyroelongatedTriangularCupola_pose_of_reps Polyhedra.johnsonGyroelongatedTriangularCupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyroelongatedTriangularCupola.Proof
