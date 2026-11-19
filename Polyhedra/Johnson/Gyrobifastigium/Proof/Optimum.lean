import Modules.Pose.Optimum
import Polyhedra.Johnson.Gyrobifastigium.Polynomials
import Polyhedra.Johnson.Gyrobifastigium.Proof.Representatives
import Polyhedra.Johnson.Gyrobifastigium.Proof.Pose

/-!
# The gyrobifastigium: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.Gyrobifastigium.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyrobifastigium_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonGyrobifastigium_pose_of_reps Polyhedra.johnsonGyrobifastigium_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.Gyrobifastigium.Proof
