import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Polynomials
import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Proof.Representatives
import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Proof.Pose

/-!
# The elongated pentagonal orthobirotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalOrthobirotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedPentagonalOrthobirotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 60 51 69 :=
  Polyhedra.johnsonElongatedPentagonalOrthobirotunda_pose_of_reps Polyhedra.johnsonElongatedPentagonalOrthobirotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedPentagonalOrthobirotunda.Proof
