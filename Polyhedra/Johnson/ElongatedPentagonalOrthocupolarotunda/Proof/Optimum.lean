import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedPentagonalOrthocupolarotunda.Polynomials
import Polyhedra.Johnson.ElongatedPentagonalOrthocupolarotunda.Proof.Representatives
import Polyhedra.Johnson.ElongatedPentagonalOrthocupolarotunda.Proof.Pose

/-!
# The elongated pentagonal orthocupolarotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalOrthocupolarotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedPentagonalOrthocupolarotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 61 52 70 :=
  Polyhedra.johnsonElongatedPentagonalOrthocupolarotunda_pose_of_reps Polyhedra.johnsonElongatedPentagonalOrthocupolarotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedPentagonalOrthocupolarotunda.Proof
