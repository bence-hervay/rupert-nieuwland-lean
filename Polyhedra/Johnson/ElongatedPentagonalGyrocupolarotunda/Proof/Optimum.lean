import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Polynomials
import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof.Representatives
import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof.Pose

/-!
# The elongated pentagonal gyrocupolarotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedPentagonalGyrocupolarotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 61 52 70 :=
  Polyhedra.johnsonElongatedPentagonalGyrocupolarotunda_pose_of_reps Polyhedra.johnsonElongatedPentagonalGyrocupolarotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof
