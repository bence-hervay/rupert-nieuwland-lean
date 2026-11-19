import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedPentagonalRotunda.Polynomials
import Polyhedra.Johnson.ElongatedPentagonalRotunda.Proof.Representatives
import Polyhedra.Johnson.ElongatedPentagonalRotunda.Proof.Pose

/-!
# The elongated pentagonal rotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalRotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedPentagonalRotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 58 49 67 :=
  Polyhedra.johnsonElongatedPentagonalRotunda_pose_of_reps Polyhedra.johnsonElongatedPentagonalRotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedPentagonalRotunda.Proof
