import Modules.Pose.Optimum
import Polyhedra.Johnson.AugmentedTruncatedCube.Polynomials
import Polyhedra.Johnson.AugmentedTruncatedCube.Proof.Representatives
import Polyhedra.Johnson.AugmentedTruncatedCube.Proof.Pose

/-!
# The augmented truncated cube: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.AugmentedTruncatedCube.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonAugmentedTruncatedCube_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 67 58 76 :=
  Polyhedra.johnsonAugmentedTruncatedCube_pose_of_reps Polyhedra.johnsonAugmentedTruncatedCube_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.AugmentedTruncatedCube.Proof
