import Modules.Pose.Optimum
import Polyhedra.Johnson.BiaugmentedTruncatedCube.Polynomials
import Polyhedra.Johnson.BiaugmentedTruncatedCube.Proof.Representatives
import Polyhedra.Johnson.BiaugmentedTruncatedCube.Proof.Pose

/-!
# The biaugmented truncated cube: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.BiaugmentedTruncatedCube.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonBiaugmentedTruncatedCube_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 47 38 56 :=
  Polyhedra.johnsonBiaugmentedTruncatedCube_pose_of_reps Polyhedra.johnsonBiaugmentedTruncatedCube_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.BiaugmentedTruncatedCube.Proof
