import Modules.Pose.Optimum
import Polyhedra.Johnson.Bilunabirotunda.Polynomials
import Polyhedra.Johnson.Bilunabirotunda.Proof.Representatives
import Polyhedra.Johnson.Bilunabirotunda.Proof.Pose

/-!
# The bilunabirotunda: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.Bilunabirotunda.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonBilunabirotunda_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 45 36 54 :=
  Polyhedra.johnsonBilunabirotunda_pose_of_reps Polyhedra.johnsonBilunabirotunda_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.Bilunabirotunda.Proof
