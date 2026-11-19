import Modules.Pose.Optimum
import Polyhedra.Johnson.AugmentedHexagonalPrism.Polynomials
import Polyhedra.Johnson.AugmentedHexagonalPrism.Proof.Representatives
import Polyhedra.Johnson.AugmentedHexagonalPrism.Proof.Pose

/-!
# The augmented hexagonal prism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.AugmentedHexagonalPrism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonAugmentedHexagonalPrism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 57 48 66 :=
  Polyhedra.johnsonAugmentedHexagonalPrism_pose_of_reps Polyhedra.johnsonAugmentedHexagonalPrism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.AugmentedHexagonalPrism.Proof
