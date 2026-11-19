import Modules.Pose.Optimum
import Polyhedra.Johnson.TriaugmentedHexagonalPrism.Polynomials
import Polyhedra.Johnson.TriaugmentedHexagonalPrism.Proof.Representatives
import Polyhedra.Johnson.TriaugmentedHexagonalPrism.Proof.Pose

/-!
# The triaugmented hexagonal prism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.TriaugmentedHexagonalPrism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonTriaugmentedHexagonalPrism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 51 42 60 :=
  Polyhedra.johnsonTriaugmentedHexagonalPrism_pose_of_reps Polyhedra.johnsonTriaugmentedHexagonalPrism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.TriaugmentedHexagonalPrism.Proof
