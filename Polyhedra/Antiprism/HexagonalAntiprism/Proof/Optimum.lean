import Modules.Pose.Optimum
import Polyhedra.Antiprism.HexagonalAntiprism.Polynomials
import Polyhedra.Antiprism.HexagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.HexagonalAntiprism.Proof.Pose

/-!
# The hexagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.HexagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismHexagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 52 43 61 :=
  Polyhedra.prismHexagonalAntiprism_pose_of_reps Polyhedra.prismHexagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.HexagonalAntiprism.Proof
