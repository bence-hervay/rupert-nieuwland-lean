import Modules.Pose.Optimum
import Polyhedra.Antiprism.PentagonalAntiprism.Polynomials
import Polyhedra.Antiprism.PentagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.PentagonalAntiprism.Proof.Pose

/-!
# The pentagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.PentagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismPentagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 39 30 48 :=
  Polyhedra.prismPentagonalAntiprism_pose_of_reps Polyhedra.prismPentagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.PentagonalAntiprism.Proof
