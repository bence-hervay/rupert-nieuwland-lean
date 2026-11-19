import Modules.Pose.Optimum
import Polyhedra.Antiprism.OctagonalAntiprism.Polynomials
import Polyhedra.Antiprism.OctagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.OctagonalAntiprism.Proof.Pose

/-!
# The octagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.OctagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismOctagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 55 46 64 :=
  Polyhedra.prismOctagonalAntiprism_pose_of_reps Polyhedra.prismOctagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.OctagonalAntiprism.Proof
