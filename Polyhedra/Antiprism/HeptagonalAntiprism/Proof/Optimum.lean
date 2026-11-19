import Modules.Pose.Optimum
import Polyhedra.Antiprism.HeptagonalAntiprism.Polynomials
import Polyhedra.Antiprism.HeptagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.HeptagonalAntiprism.Proof.Pose

/-!
# The heptagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.HeptagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismHeptagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 42 33 51 :=
  Polyhedra.prismHeptagonalAntiprism_pose_of_reps Polyhedra.prismHeptagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.HeptagonalAntiprism.Proof
