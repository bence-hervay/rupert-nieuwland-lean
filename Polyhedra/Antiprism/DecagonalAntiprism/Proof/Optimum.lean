import Modules.Pose.Optimum
import Polyhedra.Antiprism.DecagonalAntiprism.Polynomials
import Polyhedra.Antiprism.DecagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.DecagonalAntiprism.Proof.Pose

/-!
# The decagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.DecagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismDecagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 55 46 64 :=
  Polyhedra.prismDecagonalAntiprism_pose_of_reps Polyhedra.prismDecagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.DecagonalAntiprism.Proof
