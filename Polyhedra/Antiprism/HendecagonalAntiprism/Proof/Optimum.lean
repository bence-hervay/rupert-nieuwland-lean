import Modules.Pose.Optimum
import Polyhedra.Antiprism.HendecagonalAntiprism.Polynomials
import Polyhedra.Antiprism.HendecagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.HendecagonalAntiprism.Proof.Pose

/-!
# The hendecagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.HendecagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismHendecagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 45 36 54 :=
  Polyhedra.prismHendecagonalAntiprism_pose_of_reps Polyhedra.prismHendecagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.HendecagonalAntiprism.Proof
