import Modules.Pose.Optimum
import Polyhedra.Antiprism.DodecagonalAntiprism.Polynomials
import Polyhedra.Antiprism.DodecagonalAntiprism.Proof.Representatives
import Polyhedra.Antiprism.DodecagonalAntiprism.Proof.Pose

/-!
# The dodecagonal antiprism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Antiprism.DodecagonalAntiprism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismDodecagonalAntiprism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 55 46 64 :=
  Polyhedra.prismDodecagonalAntiprism_pose_of_reps Polyhedra.prismDodecagonalAntiprism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Antiprism.DodecagonalAntiprism.Proof
