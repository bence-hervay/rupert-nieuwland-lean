import Modules.Pose.Optimum
import Polyhedra.Archimedean.TruncatedIcosahedron.Polynomials
import Polyhedra.Archimedean.TruncatedIcosahedron.Proof.Representatives
import Polyhedra.Archimedean.TruncatedIcosahedron.Proof.Pose

/-!
# The truncated icosahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Archimedean.TruncatedIcosahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanTruncatedIcosahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 44 35 53 :=
  Polyhedra.archimedeanTruncatedIcosahedron_pose_of_reps Polyhedra.archimedeanTruncatedIcosahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Archimedean.TruncatedIcosahedron.Proof
