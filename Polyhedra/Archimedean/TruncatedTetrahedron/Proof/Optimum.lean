import Modules.Pose.Optimum
import Polyhedra.Archimedean.TruncatedTetrahedron.Polynomials
import Polyhedra.Archimedean.TruncatedTetrahedron.Proof.Representatives
import Polyhedra.Archimedean.TruncatedTetrahedron.Proof.Pose

/-!
# The truncated tetrahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Archimedean.TruncatedTetrahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanTruncatedTetrahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.archimedeanTruncatedTetrahedron_pose_of_reps Polyhedra.archimedeanTruncatedTetrahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Archimedean.TruncatedTetrahedron.Proof
