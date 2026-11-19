import Modules.Pose.Optimum
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Polynomials
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Proof.Representatives
import Polyhedra.Catalan.PentagonalIcositetrahedronLaevo.Proof.Pose

/-!
# The pentagonal icositetrahedron laevo: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Catalan.PentagonalIcositetrahedronLaevo.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.catalanPentagonalIcositetrahedronLaevo_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 62 53 71 :=
  Polyhedra.catalanPentagonalIcositetrahedronLaevo_pose_of_reps Polyhedra.catalanPentagonalIcositetrahedronLaevo_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Catalan.PentagonalIcositetrahedronLaevo.Proof
