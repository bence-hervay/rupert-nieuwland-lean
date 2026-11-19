import Modules.Pose.Optimum
import Polyhedra.Archimedean.TruncatedCuboctahedron.Polynomials
import Polyhedra.Archimedean.TruncatedCuboctahedron.Proof.Representatives
import Polyhedra.Archimedean.TruncatedCuboctahedron.Proof.Pose

/-!
# The truncated cuboctahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Archimedean.TruncatedCuboctahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanTruncatedCuboctahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 42 33 51 :=
  Polyhedra.archimedeanTruncatedCuboctahedron_pose_of_reps Polyhedra.archimedeanTruncatedCuboctahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Archimedean.TruncatedCuboctahedron.Proof
