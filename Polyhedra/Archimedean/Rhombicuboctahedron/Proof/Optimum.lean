import Modules.Pose.Optimum
import Polyhedra.Archimedean.Rhombicuboctahedron.Polynomials
import Polyhedra.Archimedean.Rhombicuboctahedron.Proof.Representatives
import Polyhedra.Archimedean.Rhombicuboctahedron.Proof.Pose

/-!
# The rhombicuboctahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Archimedean.Rhombicuboctahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanRhombicuboctahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 42 33 51 :=
  Polyhedra.archimedeanRhombicuboctahedron_pose_of_reps Polyhedra.archimedeanRhombicuboctahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Archimedean.Rhombicuboctahedron.Proof
