import Modules.Pose.Optimum
import Polyhedra.Archimedean.Icosidodecahedron.Polynomials
import Polyhedra.Archimedean.Icosidodecahedron.Proof.Representatives
import Polyhedra.Archimedean.Icosidodecahedron.Proof.Pose

/-!
# The icosidodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Archimedean.Icosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.archimedeanIcosidodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.archimedeanIcosidodecahedron_pose_of_reps Polyhedra.archimedeanIcosidodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Archimedean.Icosidodecahedron.Proof
