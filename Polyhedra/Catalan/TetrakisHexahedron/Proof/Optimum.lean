import Modules.Pose.Optimum
import Polyhedra.Catalan.TetrakisHexahedron.Polynomials
import Polyhedra.Catalan.TetrakisHexahedron.Proof.Representatives
import Polyhedra.Catalan.TetrakisHexahedron.Proof.Pose

/-!
# The tetrakis hexahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Catalan.TetrakisHexahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.catalanTetrakisHexahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.catalanTetrakisHexahedron_pose_of_reps Polyhedra.catalanTetrakisHexahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Catalan.TetrakisHexahedron.Proof
