import Modules.Pose.Optimum
import Polyhedra.Platonic.Dodecahedron.Polynomials
import Polyhedra.Platonic.Dodecahedron.Proof.Representatives
import Polyhedra.Platonic.Dodecahedron.Proof.Pose

/-!
# The dodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Platonic.Dodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.platonicDodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.platonicDodecahedron_pose_of_reps Polyhedra.platonicDodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Platonic.Dodecahedron.Proof
