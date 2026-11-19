import Modules.Pose.Optimum
import Polyhedra.Platonic.Tetrahedron.Polynomials
import Polyhedra.Platonic.Tetrahedron.Proof.Representatives
import Polyhedra.Platonic.Tetrahedron.Proof.Pose

/-!
# The tetrahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Platonic.Tetrahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.platonicTetrahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.platonicTetrahedron_pose_of_reps Polyhedra.platonicTetrahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Platonic.Tetrahedron.Proof
