import Modules.Pose.Optimum
import Polyhedra.Johnson.AugmentedDodecahedron.Polynomials
import Polyhedra.Johnson.AugmentedDodecahedron.Proof.Representatives
import Polyhedra.Johnson.AugmentedDodecahedron.Proof.Pose

/-!
# The augmented dodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.AugmentedDodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonAugmentedDodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 57 48 66 :=
  Polyhedra.johnsonAugmentedDodecahedron_pose_of_reps Polyhedra.johnsonAugmentedDodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.AugmentedDodecahedron.Proof
