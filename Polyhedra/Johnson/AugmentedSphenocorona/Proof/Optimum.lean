import Modules.Pose.Optimum
import Polyhedra.Johnson.AugmentedSphenocorona.Polynomials
import Polyhedra.Johnson.AugmentedSphenocorona.Proof.Representatives
import Polyhedra.Johnson.AugmentedSphenocorona.Proof.Pose

/-!
# The augmented sphenocorona: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.AugmentedSphenocorona.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonAugmentedSphenocorona_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 58 49 67 :=
  Polyhedra.johnsonAugmentedSphenocorona_pose_of_reps Polyhedra.johnsonAugmentedSphenocorona_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.AugmentedSphenocorona.Proof
