import Modules.Pose.Optimum
import Polyhedra.Johnson.Hebesphenomegacorona.Polynomials
import Polyhedra.Johnson.Hebesphenomegacorona.Proof.Representatives
import Polyhedra.Johnson.Hebesphenomegacorona.Proof.Pose

/-!
# The hebesphenomegacorona: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.Hebesphenomegacorona.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonHebesphenomegacorona_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 48 39 57 :=
  Polyhedra.johnsonHebesphenomegacorona_pose_of_reps Polyhedra.johnsonHebesphenomegacorona_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.Hebesphenomegacorona.Proof
