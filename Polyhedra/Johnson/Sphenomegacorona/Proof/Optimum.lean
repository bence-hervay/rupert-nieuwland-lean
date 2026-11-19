import Modules.Pose.Optimum
import Polyhedra.Johnson.Sphenomegacorona.Polynomials
import Polyhedra.Johnson.Sphenomegacorona.Proof.Representatives
import Polyhedra.Johnson.Sphenomegacorona.Proof.Pose

/-!
# The sphenomegacorona: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.Sphenomegacorona.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonSphenomegacorona_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 51 42 60 :=
  Polyhedra.johnsonSphenomegacorona_pose_of_reps Polyhedra.johnsonSphenomegacorona_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.Sphenomegacorona.Proof
