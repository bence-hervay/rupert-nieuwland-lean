import Modules.Pose.Optimum
import Polyhedra.Johnson.MetabiaugmentedTruncatedDodecahedron.Polynomials
import Polyhedra.Johnson.MetabiaugmentedTruncatedDodecahedron.Proof.Representatives
import Polyhedra.Johnson.MetabiaugmentedTruncatedDodecahedron.Proof.Pose

/-!
# The metabiaugmented truncated dodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.MetabiaugmentedTruncatedDodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonMetabiaugmentedTruncatedDodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 66 57 75 :=
  Polyhedra.johnsonMetabiaugmentedTruncatedDodecahedron_pose_of_reps Polyhedra.johnsonMetabiaugmentedTruncatedDodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.MetabiaugmentedTruncatedDodecahedron.Proof
