import Modules.Pose.Optimum
import Polyhedra.Johnson.TridiminishedIcosahedron.Polynomials
import Polyhedra.Johnson.TridiminishedIcosahedron.Proof.Representatives
import Polyhedra.Johnson.TridiminishedIcosahedron.Proof.Pose

/-!
# The tridiminished icosahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.TridiminishedIcosahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonTridiminishedIcosahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonTridiminishedIcosahedron_pose_of_reps Polyhedra.johnsonTridiminishedIcosahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.TridiminishedIcosahedron.Proof
