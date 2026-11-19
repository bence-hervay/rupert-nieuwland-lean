import Modules.Pose.Optimum
import Polyhedra.Johnson.SquarePyramid.Polynomials
import Polyhedra.Johnson.SquarePyramid.Proof.Representatives
import Polyhedra.Johnson.SquarePyramid.Proof.Pose

/-!
# The square pyramid: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.SquarePyramid.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonSquarePyramid_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonSquarePyramid_pose_of_reps Polyhedra.johnsonSquarePyramid_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.SquarePyramid.Proof
