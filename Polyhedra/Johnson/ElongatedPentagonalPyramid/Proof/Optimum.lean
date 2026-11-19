import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedPentagonalPyramid.Polynomials
import Polyhedra.Johnson.ElongatedPentagonalPyramid.Proof.Representatives
import Polyhedra.Johnson.ElongatedPentagonalPyramid.Proof.Pose

/-!
# The elongated pentagonal pyramid: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedPentagonalPyramid.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedPentagonalPyramid_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 48 39 57 :=
  Polyhedra.johnsonElongatedPentagonalPyramid_pose_of_reps Polyhedra.johnsonElongatedPentagonalPyramid_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedPentagonalPyramid.Proof
