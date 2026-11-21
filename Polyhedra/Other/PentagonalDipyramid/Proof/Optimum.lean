import Modules.Pose.Optimum
import Polyhedra.Other.PentagonalDipyramid.Polynomials
import Polyhedra.Other.PentagonalDipyramid.Proof.Representatives
import Polyhedra.Other.PentagonalDipyramid.Proof.Pose

/-!
# The pentagonal dipyramid: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Other.PentagonalDipyramid.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.dipyramidPentagonalDipyramid_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.dipyramidPentagonalDipyramid_pose_of_reps Polyhedra.dipyramidPentagonalDipyramid_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Other.PentagonalDipyramid.Proof
