import Modules.Pose.Optimum
import Polyhedra.Other.HendecagonalDipyramid.Polynomials
import Polyhedra.Other.HendecagonalDipyramid.Proof.Representatives
import Polyhedra.Other.HendecagonalDipyramid.Proof.Pose

/-!
# The hendecagonal dipyramid: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Other.HendecagonalDipyramid.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.dipyramidHendecagonalDipyramid_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 45 36 54 :=
  Polyhedra.dipyramidHendecagonalDipyramid_pose_of_reps Polyhedra.dipyramidHendecagonalDipyramid_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Other.HendecagonalDipyramid.Proof
