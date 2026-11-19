import Modules.Pose.Optimum
import Polyhedra.Johnson.TriangularDipyramidJ12.Polynomials
import Polyhedra.Johnson.TriangularDipyramidJ12.Proof.Representatives
import Polyhedra.Johnson.TriangularDipyramidJ12.Proof.Pose

/-!
# The triangular dipyramid j12: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.TriangularDipyramidJ12.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonTriangularDipyramidJ12_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonTriangularDipyramidJ12_pose_of_reps Polyhedra.johnsonTriangularDipyramidJ12_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.TriangularDipyramidJ12.Proof
