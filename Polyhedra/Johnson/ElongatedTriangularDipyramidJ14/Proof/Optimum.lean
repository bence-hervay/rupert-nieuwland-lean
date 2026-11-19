import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Polynomials
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.Representatives
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.Pose

/-!
# The elongated triangular dipyramid j14: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedTriangularDipyramidJ14.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedTriangularDipyramidJ14_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonElongatedTriangularDipyramidJ14_pose_of_reps Polyhedra.johnsonElongatedTriangularDipyramidJ14_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedTriangularDipyramidJ14.Proof
