import Modules.Pose.Optimum
import Polyhedra.Other.EnneagonalTrapezohedron.Polynomials
import Polyhedra.Other.EnneagonalTrapezohedron.Proof.Representatives
import Polyhedra.Other.EnneagonalTrapezohedron.Proof.Pose

/-!
# The enneagonal trapezohedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Other.EnneagonalTrapezohedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.trapezohedronEnneagonalTrapezohedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 41 32 50 :=
  Polyhedra.trapezohedronEnneagonalTrapezohedron_pose_of_reps Polyhedra.trapezohedronEnneagonalTrapezohedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Other.EnneagonalTrapezohedron.Proof
