import Modules.Pose.Optimum
import Polyhedra.Prism.EnneagonalPrism.Polynomials
import Polyhedra.Prism.EnneagonalPrism.Proof.Representatives
import Polyhedra.Prism.EnneagonalPrism.Proof.Pose

/-!
# The enneagonal prism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Prism.EnneagonalPrism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismEnneagonalPrism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 54 45 63 :=
  Polyhedra.prismEnneagonalPrism_pose_of_reps Polyhedra.prismEnneagonalPrism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Prism.EnneagonalPrism.Proof
