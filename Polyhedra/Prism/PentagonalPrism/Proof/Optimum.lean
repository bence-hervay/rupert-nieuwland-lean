import Modules.Pose.Optimum
import Polyhedra.Prism.PentagonalPrism.Polynomials
import Polyhedra.Prism.PentagonalPrism.Proof.Representatives
import Polyhedra.Prism.PentagonalPrism.Proof.Pose

/-!
# The pentagonal prism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Prism.PentagonalPrism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismPentagonalPrism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 48 39 57 :=
  Polyhedra.prismPentagonalPrism_pose_of_reps Polyhedra.prismPentagonalPrism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Prism.PentagonalPrism.Proof
