import Modules.Pose.Optimum
import Polyhedra.Prism.TriangularPrism.Polynomials
import Polyhedra.Prism.TriangularPrism.Proof.Representatives
import Polyhedra.Prism.TriangularPrism.Proof.Pose

/-!
# The triangular prism: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Prism.TriangularPrism.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.prismTriangularPrism_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.prismTriangularPrism_pose_of_reps Polyhedra.prismTriangularPrism_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Prism.TriangularPrism.Proof
