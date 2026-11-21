import Modules.Pose.Optimum
import Polyhedra.Other.OctagonalTrapezohedron.Polynomials
import Polyhedra.Other.OctagonalTrapezohedron.Proof.Representatives
import Polyhedra.Other.OctagonalTrapezohedron.Proof.Pose

/-!
# The octagonal trapezohedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Other.OctagonalTrapezohedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.trapezohedronOctagonalTrapezohedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 51 42 60 :=
  Polyhedra.trapezohedronOctagonalTrapezohedron_pose_of_reps Polyhedra.trapezohedronOctagonalTrapezohedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Other.OctagonalTrapezohedron.Proof
