import Modules.Pose.Optimum
import Polyhedra.Other.HendecagonalTrapezohedron.Polynomials
import Polyhedra.Other.HendecagonalTrapezohedron.Proof.Representatives
import Polyhedra.Other.HendecagonalTrapezohedron.Proof.Pose

/-!
# The hendecagonal trapezohedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Other.HendecagonalTrapezohedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.trapezohedronHendecagonalTrapezohedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 41 32 50 :=
  Polyhedra.trapezohedronHendecagonalTrapezohedron_pose_of_reps Polyhedra.trapezohedronHendecagonalTrapezohedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Other.HendecagonalTrapezohedron.Proof
