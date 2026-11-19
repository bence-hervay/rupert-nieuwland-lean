import Modules.Pose.Optimum
import Polyhedra.Johnson.MetabidiminishedIcosahedron.Polynomials
import Polyhedra.Johnson.MetabidiminishedIcosahedron.Proof.Representatives
import Polyhedra.Johnson.MetabidiminishedIcosahedron.Proof.Pose

/-!
# The metabidiminished icosahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.MetabidiminishedIcosahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonMetabidiminishedIcosahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 51 42 60 :=
  Polyhedra.johnsonMetabidiminishedIcosahedron_pose_of_reps Polyhedra.johnsonMetabidiminishedIcosahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.MetabidiminishedIcosahedron.Proof
