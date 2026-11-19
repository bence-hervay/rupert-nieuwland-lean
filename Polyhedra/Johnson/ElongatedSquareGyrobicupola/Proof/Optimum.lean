import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Polynomials
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Proof.Representatives
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Proof.Pose

/-!
# The elongated square gyrobicupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedSquareGyrobicupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedSquareGyrobicupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 22 13 31 :=
  Polyhedra.johnsonElongatedSquareGyrobicupola_pose_of_reps Polyhedra.johnsonElongatedSquareGyrobicupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedSquareGyrobicupola.Proof
