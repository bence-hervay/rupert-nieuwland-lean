import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedSquareCupola.Polynomials
import Polyhedra.Johnson.ElongatedSquareCupola.Proof.Representatives
import Polyhedra.Johnson.ElongatedSquareCupola.Proof.Pose

/-!
# The elongated square cupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedSquareCupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedSquareCupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 63 54 72 :=
  Polyhedra.johnsonElongatedSquareCupola_pose_of_reps Polyhedra.johnsonElongatedSquareCupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedSquareCupola.Proof
