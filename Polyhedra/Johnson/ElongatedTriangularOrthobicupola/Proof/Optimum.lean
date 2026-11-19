import Modules.Pose.Optimum
import Polyhedra.Johnson.ElongatedTriangularOrthobicupola.Polynomials
import Polyhedra.Johnson.ElongatedTriangularOrthobicupola.Proof.Representatives
import Polyhedra.Johnson.ElongatedTriangularOrthobicupola.Proof.Pose

/-!
# The elongated triangular orthobicupola: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.ElongatedTriangularOrthobicupola.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonElongatedTriangularOrthobicupola_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 54 45 63 :=
  Polyhedra.johnsonElongatedTriangularOrthobicupola_pose_of_reps Polyhedra.johnsonElongatedTriangularOrthobicupola_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.ElongatedTriangularOrthobicupola.Proof
