import Modules.Pose.Optimum
import Polyhedra.Johnson.DiminishedRhombicosidodecahedron.Polynomials
import Polyhedra.Johnson.DiminishedRhombicosidodecahedron.Proof.Representatives
import Polyhedra.Johnson.DiminishedRhombicosidodecahedron.Proof.Pose

/-!
# The diminished rhombicosidodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.DiminishedRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonDiminishedRhombicosidodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 79 70 88 :=
  Polyhedra.johnsonDiminishedRhombicosidodecahedron_pose_of_reps Polyhedra.johnsonDiminishedRhombicosidodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.DiminishedRhombicosidodecahedron.Proof
