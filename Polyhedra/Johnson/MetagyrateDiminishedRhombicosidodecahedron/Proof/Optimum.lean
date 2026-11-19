import Modules.Pose.Optimum
import Polyhedra.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Polynomials
import Polyhedra.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Proof.Representatives
import Polyhedra.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Proof.Pose

/-!
# The metagyrate diminished rhombicosidodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonMetagyrateDiminishedRhombicosidodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 77 68 86 :=
  Polyhedra.johnsonMetagyrateDiminishedRhombicosidodecahedron_pose_of_reps Polyhedra.johnsonMetagyrateDiminishedRhombicosidodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Proof
