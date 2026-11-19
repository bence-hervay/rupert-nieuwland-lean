import Modules.Pose.Optimum
import Polyhedra.Johnson.GyrateBidiminishedRhombicosidodecahedron.Polynomials
import Polyhedra.Johnson.GyrateBidiminishedRhombicosidodecahedron.Proof.Representatives
import Polyhedra.Johnson.GyrateBidiminishedRhombicosidodecahedron.Proof.Pose

/-!
# The gyrate bidiminished rhombicosidodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.GyrateBidiminishedRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonGyrateBidiminishedRhombicosidodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 71 62 80 :=
  Polyhedra.johnsonGyrateBidiminishedRhombicosidodecahedron_pose_of_reps Polyhedra.johnsonGyrateBidiminishedRhombicosidodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.GyrateBidiminishedRhombicosidodecahedron.Proof
