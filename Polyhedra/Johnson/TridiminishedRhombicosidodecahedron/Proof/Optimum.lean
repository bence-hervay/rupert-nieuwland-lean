import Modules.Pose.Optimum
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Polynomials
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Proof.Representatives
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Proof.Pose

/-!
# The tridiminished rhombicosidodecahedron: the optimum

The join of the certificate's exact number (`Proof/Representatives.lean`: each of the
representatives' systems, one or several, has its one root at `ν`) and the pose root
(`Proof/Pose.lean`, from the same systems).
-/

namespace Nieuwland.Johnson.TridiminishedRhombicosidodecahedron.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.johnsonTridiminishedRhombicosidodecahedron_fullDim

theorem poseRoot : PolynomialSystem.IsPoseRoot polyhedron system (ν polyhedron) 70 61 79 :=
  Polyhedra.johnsonTridiminishedRhombicosidodecahedron_pose_of_reps Polyhedra.johnsonTridiminishedRhombicosidodecahedron_nu_reps_list

theorem isOptimum : polyhedron.IsOptimum system layout :=
  PolynomialSystem.IsPoseRoot.isOptimum fullDim poseRoot (by decide +kernel)

theorem isRupert : polyhedron.IsRupert :=
  Polyhedron.isRupert_of_one_lt_nieuwland fullDim isOptimum.one_lt

end Nieuwland.Johnson.TridiminishedRhombicosidodecahedron.Proof
