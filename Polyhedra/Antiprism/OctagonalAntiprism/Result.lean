import Polyhedra.Antiprism.OctagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.OctagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.OctagonalAntiprism.Proof.Theta

/-!
# The octagonal antiprism: the result

The octagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Antiprism.OctagonalAntiprism

open Notation

/-- **The octagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the octagonal antiprism.** The system `system` has exactly one root in its box;
at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`,
and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
(`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
theorem isOptimum : polyhedron.IsOptimum system layout :=
  Proof.isOptimum

/-- The system has exactly one root in its box (a part of `isOptimum`). -/
theorem hasUniqueRoot : system.HasUniqueRoot :=
  isOptimum.uniqueRoot

/-- The Nieuwland number is greater than `1` (a part of `isOptimum`). -/
theorem one_lt_nieuwland : 1 < ν polyhedron :=
  isOptimum.one_lt

/-- Rational intervals for the optimum: for the Nieuwland number `ν` and for the entries of an
optimal pose, the plug's rotation `R₁`, the hole's rotation `R₂` and the translation `t` (the
variables of `layout`, in the order of `PoseLayout.variables`). -/
def enclosure : List (ℚ × ℚ) :=
  [(1.0007046085639461061549486276844, 1.0007046085639461061549486276845),    -- ν
   (-0.6700111877763454609534932367793, -0.6700111877763454609534932367792),  -- R₁ 0 0
   (0.7418410168811013121070854305874, 0.7418410168811013121070854305875),    -- R₁ 0 1
   (-0.0275120687579887537074680885427, -0.0275120687579887537074680885426),  -- R₁ 0 2
   (0.3433853025924353690982478462639, 0.343385302592435369098247846264),     -- R₁ 1 0
   (0.342568059481279846836155969552, 0.3425680594812798468361559695521),     -- R₁ 1 1
   (0.8744905137202643847887485125489, 0.874490513720264384788748512549),     -- R₁ 1 2
   (0.6581576879578573624038113016257, 0.6581576879578573624038113016258),    -- R₁ 2 0
   (0.5764711877414550116660119009858, 0.5764711877414550116660119009859),    -- R₁ 2 1
   (-0.4842617344844870013024715016749, -0.4842617344844870013024715016748),  -- R₁ 2 2
   (-0.7070518934967375557292662087811, -0.707051893496737555729266208781),   -- R₂ 0 0
   (0.7071616646161456711604738345934, 0.7071616646161456711604738345935),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3917936231237776441574563006234, 0.3917936231237776441574563006235),    -- R₂ 1 0
   (0.3917328058782463789213561808179, 0.391732805878246378921356180818),     -- R₂ 1 1
   (0.8324921415114375882487600269381, 0.8324921415114375882487600269382),    -- R₂ 1 2
   (0.5887065285710881092055248597897, 0.5887065285710881092055248597898),    -- R₂ 2 0
   (0.5886151449768159394608542319512, 0.5886151449768159394608542319513),    -- R₂ 2 1
   (-0.5540368528552054479120478111679, -0.5540368528552054479120478111678),  -- R₂ 2 2
   (-0.0123657460919161192562773469608, -0.0123657460919161192562773469607),  -- t 0
   (0.0166419950978951770146165505524, 0.0166419950978951770146165505525)]    -- t 1

/-- **The enclosure of the optimum of the octagonal antiprism.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

@[inherit_doc] local notation "θ" => theta

/-- **`θ` is a root of its polynomial**, and it lies between these two rationals, which are at most
`2 ^ -100` apart. -/
theorem theta_isRoot :
    polyEval [79/512, 7/16, -69/16, 3, 13/2, -4, -3, 0, 1] θ = 0 ∧
      (1.7367107498078623110777935614292 : ℝ) ≤ θ ∧
      θ ≤ (1.7367107498078623110777935614293 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.OctagonalAntiprism
