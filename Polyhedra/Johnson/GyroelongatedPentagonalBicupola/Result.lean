import Polyhedra.Johnson.GyroelongatedPentagonalBicupola.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalBicupola.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedPentagonalBicupola.Proof.Theta

/-!
# The gyroelongated pentagonal bicupola: the result

The gyroelongated pentagonal bicupola is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedPentagonalBicupola

open Notation

/-- **The gyroelongated pentagonal bicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated pentagonal bicupola.** The system `system` has exactly one
root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
greater than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with
which the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits
through it (`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
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
  [(1.0003885592479352861215326872908, 1.0003885592479352861215326872909),    -- ν
   (-0.6181550631740133690040523045472, -0.6181550631740133690040523045471),  -- R₁ 0 0
   (0.7857681821468944811916907934998, 0.7857681821468944811916907934999),    -- R₁ 0 1
   (-0.0212763201211205206241173876113, -0.0212763201211205206241173876112),  -- R₁ 0 2
   (-0.3769764796748961925491983679295, -0.3769764796748961925491983679294),  -- R₁ 1 0
   (-0.272594516794576104567232134929, -0.2725945167945761045672321349289),   -- R₁ 1 1
   (0.8852010862992962594540015938366, 0.8852010862992962594540015938367),    -- R₁ 1 2
   (0.6897630402132707187342627172706, 0.6897630402132707187342627172707),    -- R₁ 2 0
   (0.5552122056827429142321688833567, 0.5552122056827429142321688833568),    -- R₁ 2 1
   (0.4647218038963197368779272655635, 0.4647218038963197368779272655636),    -- R₁ 2 2
   (-0.5894381376265154896986329357438, -0.5894381376265154896986329357437),  -- R₂ 0 0
   (0.807813519267525619013995856484, 0.8078135192675256190139958564841),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4290382117489504050667571294025, 0.4290382117489504050667571294026),    -- R₂ 1 0
   (0.3130567618294108046566795835501, 0.3130567618294108046566795835502),    -- R₂ 1 1
   (0.8473025886495015027652184641692, 0.8473025886495015027652184641693),    -- R₂ 1 2
   (0.6844624860214384160651783473423, 0.6844624860214384160651783473424),    -- R₂ 2 0
   (0.4994324598596877080192924985005, 0.4994324598596877080192924985006),    -- R₂ 2 1
   (-0.5311104623972810113977740413411, -0.531110462397281011397774041341),   -- R₂ 2 2
   (-0.0100960839705367822219544344571, -0.010096083970536782221954434457),   -- t 0
   (0.016428794111805171272746867964, 0.0164287941118051712727468679641)]     -- t 1

/-- **The enclosure of the optimum of the gyroelongated pentagonal bicupola.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
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
    polyEval [-1/1600, 1/20, 31/80, 1/4, -49/40, -3/2, 3/2, 0, 1] θ = 0 ∧
      (0.6940640579892960447363608848778 : ℝ) ≤ θ ∧
      θ ≤ (0.6940640579892960447363608848779 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedPentagonalBicupola
