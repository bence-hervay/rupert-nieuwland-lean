import Polyhedra.Johnson.GyroelongatedPentagonalRotunda.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalRotunda.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedPentagonalRotunda.Proof.Theta

/-!
# The gyroelongated pentagonal rotunda: the result

The gyroelongated pentagonal rotunda is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedPentagonalRotunda

open Notation

/-- **The gyroelongated pentagonal rotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated pentagonal rotunda.** The system `system` has exactly one
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
  [(1.000199066090592665768113352419, 1.0001990660905926657681133524191),     -- ν
   (-0.0885274538226544224188399398536, -0.0885274538226544224188399398535),  -- R₁ 0 0
   (0.4529152523243057943030483557523, 0.4529152523243057943030483557524),    -- R₁ 0 1
   (0.8871474872487033109415263987415, 0.8871474872487033109415263987416),    -- R₁ 0 2
   (0.8468982696557836047836254609682, 0.8468982696557836047836254609683),    -- R₁ 1 0
   (-0.4346109878492050580267741532213, -0.4346109878492050580267741532212),  -- R₁ 1 1
   (0.3063929015084680001475894292226, 0.3063929015084680001475894292227),    -- R₁ 1 2
   (0.5243340640981829515391075468466, 0.5243340640981829515391075468467),    -- R₁ 2 0
   (0.7784478553202831891023884989951, 0.7784478553202831891023884989952),    -- R₁ 2 1
   (-0.3450981393365284776048434961065, -0.3450981393365284776048434961064),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.5825082326734292358131832038296, 0.5825082326734292358131832038297),    -- R₂ 0 1
   (0.81282480207464020793968405691, 0.8128248020746402079396840569101),      -- R₂ 0 2
   (0.8610612469176987156618221084522, 0.8610612469176987156618221084523),    -- R₂ 1 0
   (-0.413322434123972801588862294973, -0.4133224341239728015888622949729),   -- R₂ 1 1
   (0.296206168920183105319351559987, 0.2962061689201831053193515599871),     -- R₂ 1 2
   (0.5085012576744898121089168143054, 0.5085012576744898121089168143055),    -- R₂ 2 0
   (0.6998919376000213593722155241141, 0.6998919376000213593722155241142),    -- R₂ 2 1
   (-0.5015752651656079458689712038038, -0.5015752651656079458689712038037),  -- R₂ 2 2
   (-0.0393814716059019880256988187793, -0.0393814716059019880256988187792),  -- t 0
   (-0.0064288109054551739478347777089, -0.0064288109054551739478347777088)]  -- t 1

/-- **The enclosure of the optimum of the gyroelongated pentagonal rotunda.** At the root of
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

end Nieuwland.Johnson.GyroelongatedPentagonalRotunda
