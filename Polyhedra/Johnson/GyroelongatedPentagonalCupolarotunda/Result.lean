import Polyhedra.Johnson.GyroelongatedPentagonalCupolarotunda.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalCupolarotunda.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedPentagonalCupolarotunda.Proof.Theta

/-!
# The gyroelongated pentagonal cupolarotunda: the result

The gyroelongated pentagonal cupolarotunda is Rupert, and its Nieuwland number and an optimal pose
are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedPentagonalCupolarotunda

open Notation

/-- **The gyroelongated pentagonal cupolarotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated pentagonal cupolarotunda.** The system `system` has exactly
one root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
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
  [(1.0001865007649608623481707459953, 1.0001865007649608623481707459954),    -- ν
   (-0.1124429085932114537674303546295, -0.1124429085932114537674303546294),  -- R₁ 0 0
   (0.4630963286979222021479777871109, 0.463096328697922202147977787111),     -- R₁ 0 1
   (0.8791463943244064122987951135986, 0.8791463943244064122987951135987),    -- R₁ 0 2
   (0.8436608062715310543937620982639, 0.843660806271531054393762098264),     -- R₁ 1 0
   (-0.4229414957555828093334171008668, -0.4229414957555828093334171008667),  -- R₁ 1 1
   (0.3306916012379214870647194939599, 0.33069160123792148706471949396),      -- R₁ 1 2
   (0.524969557468210571024000085865, 0.5249695574682105710240000858651),     -- R₁ 2 0
   (0.7788852813569764240892182392914, 0.7788852813569764240892182392915),    -- R₁ 2 1
   (-0.3431394501031538821346852027298, -0.3431394501031538821346852027297),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.6251723039941467856205223622739, 0.625172303994146785620522362274),     -- R₂ 0 1
   (0.7804867649862168668796220364545, 0.7804867649862168668796220364546),    -- R₂ 0 2
   (0.8663197514497604133312986736352, 0.8663197514497604133312986736353),    -- R₂ 1 0
   (-0.3898451999778001382077341366944, -0.3898451999778001382077341366943),  -- R₂ 1 1
   (0.3122672065752251855313934496746, 0.3122672065752251855313934496747),    -- R₂ 1 2
   (0.499489827972527725052396211969, 0.4994898279725277250523962119691),     -- R₂ 2 0
   (0.6761511002526869645669633769805, 0.6761511002526869645669633769806),    -- R₂ 2 1
   (-0.5415991150094833026239090763652, -0.5415991150094833026239090763651),  -- R₂ 2 2
   (-0.0494567268437203759843529593438, -0.0494567268437203759843529593437),  -- t 0
   (-0.0100676521373308179637920791944, -0.0100676521373308179637920791943)]  -- t 1

/-- **The enclosure of the optimum of the gyroelongated pentagonal cupolarotunda.** At the root of
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

end Nieuwland.Johnson.GyroelongatedPentagonalCupolarotunda
