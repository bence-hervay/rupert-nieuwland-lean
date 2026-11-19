import Polyhedra.Johnson.GyroelongatedPentagonalBirotunda.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalBirotunda.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedPentagonalBirotunda.Proof.Theta

/-!
# The gyroelongated pentagonal birotunda: the result

The gyroelongated pentagonal birotunda is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedPentagonalBirotunda

open Notation

/-- **The gyroelongated pentagonal birotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated pentagonal birotunda.** The system `system` has exactly one
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
  [(1.0023900430668194842580397936435, 1.0023900430668194842580397936436),    -- ν
   (0.1563600771893262936430472167406, 0.1563600771893262936430472167407),    -- R₁ 0 0
   (0.9873666159393232330435231402029, 0.987366615939323233043523140203),     -- R₁ 0 1
   (-0.0256649954193819285677649364379, -0.0256649954193819285677649364378),  -- R₁ 0 2
   (0.9872128996302727936374911220908, 0.9872128996302727936374911220909),    -- R₁ 1 0
   (-0.1570462469166209452381662552352, -0.1570462469166209452381662552351),  -- R₁ 1 1
   (-0.0273343581046393207217260570161, -0.027334358104639320721726057016),   -- R₁ 1 2
   (-0.0310196238683975394075839604201, -0.03101962386839753940758396042),    -- R₁ 2 0
   (-0.0210628122038036118969214685891, -0.021062812203803611896921468589),   -- R₁ 2 1
   (-0.9992968232097660597999492315784, -0.9992968232097660597999492315783),  -- R₁ 2 2
   (0.5189105022525924630933919295797, 0.5189105022525924630933919295798),    -- R₂ 0 0
   (0.8548285738392009508680296847825, 0.8548285738392009508680296847826),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.0685741115492697515617000972894, 0.0685741115492697515617000972895),    -- R₂ 1 0
   (-0.0416268568395450328677473979123, -0.0416268568395450328677473979122),  -- R₂ 1 1
   (0.996777204803003273310302225403, 0.9967772048030032733103022254031),     -- R₂ 1 2
   (0.8520736364171764123124317502386, 0.8520736364171764123124317502387),    -- R₂ 2 0
   (-0.5172381599782616489776291026758, -0.5172381599782616489776291026757),  -- R₂ 2 1
   (-0.0802197231677576172935761173631, -0.080219723167757617293576117363),   -- R₂ 2 2
   (-0.0000058719185146145784922023736, -0.0000058719185146145784922023735),  -- t 0
   (-0.1761824594511346597062894925486, -0.1761824594511346597062894925485)]  -- t 1

/-- **The enclosure of the optimum of the gyroelongated pentagonal birotunda.** At the root of
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

end Nieuwland.Johnson.GyroelongatedPentagonalBirotunda
