import Polyhedra.Other.EnneagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.EnneagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.EnneagonalTrapezohedron.Proof.Theta

/-!
# The enneagonal trapezohedron: the result

The enneagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Other.EnneagonalTrapezohedron

open Notation

/-- **The enneagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the enneagonal trapezohedron.** The system `system` has exactly one root in its
box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than
`1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
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
  [(1.017114120894887100003754154902, 1.0171141208948871000037541549021),     -- ν
   (0.6896981832286046545266124623773, 0.6896981832286046545266124623774),    -- R₁ 0 0
   (0.7069387639640131196640073171197, 0.7069387639640131196640073171198),    -- R₁ 0 1
   (0.1566971603322645622334048047187, 0.1566971603322645622334048047188),    -- R₁ 0 2
   (0.7204098314009917315424295744545, 0.7204098314009917315424295744546),    -- R₁ 1 0
   (-0.6481155220787777495439018045258, -0.6481155220787777495439018045257),  -- R₁ 1 1
   (-0.2468925775744342201547933660399, -0.2468925775744342201547933660398),  -- R₁ 1 2
   (-0.072980071745352162105617152591, -0.0729800717453521621056171525909),   -- R₁ 2 0
   (0.2831675370616955040706439795408, 0.2831675370616955040706439795409),    -- R₁ 2 1
   (-0.9562897338581318024147370360483, -0.9562897338581318024147370360482),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.5783366566247689439468539568707, 0.5783366566247689439468539568708),    -- R₂ 0 1
   (0.8157982051978810893196050381694, 0.8157982051978810893196050381695),    -- R₂ 0 2
   (0.7895147074977531338916927123134, 0.7895147074977531338916927123135),    -- R₂ 1 0
   (-0.5006811708554698066053007853628, -0.5006811708554698066053007853627),  -- R₂ 1 1
   (0.3549435050758545199289740287922, 0.3549435050758545199289740287923),    -- R₂ 1 2
   (0.6137316405765123263762417986507, 0.6137316405765123263762417986508),    -- R₂ 2 0
   (0.6440846813539970785154723125297, 0.6440846813539970785154723125298),    -- R₂ 2 1
   (-0.4566052962903329450023223545573, -0.4566052962903329450023223545572),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the enneagonal trapezohedron.** At the root of `system`, the
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
    polyEval [64/81, 0, -256/9, 0, 1168/9, 0, 1760/9, 0, -280, 0, 64, 0, 1] θ = 0 ∧
      (0.3894107250291187690117025147923 : ℝ) ≤ θ ∧
      θ ≤ (0.3894107250291187690117025147924 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.EnneagonalTrapezohedron
