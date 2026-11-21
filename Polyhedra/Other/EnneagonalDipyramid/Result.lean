import Polyhedra.Other.EnneagonalDipyramid.Proof.Optimum
import Polyhedra.Other.EnneagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.EnneagonalDipyramid.Proof.Theta

/-!
# The enneagonal dipyramid: the result

The enneagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.EnneagonalDipyramid

open Notation

/-- **The enneagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the enneagonal dipyramid.** The system `system` has exactly one root in its
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
  [(1.0081705752001364715134454074807, 1.0081705752001364715134454074808),    -- ν
   (-0.8818534323899734549408138399506, -0.8818534323899734549408138399505),  -- R₁ 0 0
   (0.3209684003754332837163340562698, 0.3209684003754332837163340562699),    -- R₁ 0 1
   (0.3454183112437122602749209972127, 0.3454183112437122602749209972128),    -- R₁ 0 2
   (-0.3420201433256687330440996146823, -0.3420201433256687330440996146822),  -- R₁ 1 0
   (-0.9396926207859083840541092773248, -0.9396926207859083840541092773247),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (0.3245870381600465791961076999936, 0.3245870381600465791961076999937),    -- R₁ 2 0
   (-0.1181400203188849189030539392308, -0.1181400203188849189030539392307),  -- R₁ 2 1
   (0.9384488213309993413070378598806, 0.9384488213309993413070378598807),    -- R₁ 2 2
   (-0.6476955124011289454869809157224, -0.6476955124011289454869809157223),  -- R₂ 0 0
   (0.761899286792840501336340090393, 0.7618992867928405013363400903931),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.761899286792840501336340090393, 0.7618992867928405013363400903931),     -- R₂ 2 0
   (0.6476955124011289454869809157223, 0.6476955124011289454869809157224),    -- R₂ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 2
   (-0.0097867120556163317968891012636, -0.0097867120556163317968891012635),  -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the enneagonal dipyramid.** At the root of `system`, the
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
    polyEval [-3/64, 0, 9/16, 0, -3/2, 0, 1] θ = 0 ∧
      (0.3420201433256687330440996146822 : ℝ) ≤ θ ∧
      θ ≤ (0.3420201433256687330440996146823 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.EnneagonalDipyramid
