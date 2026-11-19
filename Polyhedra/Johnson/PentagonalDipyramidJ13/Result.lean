import Polyhedra.Johnson.PentagonalDipyramidJ13.Proof.Optimum
import Polyhedra.Johnson.PentagonalDipyramidJ13.Proof.Enclosure
import Polyhedra.Johnson.PentagonalDipyramidJ13.Proof.Theta

/-!
# The pentagonal dipyramid j13: the result

The pentagonal dipyramid j13 is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.PentagonalDipyramidJ13

open Notation

/-- **The pentagonal dipyramid j13 is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal dipyramid j13.** The system `system` has exactly one root in its
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
  [(1.043612947556708626079386535877, 1.0436129475567086260793865358771),     -- ν
   (-0.4670861794813578482255593117741, -0.467086179481357848225559311774),   -- R₁ 0 0
   (0.6428889727400945671816830329725, 0.6428889727400945671816830329726),    -- R₁ 0 1
   (-0.60706199820668622309539158142, -0.6070619982066862230953915814199),    -- R₁ 0 2
   (0.356822089773089931941969843046, 0.3568220897730899319419698430461),     -- R₁ 1 0
   (-0.4911234731884230114078351376177, -0.4911234731884230114078351376176),  -- R₁ 1 1
   (-0.7946544722917661229555309283276, -0.7946544722917661229555309283275),  -- R₁ 1 2
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 2 0
   (-0.5877852522924731291687059546391, -0.587785252292473129168705954639),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0, 0),                                                                    -- R₂ 2 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 2 2
   (-0.0707248124857267169464853078892, -0.0707248124857267169464853078891),  -- t 0
   (-0.2521959999423122803669518125225, -0.2521959999423122803669518125224)]  -- t 1

/-- **The enclosure of the optimum of the pentagonal dipyramid j13.** At the root of `system`, the
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
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.PentagonalDipyramidJ13
