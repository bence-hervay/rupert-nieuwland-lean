import Polyhedra.Other.HeptagonalDipyramid.Proof.Optimum
import Polyhedra.Other.HeptagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.HeptagonalDipyramid.Proof.Theta

/-!
# The heptagonal dipyramid: the result

The heptagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.HeptagonalDipyramid

open Notation

/-- **The heptagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the heptagonal dipyramid.** The system `system` has exactly one root in its
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
  [(1.0074150608450983138835915337104, 1.0074150608450983138835915337105),    -- ν
   (0.9749279121818236070181316829939, 0.974927912181823607018131682994),     -- R₁ 0 0
   (0.2225209339563144042889025644967, 0.2225209339563144042889025644968),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.1992390937049782414335395292741, 0.1992390937049782414335395292742),    -- R₁ 1 0
   (-0.8729235052057049829649993441215, -0.8729235052057049829649993441214),  -- R₁ 1 1
   (-0.4453182430565858203456053710937, -0.4453182430565858203456053710936),  -- R₁ 1 2
   (-0.0990926313527364988655140791205, -0.0990926313527364988655140791204),  -- R₁ 2 0
   (0.434153184959635080901873670991, 0.4341531849596350809018736709911),     -- R₁ 2 1
   (-0.895372359636478590133502086356, -0.8953723596364785901335020863559),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 0 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 2
   (0.777320373896047663048027753, 0.7773203738960476630480277530001),        -- R₂ 1 0
   (-0.6291049485786204359417583828192, -0.6291049485786204359417583828191),  -- R₂ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 2
   (0.6291049485786204359417583828191, 0.6291049485786204359417583828192),    -- R₂ 2 0
   (0.777320373896047663048027753, 0.7773203738960476630480277530001),        -- R₂ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (0.0200962063815293452886242882926, 0.0200962063815293452886242882927)]    -- t 1

/-- **The enclosure of the optimum of the heptagonal dipyramid.** At the root of `system`, the
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
    polyEval [-7/64, 0, 7/8, 0, -7/4, 0, 1] θ = 0 ∧
      (0.4338837391175581204757683328483 : ℝ) ≤ θ ∧
      θ ≤ (0.4338837391175581204757683328484 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.HeptagonalDipyramid
