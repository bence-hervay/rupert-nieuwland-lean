import Polyhedra.Other.TriangularDipyramid.Proof.Optimum
import Polyhedra.Other.TriangularDipyramid.Proof.Enclosure

/-!
# The triangular dipyramid: the result

The triangular dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.TriangularDipyramid

open Notation

/-- **The triangular dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triangular dipyramid.** The system `system` has exactly one root in its
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
  [(1.0201604446568165160322893083513, 1.0201604446568165160322893083514),    -- ν
   (0.9802379667214028088854943472696, 0.9802379667214028088854943472697),    -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.197821961869480000823505899216, 0.1978219618694800008235058992161),     -- R₁ 0 2
   (-0.1295048734845085710756403289075, -0.1295048734845085710756403289074),  -- R₁ 1 0
   (0.7559289460184544544290330724683, 0.7559289460184544544290330724684),    -- R₁ 1 1
   (0.6417163830814902923072618959516, 0.6417163830814902923072618959517),    -- R₁ 1 2
   (-0.1495393471352989029709741832009, -0.1495393471352989029709741832008),  -- R₁ 2 0
   (-0.6546536707079771437982924562469, -0.6546536707079771437982924562468),  -- R₁ 2 1
   (0.7409902530309828578487193421851, 0.7409902530309828578487193421852),    -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0, 0),                                                                    -- R₂ 2 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (-0.2288311903008548548840981050076, -0.2288311903008548548840981050075)]  -- t 1

/-- **The enclosure of the optimum of the triangular dipyramid.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Other.TriangularDipyramid
