import Polyhedra.Other.DecagonalDipyramid.Proof.Optimum
import Polyhedra.Other.DecagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.DecagonalDipyramid.Proof.Theta

/-!
# The decagonal dipyramid: the result

The decagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.DecagonalDipyramid

open Notation

/-- **The decagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the decagonal dipyramid.** The system `system` has exactly one root in its box;
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
  [(1.0420303365640580658431134173294, 1.0420303365640580658431134173295),    -- ν
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 0 0
   (0.587785252292473129168705954639, 0.5877852522924731291687059546391),     -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.5584801294868765077994272107365, 0.5584801294868765077994272107366),    -- R₁ 1 0
   (0.7686819531681367612366227620992, 0.7686819531681367612366227620993),    -- R₁ 1 1
   (-0.311814046896447646185175256629, -0.3118140468964476461851752566289),   -- R₁ 1 2
   (-0.1832796982233655276323217453978, -0.1832796982233655276323217453977),  -- R₁ 2 0
   (-0.2522628630240529776778408175518, -0.2522628630240529776778408175517),  -- R₁ 2 1
   (-0.9501431471931268673301980395104, -0.9501431471931268673301980395103),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 2
   (0.9510565162951535721164393333793, 0.9510565162951535721164393333794),    -- R₂ 1 0
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₂ 2 0
   (0.9510565162951535721164393333793, 0.9510565162951535721164393333794),    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the decagonal dipyramid.** At the root of `system`, the
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
    polyEval [-1/20, 1/2, -3/2, 1, 1] θ = 0 ∧
      (0.4094227023180610640371922534991 : ℝ) ≤ θ ∧
      θ ≤ (0.4094227023180610640371922534992 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.DecagonalDipyramid
