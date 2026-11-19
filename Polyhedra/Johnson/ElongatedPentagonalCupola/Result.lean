import Polyhedra.Johnson.ElongatedPentagonalCupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedPentagonalCupola.Proof.Enclosure
import Polyhedra.Johnson.ElongatedPentagonalCupola.Proof.Theta

/-!
# The elongated pentagonal cupola: the result

The elongated pentagonal cupola is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedPentagonalCupola

open Notation

/-- **The elongated pentagonal cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated pentagonal cupola.** The system `system` has exactly one root in
its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which
the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
   (-0.9087368947999471231362551453171, -0.908736894799947123136255145317),   -- R₁ 0 0
   (0.2952665158140333716756568809632, 0.2952665158140333716756568809633),    -- R₁ 0 1
   (-0.294982949792680417752210672772, -0.2949829497926804177522106727719),   -- R₁ 0 2
   (0.2805454565962948317535959365306, 0.2805454565962948317535959365307),    -- R₁ 1 0
   (-0.0911547445367901230753140495911, -0.091154744536790123075314049591),   -- R₁ 1 1
   (-0.9555025166537286435874222778177, -0.9555025166537286435874222778176),  -- R₁ 1 2
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₁ 2 0
   (-0.9510565162951535721164393333794, -0.9510565162951535721164393333793),  -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9545848777325213278056775439082, 0.9545848777325213278056775439083),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.2979391065375394913213323585545, 0.2979391065375394913213323585546),    -- R₂ 0 2
   (0.0287081727528970265172972448351, 0.0287081727528970265172972448352),    -- R₂ 1 0
   (0.995346950655718378208226115053, 0.9953469506557183782082261150531),     -- R₂ 1 1
   (-0.0919798273403073132506951272747, -0.0919798273403073132506951272746),  -- R₂ 1 2
   (-0.2965527811732291409348429270605, -0.2965527811732291409348429270604),  -- R₂ 2 0
   (0.0963558395758291545852531892372, 0.0963558395758291545852531892373),    -- R₂ 2 1
   (0.9501431471931268673301980395103, 0.9501431471931268673301980395104),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the elongated pentagonal cupola.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
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

end Nieuwland.Johnson.ElongatedPentagonalCupola
