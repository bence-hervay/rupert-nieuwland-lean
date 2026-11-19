import Polyhedra.Johnson.ElongatedPentagonalOrthobicupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedPentagonalOrthobicupola.Proof.Enclosure
import Polyhedra.Johnson.ElongatedPentagonalOrthobicupola.Proof.Theta

/-!
# The elongated pentagonal orthobicupola: the result

The elongated pentagonal orthobicupola is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedPentagonalOrthobicupola

open Notation

/-- **The elongated pentagonal orthobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated pentagonal orthobicupola.** The system `system` has exactly one
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
  [(1.0420303365640580658431134173294, 1.0420303365640580658431134173295),    -- ν
   (-0.5777005549900843227889417607147, -0.5777005549900843227889417607146),  -- R₁ 0 0
   (-0.1877062888409595950558973364479, -0.1877062888409595950558973364478),  -- R₁ 0 1
   (0.7943729715276715070775353271208, 0.7943729715276715070775353271209),    -- R₁ 0 2
   (-0.7554935909401364812527728914943, -0.7554935909401364812527728914942),  -- R₁ 1 0
   (-0.2454747480741767363873345937879, -0.2454747480741767363873345937878),  -- R₁ 1 1
   (-0.6074303104935554606251927546888, -0.6074303104935554606251927546887),  -- R₁ 1 2
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 2 0
   (-0.9510565162951535721164393333794, -0.9510565162951535721164393333793),  -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9818989922967069455493383751513, 0.9818989922967069455493383751514),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.1894053033225612571664129968472, -0.1894053033225612571664129968471),  -- R₂ 0 2
   (-0.0477799240880884767585608451776, -0.0477799240880884767585608451775),  -- R₂ 1 0
   (0.9676587456014170107109116245855, 0.9676587456014170107109116245856),    -- R₂ 1 1
   (-0.2476966509971998340998682913002, -0.2476966509971998340998682913001),  -- R₂ 1 2
   (0.1832796982233655276323217453977, 0.1832796982233655276323217453978),    -- R₂ 2 0
   (0.2522628630240529776778408175517, 0.2522628630240529776778408175518),    -- R₂ 2 1
   (0.9501431471931268673301980395103, 0.9501431471931268673301980395104),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the elongated pentagonal orthobicupola.** At the root of
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
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ElongatedPentagonalOrthobicupola
