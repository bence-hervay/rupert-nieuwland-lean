import Polyhedra.Other.PentagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.PentagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.PentagonalTrapezohedron.Proof.Theta

/-!
# The pentagonal trapezohedron: the result

The pentagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Other.PentagonalTrapezohedron

open Notation

/-- **The pentagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal trapezohedron.** The system `system` has exactly one root in its
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
  [(1.0364766009665618210552955462546, 1.0364766009665618210552955462547),    -- ν
   (0.99394089808538644685795001988, 0.9939408980853864468579500198801),      -- R₁ 0 0
   (-0.1005797394475916627235072830719, -0.1005797394475916627235072830718),  -- R₁ 0 1
   (-0.044330656727258239747380290105, -0.0443306567272582397473802901049),   -- R₁ 0 2
   (0.0655442711217736590208851871314, 0.0655442711217736590208851871315),    -- R₁ 1 0
   (0.866118516584115383175153997383, 0.8661185165841153831751539973831),     -- R₁ 1 1
   (-0.4955226167928633240257833773842, -0.4955226167928633240257833773841),  -- R₁ 1 2
   (0.0882351383312275440600286452194, 0.0882351383312275440600286452195),    -- R₁ 2 0
   (0.4896145741731816744296859413734, 0.4896145741731816744296859413735),    -- R₁ 2 1
   (0.867463041933708620312513388212, 0.8674630419337086203125133882121),     -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.3971598533993761089231166043085, 0.3971598533993761089231166043086),    -- R₂ 0 1
   (0.9177494488409056393734504711754, 0.9177494488409056393734504711755),    -- R₂ 0 2
   (0.8949315835741926912188061960836, 0.8949315835741926912188061960837),    -- R₂ 1 0
   (-0.4095029105888064792281785974115, -0.4095029105888064792281785974114),  -- R₂ 1 1
   (0.1772140709443912322853220616464, 0.1772140709443912322853220616465),    -- R₂ 1 2
   (0.446203384928204867233577077636, 0.4462033849282048672335770776361),     -- R₂ 2 0
   (0.8213229675755342248926448641488, 0.8213229675755342248926448641489),    -- R₂ 2 1
   (-0.3554308965347978774383994704506, -0.3554308965347978774383994704505),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the pentagonal trapezohedron.** At the root of `system`, the
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
    polyEval [-4/25, 8/5, -12/5, 0, 1] θ = 0 ∧
      (0.7721332917328642654377061459613 : ℝ) ≤ θ ∧
      θ ≤ (0.7721332917328642654377061459614 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.PentagonalTrapezohedron
