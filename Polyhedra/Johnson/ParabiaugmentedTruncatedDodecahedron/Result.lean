import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.ParabiaugmentedTruncatedDodecahedron.Proof.Enclosure

/-!
# The parabiaugmented truncated dodecahedron: the result

The parabiaugmented truncated dodecahedron is Rupert, and its Nieuwland number and an optimal pose
are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ParabiaugmentedTruncatedDodecahedron

open Notation

/-- **The parabiaugmented truncated dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the parabiaugmented truncated dodecahedron.** The system `system` has exactly
one root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
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
  [(1.0144848972508477373686930856485, 1.0144848972508477373686930856486),    -- ν
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 0 0
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 0 1
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 0 2
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 1 0
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 1 1
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 1 2
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 0
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 2 1
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 2 2
   (0.9857219192813019146144665496128, 0.9857219192813019146144665496129),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.1683814058867145601686667738868, 0.1683814058867145601686667738869),    -- R₂ 0 2
   (0.0989571122862496041377482002772, 0.0989571122862496041377482002773),    -- R₂ 1 0
   (0.8090816876136465426958913924638, 0.8090816876136465426958913924639),    -- R₂ 1 1
   (-0.5793050256093246238669984709572, -0.5793050256093246238669984709571),  -- R₂ 1 2
   (-0.1362343120375814148053839225533, -0.1362343120375814148053839225532),  -- R₂ 2 0
   (0.5876961993821754082036875709272, 0.5876961993821754082036875709273),    -- R₂ 2 1
   (0.7975295539698784284591319947177, 0.7975295539698784284591319947178),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the parabiaugmented truncated dodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ParabiaugmentedTruncatedDodecahedron
