import Polyhedra.Johnson.Gyrobifastigium.Proof.Optimum
import Polyhedra.Johnson.Gyrobifastigium.Proof.Enclosure

/-!
# The gyrobifastigium: the result

The gyrobifastigium is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.Gyrobifastigium

open Notation

/-- **The gyrobifastigium is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyrobifastigium.** The system `system` has exactly one root in its box; at
the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and
the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.0440171988517470258498627247993, 1.0440171988517470258498627247994),    -- ν
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.866025403784438646763723170753, -0.8660254037844386467637231707529),   -- R₁ 1 1
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 1
   (0.8660254037844386467637231707529, 0.866025403784438646763723170753),     -- R₁ 2 2
   (-0.6451918959504387955440502085793, -0.6451918959504387955440502085792),  -- R₂ 0 0
   (0.7640205608489068397706840855294, 0.7640205608489068397706840855295),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.7640205608489068397706840855294, 0.7640205608489068397706840855295),    -- R₂ 2 0
   (0.6451918959504387955440502085792, 0.6451918959504387955440502085793),    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (-0.038120012409044147217272930106, -0.0381200124090441472172729301059)]   -- t 1

/-- **The enclosure of the optimum of the gyrobifastigium.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.Gyrobifastigium
