import Polyhedra.Johnson.PentagonalCupola.Proof.Optimum
import Polyhedra.Johnson.PentagonalCupola.Proof.Enclosure

/-!
# The pentagonal cupola: the result

The pentagonal cupola is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.PentagonalCupola

open Notation

/-- **The pentagonal cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal cupola.** The system `system` has exactly one root in its box;
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
  [(1.0514622242382672120513381696957, 1.0514622242382672120513381696958),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.9982630332714447355250227027297, 0.9982630332714447355250227027298),    -- R₁ 0 1
   (0.0589144838192988072294820849609, 0.058914483819298807229482084961),     -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.058914483819298807229482084961, -0.0589144838192988072294820849609),   -- R₁ 1 1
   (0.9982630332714447355250227027297, 0.9982630332714447355250227027298),    -- R₁ 1 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.0309731770982446638895632558912, 0.0309731770982446638895632558913),    -- R₂ 0 0
   (0.9995202160539029198882799579563, 0.9995202160539029198882799579564),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.4934043589847513986649552368014, -0.4934043589847513986649552368013),  -- R₂ 1 0
   (0.0152896363139256752567764590857, 0.0152896363139256752567764590858),    -- R₂ 1 1
   (0.8696656630891175164268525299342, 0.8696656630891175164268525299343),    -- R₂ 1 2
   (0.8692484114654954858354317588342, 0.8692484114654954858354317588343),    -- R₂ 2 0
   (-0.0269363085991216143765738191258, -0.0269363085991216143765738191257),  -- R₂ 2 1
   (0.4936412001076951670200092965999, 0.4936412001076951670200092966),       -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the pentagonal cupola.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.PentagonalCupola
