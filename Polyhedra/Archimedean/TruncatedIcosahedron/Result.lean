import Polyhedra.Archimedean.TruncatedIcosahedron.Proof.Optimum
import Polyhedra.Archimedean.TruncatedIcosahedron.Proof.Enclosure

/-!
# The truncated icosahedron: the result

The truncated icosahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Archimedean.TruncatedIcosahedron

open Notation

/-- **The truncated icosahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the truncated icosahedron.** The system `system` has exactly one root in its
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
  [(1.0019651861899474666187666625841, 1.0019651861899474666187666625842),    -- ν
   (0.9951248862871590461528896271141, 0.9951248862871590461528896271142),    -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.0986228203407749731141638537944, 0.0986228203407749731141638537945),    -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0986228203407749731141638537945, -0.0986228203407749731141638537944),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9951248862871590461528896271141, 0.9951248862871590461528896271142),    -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 0
   (0.9708049184193268142819296241344, 0.9708049184193268142819296241345),    -- R₂ 1 1
   (0.2398704032865334737310708482376, 0.2398704032865334737310708482377),    -- R₂ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 0
   (-0.2398704032865334737310708482377, -0.2398704032865334737310708482376),  -- R₂ 2 1
   (0.9708049184193268142819296241344, 0.9708049184193268142819296241345),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the truncated icosahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.TruncatedIcosahedron
