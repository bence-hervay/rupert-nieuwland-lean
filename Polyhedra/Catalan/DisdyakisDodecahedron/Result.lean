import Polyhedra.Catalan.DisdyakisDodecahedron.Proof.Optimum
import Polyhedra.Catalan.DisdyakisDodecahedron.Proof.Enclosure

/-!
# The disdyakis dodecahedron: the result

The disdyakis dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Catalan.DisdyakisDodecahedron

open Notation

/-- **The disdyakis dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the disdyakis dodecahedron.** The system `system` has exactly one root in its
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
  [(1.0045002810282670678449269706332, 1.0045002810282670678449269706333),    -- ν
   (0.2293529379742081831920329851377, 0.2293529379742081831920329851378),    -- R₁ 0 0
   (-0.7936668390414659469839791513957, -0.7936668390414659469839791513956),  -- R₁ 0 1
   (0.5634626681941997111551312477413, 0.5634626681941997111551312477414),    -- R₁ 0 2
   (-0.7838364158387249515227838988503, -0.7838364158387249515227838988502),  -- R₁ 1 0
   (0.1926012605312522740119902022349, 0.192601260531252274011990202235),     -- R₁ 1 1
   (0.5903433133752546713635857075972, 0.5903433133752546713635857075973),    -- R₁ 1 2
   (-0.5770595316323095532350322240056, -0.5770595316323095532350322240055),  -- R₁ 2 0
   (-0.5770595316323095532350322240056, -0.5770595316323095532350322240055),  -- R₁ 2 1
   (-0.5779313055239342718935715246406, -0.5779313055239342718935715246405),  -- R₁ 2 2
   (-0.2157995925973902743941155174836, -0.2157995925973902743941155174835),  -- R₂ 0 0
   (0.9764376763699772255347741010852, 0.9764376763699772255347741010853),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.2059733912203293055089465550383, 0.2059733912203293055089465550384),    -- R₂ 1 0
   (0.0455215678244762890199868391607, 0.0455215678244762890199868391608),    -- R₂ 1 1
   (0.9774982091911978411560252973727, 0.9774982091911978411560252973728),    -- R₂ 1 2
   (0.9544660800384671350763760925933, 0.9544660800384671350763760925934),    -- R₂ 2 0
   (0.2109437153081390675212372767857, 0.2109437153081390675212372767858),    -- R₂ 2 1
   (-0.2109437153081390675212372767858, -0.2109437153081390675212372767857),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the disdyakis dodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.DisdyakisDodecahedron
