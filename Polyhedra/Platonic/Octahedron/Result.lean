import Polyhedra.Platonic.Octahedron.Proof.Optimum
import Polyhedra.Platonic.Octahedron.Proof.Enclosure

/-!
# The octahedron: the result

The octahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Platonic.Octahedron

open Notation

/-- **The octahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the octahedron.** The system `system` has exactly one root in its box; at the
root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and the
variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
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
  [(1.0606601717798212866012665431572, 1.0606601717798212866012665431573),    -- ν
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 0 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.2357022603955158414669481207016, 0.2357022603955158414669481207017),    -- R₁ 1 0
   (-0.2357022603955158414669481207017, -0.2357022603955158414669481207016),  -- R₁ 1 1
   (0.9428090415820633658677924828064, 0.9428090415820633658677924828065),    -- R₁ 1 2
   (0.6666666666666666666666666666666, 0.6666666666666666666666666666667),    -- R₁ 2 0
   (-0.6666666666666666666666666666667, -0.6666666666666666666666666666666),  -- R₁ 2 1
   (-0.3333333333333333333333333333334, -0.3333333333333333333333333333333),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 1 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 2 0
   (0, 0),                                                                    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the octahedron.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Platonic.Octahedron
