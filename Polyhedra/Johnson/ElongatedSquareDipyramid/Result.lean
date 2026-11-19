import Polyhedra.Johnson.ElongatedSquareDipyramid.Proof.Optimum
import Polyhedra.Johnson.ElongatedSquareDipyramid.Proof.Enclosure

/-!
# The elongated square dipyramid: the result

The elongated square dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedSquareDipyramid

open Notation

/-- **The elongated square dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated square dipyramid.** The system `system` has exactly one root in
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
  [(1.2247448713915890490986420373529, 1.224744871391589049098642037353),     -- ν
   (-0.985598559653488780875362792953, -0.9855985596534887808753627929529),   -- R₁ 0 0
   (0.1691019787257627481429347680509, 0.169101978725762748142934768051),     -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.1691019787257627481429347680509, 0.169101978725762748142934768051),     -- R₁ 1 0
   (0.9855985596534887808753627929529, 0.985598559653488780875362792953),     -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 2
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 0 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 2 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the elongated square dipyramid.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ElongatedSquareDipyramid
