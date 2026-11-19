import Polyhedra.Johnson.MetabiaugmentedTruncatedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.MetabiaugmentedTruncatedDodecahedron.Proof.Enclosure

/-!
# The metabiaugmented truncated dodecahedron: the result

The metabiaugmented truncated dodecahedron is Rupert, and its Nieuwland number and an optimal pose
are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.MetabiaugmentedTruncatedDodecahedron

open Notation

/-- **The metabiaugmented truncated dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the metabiaugmented truncated dodecahedron.** The system `system` has exactly
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
  [(1.0060522809873810949585100849889, 1.006052280987381094958510084989),     -- ν
   (0.9503231684326798377102189097235, 0.9503231684326798377102189097236),    -- R₁ 0 0
   (0.3112649603474063182169538254128, 0.3112649603474063182169538254129),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 1 2
   (-0.3112649603474063182169538254129, -0.3112649603474063182169538254128),  -- R₁ 2 0
   (0.9503231684326798377102189097235, 0.9503231684326798377102189097236),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.7925876807854904433296691021877, 0.7925876807854904433296691021878),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.609757958756650836961127825594, 0.6097579587566508369611278255941),     -- R₂ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 2
   (-0.6097579587566508369611278255941, -0.609757958756650836961127825594),   -- R₂ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 1
   (0.7925876807854904433296691021877, 0.7925876807854904433296691021878),    -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the metabiaugmented truncated dodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.MetabiaugmentedTruncatedDodecahedron
