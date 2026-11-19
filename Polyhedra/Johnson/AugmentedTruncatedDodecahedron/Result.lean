import Polyhedra.Johnson.AugmentedTruncatedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.AugmentedTruncatedDodecahedron.Proof.Enclosure

/-!
# The augmented truncated dodecahedron: the result

The augmented truncated dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.AugmentedTruncatedDodecahedron

open Notation

/-- **The augmented truncated dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented truncated dodecahedron.** The system `system` has exactly one
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
  [(1.0038080665637097454388487420757, 1.0038080665637097454388487420758),    -- ν
   (0.8380347769833112121798376038478, 0.8380347769833112121798376038479),    -- R₁ 0 0
   (0.3620046349091190123023925615729, 0.362004634909119012302392561573),     -- R₁ 0 1
   (0.4082283146363653358753372157092, 0.4082283146363653358753372157093),    -- R₁ 0 2
   (0.0112512756827735476969353614115, 0.0112512756827735476969353614116),    -- R₁ 1 0
   (0.7365711427687590732936964662635, 0.7365711427687590732936964662636),    -- R₁ 1 1
   (-0.6762664862580686594181625975837, -0.6762664862580686594181625975836),  -- R₁ 1 2
   (-0.5455007986813970456666979795991, -0.545500798681397045666697979599),   -- R₁ 2 0
   (0.5713279233020558315961538738151, 0.5713279233020558315961538738152),    -- R₁ 2 1
   (0.6131992194167554061635115661864, 0.6131992194167554061635115661865),    -- R₁ 2 2
   (0.8912368509723498576458779369732, 0.8912368509723498576458779369733),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4535381742134717490797634937515, 0.4535381742134717490797634937516),    -- R₂ 0 2
   (-0.0273040037988792272769962984146, -0.0273040037988792272769962984145),  -- R₂ 1 0
   (0.9981862015729583741763729615676, 0.9981862015729583741763729615677),    -- R₂ 1 1
   (0.0536544347272441376206541245443, 0.0536544347272441376206541245444),    -- R₂ 1 2
   (-0.4527155473864800231590257410241, -0.452715547386480023159025741024),   -- R₂ 2 0
   (-0.0602022174786719377966713127398, -0.0602022174786719377966713127397),  -- R₂ 2 1
   (0.8896203269739346775856176774771, 0.8896203269739346775856176774772),    -- R₂ 2 2
   (0.0065147701259236961023074490938, 0.0065147701259236961023074490939),    -- t 0
   (0.0090444132783039538072720587826, 0.0090444132783039538072720587827)]    -- t 1

/-- **The enclosure of the optimum of the augmented truncated dodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.AugmentedTruncatedDodecahedron
