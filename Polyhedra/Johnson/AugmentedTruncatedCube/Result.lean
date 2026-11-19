import Polyhedra.Johnson.AugmentedTruncatedCube.Proof.Optimum
import Polyhedra.Johnson.AugmentedTruncatedCube.Proof.Enclosure

/-!
# The augmented truncated cube: the result

The augmented truncated cube is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.AugmentedTruncatedCube

open Notation

/-- **The augmented truncated cube is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented truncated cube.** The system `system` has exactly one root in its
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
  [(1.0376444035133225592984139924167, 1.0376444035133225592984139924168),    -- ν
   (-0.3908903675447479386348210579123, -0.3908903675447479386348210579122),  -- R₁ 0 0
   (0.9204372442272921560205089846143, 0.9204372442272921560205089846144),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.9204372442272921560205089846143, 0.9204372442272921560205089846144),    -- R₁ 1 0
   (0.3908903675447479386348210579122, 0.3908903675447479386348210579123),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 2
   (-0.5202328887871009562755286365083, -0.5202328887871009562755286365082),  -- R₂ 0 0
   (0.8540244384232970227602150552029, 0.854024438423297022760215055203),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.5406447049927423484536794169558, 0.5406447049927423484536794169559),    -- R₂ 1 0
   (0.3293361923050933884296140866088, 0.3293361923050933884296140866089),    -- R₂ 1 1
   (0.7741065659205411643281981208181, 0.7741065659205411643281981208182),    -- R₂ 1 2
   (0.6611059252400771251745542769171, 0.6611059252400771251745542769172),    -- R₂ 2 0
   (0.4027156950179055267365645853296, 0.4027156950179055267365645853297),    -- R₂ 2 1
   (-0.6330553092729788146833806677858, -0.6330553092729788146833806677857),  -- R₂ 2 2
   (0.0163750911545849943762170023595, 0.0163750911545849943762170023596),    -- t 0
   (0.0211574457789175970881457054688, 0.0211574457789175970881457054689)]    -- t 1

/-- **The enclosure of the optimum of the augmented truncated cube.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.AugmentedTruncatedCube
