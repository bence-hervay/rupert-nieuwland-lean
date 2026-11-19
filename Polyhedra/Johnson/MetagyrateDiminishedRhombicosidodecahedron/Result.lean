import Polyhedra.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.MetagyrateDiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The metagyrate diminished rhombicosidodecahedron: the result

The metagyrate diminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal
pose are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them
to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.MetagyrateDiminishedRhombicosidodecahedron

open Notation

/-- **The metagyrate diminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the metagyrate diminished rhombicosidodecahedron.** The system `system` has
exactly one root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`,
which is greater than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation
`t` with which the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy
fits through it (`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
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
  [(1.006155356560708554068280956734, 1.0061553565607085540682809567341),     -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.2278759521915720906368166199561, 0.2278759521915720906368166199562),    -- R₁ 0 1
   (0.9736901716730966114729586495275, 0.9736901716730966114729586495276),    -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.9736901716730966114729586495276, -0.9736901716730966114729586495275),  -- R₁ 1 1
   (0.2278759521915720906368166199561, 0.2278759521915720906368166199562),    -- R₁ 1 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.598515424639987073224310151365, 0.5985154246399870732243101513651),     -- R₂ 0 0
   (0.8011112821999300457858927320626, 0.8011112821999300457858927320627),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.2837603262219727813520973152202, 0.2837603262219727813520973152203),    -- R₂ 1 0
   (-0.211999176541793219872309042554, -0.2119991765417932198723090425539),   -- R₂ 1 1
   (0.9351665233572046433166452428993, 0.9351665233572046433166452428994),    -- R₂ 1 2
   (0.7491724525971410415759904518655, 0.7491724525971410415759904518656),    -- R₂ 2 0
   (-0.5597115888362377268101615713556, -0.5597115888362377268101615713555),  -- R₂ 2 1
   (-0.3542083759483940016850095945749, -0.3542083759483940016850095945748),  -- R₂ 2 2
   (0.0405551479156255951127182241549, 0.040555147915625595112718224155),     -- t 0
   (-0.0158760130990034807777938890354, -0.0158760130990034807777938890353)]  -- t 1

/-- **The enclosure of the optimum of the metagyrate diminished rhombicosidodecahedron.** At the
root of `system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.MetagyrateDiminishedRhombicosidodecahedron
