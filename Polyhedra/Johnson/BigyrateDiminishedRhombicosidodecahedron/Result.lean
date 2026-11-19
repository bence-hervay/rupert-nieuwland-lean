import Polyhedra.Johnson.BigyrateDiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.BigyrateDiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The bigyrate diminished rhombicosidodecahedron: the result

The bigyrate diminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal
pose are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them
to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.BigyrateDiminishedRhombicosidodecahedron

open Notation

/-- **The bigyrate diminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the bigyrate diminished rhombicosidodecahedron.** The system `system` has
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
  [(1.0054940369603552271400900220168, 1.0054940369603552271400900220169),    -- ν
   (0.6775954296907603683260542370298, 0.6775954296907603683260542370299),    -- R₁ 0 0
   (0.4788384750580056954643164574047, 0.4788384750580056954643164574048),    -- R₁ 0 1
   (0.5581918563238964701730614692594, 0.5581918563238964701730614692595),    -- R₁ 0 2
   (-0.6638592539314868603150547110604, -0.6638592539314868603150547110603),  -- R₁ 1 0
   (0.7248540007774349564544194360305, 0.7248540007774349564544194360306),    -- R₁ 1 1
   (0.1840586007946272831281341279494, 0.1840586007946272831281341279495),    -- R₁ 1 2
   (-0.3164732605319499499134539801013, -0.3164732605319499499134539801012),  -- R₁ 2 0
   (-0.4952780959835292181237912352474, -0.4952780959835292181237912352473),  -- R₁ 2 1
   (0.8090391109255513297884806036035, 0.8090391109255513297884806036036),    -- R₁ 2 2
   (0.7874453108557554948301881977143, 0.7874453108557554948301881977144),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.6163845247986702962778202438259, 0.616384524798670296277820243826),     -- R₂ 0 2
   (0.2270329213995009564098390367097, 0.2270329213995009564098390367098),    -- R₂ 1 0
   (0.9296951112537855844700929643846, 0.9296951112537855844700929643847),    -- R₂ 1 1
   (-0.290039743331184296122521485355, -0.2900397433311842961225214853549),   -- R₂ 1 2
   (-0.5730496793578115406347620304496, -0.5730496793578115406347620304495),  -- R₂ 2 0
   (0.3683300152184332162553110119788, 0.3683300152184332162553110119789),    -- R₂ 2 1
   (0.7320840558823133782087736911126, 0.7320840558823133782087736911127),    -- R₂ 2 2
   (0.0418504580096387708140848880734, 0.0418504580096387708140848880735),    -- t 0
   (0.0157265582595099621978443365138, 0.0157265582595099621978443365139)]    -- t 1

/-- **The enclosure of the optimum of the bigyrate diminished rhombicosidodecahedron.** At the root
of `system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.BigyrateDiminishedRhombicosidodecahedron
