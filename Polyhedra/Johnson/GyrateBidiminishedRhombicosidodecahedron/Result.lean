import Polyhedra.Johnson.GyrateBidiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.GyrateBidiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The gyrate bidiminished rhombicosidodecahedron: the result

The gyrate bidiminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal
pose are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them
to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.GyrateBidiminishedRhombicosidodecahedron

open Notation

/-- **The gyrate bidiminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyrate bidiminished rhombicosidodecahedron.** The system `system` has
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
  [(1.0062800843661519003640304077207, 1.0062800843661519003640304077208),    -- ν
   (0.4744164399774602697901371633301, 0.4744164399774602697901371633302),    -- R₁ 0 0
   (0.8803005404287292820160773291281, 0.8803005404287292820160773291282),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.8803005404287292820160773291281, 0.8803005404287292820160773291282),    -- R₁ 1 0
   (-0.4744164399774602697901371633302, -0.4744164399774602697901371633301),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 2
   (-0.0691950407912059678559893113306, -0.0691950407912059678559893113305),  -- R₂ 0 0
   (0.9976031507217202760762359111713, 0.9976031507217202760762359111714),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.5151219175383320490475965155328, 0.5151219175383320490475965155329),    -- R₂ 1 0
   (0.0357295203716251333911673597803, 0.0357295203716251333911673597804),    -- R₂ 1 1
   (0.8563718885190273812764550347014, 0.8563718885190273812764550347015),    -- R₂ 1 2
   (0.8543192941760915063035225275406, 0.8543192941760915063035225275407),    -- R₂ 2 0
   (0.0592566877585161893088779973829, 0.059256687758516189308877997383),     -- R₂ 2 1
   (-0.5163595535616190561311909312608, -0.5163595535616190561311909312607),  -- R₂ 2 2
   (-0.0326179538568581007117283042777, -0.0326179538568581007117283042776),  -- t 0
   (0.0258811488554629333049321497373, 0.0258811488554629333049321497374)]    -- t 1

/-- **The enclosure of the optimum of the gyrate bidiminished rhombicosidodecahedron.** At the root
of `system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.GyrateBidiminishedRhombicosidodecahedron
