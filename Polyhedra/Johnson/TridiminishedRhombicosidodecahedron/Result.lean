import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.TridiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The tridiminished rhombicosidodecahedron: the result

The tridiminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.TridiminishedRhombicosidodecahedron

open Notation

/-- **The tridiminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the tridiminished rhombicosidodecahedron.** The system `system` has exactly one
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
  [(1.003825292900091823107456981684, 1.0038252929000918231074569816841),     -- ν
   (0.2948833213468458770304241555723, 0.2948833213468458770304241555724),    -- R₁ 0 0
   (-0.9555332682808342862495980910139, -0.9555332682808342862495980910138),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.9555332682808342862495980910138, 0.9555332682808342862495980910139),    -- R₁ 1 0
   (0.2948833213468458770304241555723, 0.2948833213468458770304241555724),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.4610980430634518766283861140878, -0.4610980430634518766283861140877),  -- R₂ 0 1
   (0.8873491954597440658683173214253, 0.8873491954597440658683173214254),    -- R₂ 0 2
   (0.8242752737572734312493797617474, 0.8242752737572734312493797617475),    -- R₂ 1 0
   (0.5024075803683879097986036284687, 0.5024075803683879097986036284688),    -- R₂ 1 1
   (0.2610687577263004965383639258287, 0.2610687577263004965383639258288),    -- R₂ 1 2
   (-0.5661892555253693101196927252867, -0.5661892555253693101196927252866),  -- R₂ 2 0
   (0.7314200010058768703659141842611, 0.7314200010058768703659141842612),    -- R₂ 2 1
   (0.3800717156750698491432597571782, 0.3800717156750698491432597571783),    -- R₂ 2 2
   (0.0262386067891218742465954186156, 0.0262386067891218742465954186157),    -- t 0
   (-0.0109271287408750082498808310547, -0.0109271287408750082498808310546)]  -- t 1

/-- **The enclosure of the optimum of the tridiminished rhombicosidodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TridiminishedRhombicosidodecahedron
