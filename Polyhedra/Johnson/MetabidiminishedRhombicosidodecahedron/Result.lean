import Polyhedra.Johnson.MetabidiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.MetabidiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The metabidiminished rhombicosidodecahedron: the result

The metabidiminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal pose
are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.MetabidiminishedRhombicosidodecahedron

open Notation

/-- **The metabidiminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the metabidiminished rhombicosidodecahedron.** The system `system` has exactly
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
  [(1.0043485833456651536905307614664, 1.0043485833456651536905307614665),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (-0.0032231400182475925866495259919, -0.0032231400182475925866495259918),  -- R₁ 0 1
   (-0.9999948056707208571241833051708, -0.9999948056707208571241833051707),  -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (0.9999948056707208571241833051707, 0.9999948056707208571241833051708),    -- R₁ 1 1
   (-0.0032231400182475925866495259919, -0.0032231400182475925866495259918),  -- R₁ 1 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.3350966399829281766256343500292, 0.3350966399829281766256343500293),    -- R₂ 0 1
   (0.9421837622630480365004215951522, 0.9421837622630480365004215951523),    -- R₂ 0 2
   (0.9988950120319300924903260928265, 0.9988950120319300924903260928266),    -- R₂ 1 0
   (-0.044280180442369667674914292371, -0.0442801804423696676749142923709),   -- R₂ 1 1
   (0.0157486684428055230534816535178, 0.0157486684428055230534816535179),    -- R₂ 1 2
   (0.0469973928822677966685174721967, 0.0469973928822677966685174721968),    -- R₂ 2 0
   (0.9411426605420365302486076021756, 0.9411426605420365302486076021757),    -- R₂ 2 1
   (-0.3347263622276063874934535448913, -0.3347263622276063874934535448912),  -- R₂ 2 2
   (-0.0342735875863573721083280290175, -0.0342735875863573721083280290174),  -- t 0
   (-0.0070838953459506876270819957524, -0.0070838953459506876270819957523)]  -- t 1

/-- **The enclosure of the optimum of the metabidiminished rhombicosidodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.MetabidiminishedRhombicosidodecahedron
