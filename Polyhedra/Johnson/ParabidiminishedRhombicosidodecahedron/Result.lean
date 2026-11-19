import Polyhedra.Johnson.ParabidiminishedRhombicosidodecahedron.Proof.Optimum
import Polyhedra.Johnson.ParabidiminishedRhombicosidodecahedron.Proof.Enclosure

/-!
# The parabidiminished rhombicosidodecahedron: the result

The parabidiminished rhombicosidodecahedron is Rupert, and its Nieuwland number and an optimal pose
are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ParabidiminishedRhombicosidodecahedron

open Notation

/-- **The parabidiminished rhombicosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the parabidiminished rhombicosidodecahedron.** The system `system` has exactly
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
  [(1.0022882219049060128459925264633, 1.0022882219049060128459925264634),    -- ν
   (0.4136254459582176643434251110682, 0.4136254459582176643434251110683),    -- R₁ 0 0
   (0.9016787467614156559401539605576, 0.9016787467614156559401539605577),    -- R₁ 0 1
   (-0.1260532748270683136339341492533, -0.1260532748270683136339341492532),  -- R₁ 0 2
   (-0.3412154529291743956643418867847, -0.3412154529291743956643418867846),  -- R₁ 1 0
   (0.2818856394481767675783792330944, 0.2818856394481767675783792330945),    -- R₁ 1 1
   (0.8967232019721753927030405860401, 0.8967232019721753927030405860402),    -- R₁ 1 2
   (0.8440888609253198353509527713379, 0.844088860925319835350952771338),     -- R₁ 2 0
   (-0.3278962090534981246507472746288, -0.3278962090534981246507472746287),  -- R₁ 2 1
   (0.4242617952987762527791691609416, 0.4242617952987762527791691609417),    -- R₁ 2 2
   (0.6710823381013398852554001358817, 0.6710823381013398852554001358818),    -- R₂ 0 0
   (0.7413828265399994694768121726056, 0.7413828265399994694768121726057),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.2009403346694484671794986404048, -0.2009403346694484671794986404047),  -- R₂ 1 0
   (0.1818864758955457709716573893195, 0.1818864758955457709716573893196),    -- R₂ 1 1
   (0.9625696295797146609669887420334, 0.9625696295797146609669887420335),    -- R₂ 1 2
   (0.7136325927193691369288755327367, 0.7136325927193691369288755327368),    -- R₂ 2 0
   (-0.645963477603695567866545442089, -0.6459634776036955678665454420889),   -- R₂ 2 1
   (0.2710345147961250089433362952848, 0.2710345147961250089433362952849),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the parabidiminished rhombicosidodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ParabidiminishedRhombicosidodecahedron
