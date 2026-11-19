import Polyhedra.Johnson.AugmentedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.AugmentedDodecahedron.Proof.Enclosure

/-!
# The augmented dodecahedron: the result

The augmented dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.AugmentedDodecahedron

open Notation

/-- **The augmented dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented dodecahedron.** The system `system` has exactly one root in its
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
  [(1.0141572390722075803603230828159, 1.014157239072207580360323082816),     -- ν
   (0.6517247171499079740632037185529, 0.651724717149907974063203718553),     -- R₁ 0 0
   (-0.6741378024143103763666315683568, -0.6741378024143103763666315683567),  -- R₁ 0 1
   (0.3475530411489398403792622330254, 0.3475530411489398403792622330255),    -- R₁ 0 2
   (0.7543850228399771252264286162579, 0.754385022839977125226428616258),     -- R₁ 1 0
   (0.623574989169823004303661825084, 0.6235749891698230043036618250841),     -- R₁ 1 1
   (-0.2050791803099044815311818216875, -0.2050791803099044815311818216874),  -- R₁ 1 2
   (-0.078473755935342091540410037168, -0.0784737559353420915404100371679),   -- R₁ 2 0
   (0.395843979666053966094916805276, 0.3958439796660539660949168052761),     -- R₁ 2 1
   (0.9149586949100713453914303659691, 0.9149586949100713453914303659692),    -- R₁ 2 2
   (0.859498766098507078087199925783, 0.8594987660985070780871999257831),     -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.5111378200399025647058127959353, 0.5111378200399025647058127959354),    -- R₂ 0 2
   (-0.0874172094855488922559243013954, -0.0874172094855488922559243013953),  -- R₂ 1 0
   (0.9852667357168846764615326840172, 0.9852667357168846764615326840173),    -- R₂ 1 1
   (0.14699554746846649356383981023, 0.1469955474684664935638398102301),      -- R₂ 1 2
   (-0.5036070914521592403923810761289, -0.5036070914521592403923810761288),  -- R₂ 2 0
   (-0.1710247335615364301524209276545, -0.1710247335615364301524209276544),  -- R₂ 2 1
   (0.8468355436265662520549803193537, 0.8468355436265662520549803193538),    -- R₂ 2 2
   (0.003882346636154438365400572914, 0.0038823466361544383654005729141),     -- t 0
   (0.0101124863207723297217147311474, 0.0101124863207723297217147311475)]    -- t 1

/-- **The enclosure of the optimum of the augmented dodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.AugmentedDodecahedron
