import Polyhedra.Johnson.TriaugmentedTruncatedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.TriaugmentedTruncatedDodecahedron.Proof.Enclosure

/-!
# The triaugmented truncated dodecahedron: the result

The triaugmented truncated dodecahedron is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.TriaugmentedTruncatedDodecahedron

open Notation

/-- **The triaugmented truncated dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triaugmented truncated dodecahedron.** The system `system` has exactly one
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
  [(1.0009150164723090837716776172899, 1.00091501647230908377167761729),      -- ν
   (0.8088646031684422544157589175245, 0.8088646031684422544157589175246),    -- R₁ 0 0
   (-0.3087705416641281674092971924693, -0.3087705416641281674092971924692),  -- R₁ 0 1
   (0.5003986474218323943341399788394, 0.5003986474218323943341399788395),    -- R₁ 0 2
   (-0.3094156649899265143519318329921, -0.309415664989926514351931832992),   -- R₁ 1 0
   (0.5001522322383127976947422220241, 0.5001522322383127976947422220242),    -- R₁ 1 1
   (0.8087704809436818114402002876013, 0.8087704809436818114402002876014),    -- R₁ 1 2
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 0
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 2 1
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 2 2
   (0.9999559624972480333298491157085, 0.9999559624972480333298491157086),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.009384725153262865312527316429, 0.0093847251532628653125273164291),     -- R₂ 0 2
   (0.0014989756968157417151777251273, 0.0014989756968157417151777251274),    -- R₂ 1 0
   (0.9871615411462627508856547451233, 0.9871615411462627508856547451234),    -- R₂ 1 1
   (-0.1597180163713403674258082390671, -0.159718016371340367425808239067),   -- R₂ 1 2
   (-0.0092642397455290670172119368079, -0.0092642397455290670172119368078),  -- R₂ 2 0
   (0.1597250502636809122886969771433, 0.1597250502636809122886969771434),    -- R₂ 2 1
   (0.9871180690171778866804733222473, 0.9871180690171778866804733222474),    -- R₂ 2 2
   (0.0047285309869408037078352567274, 0.0047285309869408037078352567275),    -- t 0
   (-0.0412443622603946575153674701748, -0.0412443622603946575153674701747)]  -- t 1

/-- **The enclosure of the optimum of the triaugmented truncated dodecahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TriaugmentedTruncatedDodecahedron
