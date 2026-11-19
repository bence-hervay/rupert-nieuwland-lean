import Polyhedra.Johnson.MetabidiminishedIcosahedron.Proof.Optimum
import Polyhedra.Johnson.MetabidiminishedIcosahedron.Proof.Enclosure

/-!
# The metabidiminished icosahedron: the result

The metabidiminished icosahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.MetabidiminishedIcosahedron

open Notation

/-- **The metabidiminished icosahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the metabidiminished icosahedron.** The system `system` has exactly one root in
its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which
the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.0232693087461700721883245829337, 1.0232693087461700721883245829338),    -- ν
   (-0.103778572433156771865260525025, -0.1037785724331567718652605250249),   -- R₁ 0 0
   (0.4782875811103888014782417543092, 0.4782875811103888014782417543093),    -- R₁ 0 1
   (-0.8720498825522019911044575495523, -0.8720498825522019911044575495522),  -- R₁ 0 2
   (-0.1849140741711348167508193276795, -0.1849140741711348167508193276794),  -- R₁ 1 0
   (0.8522193278920288242349754362547, 0.8522193278920288242349754362548),    -- R₁ 1 1
   (0.4894170025047052994235077781707, 0.4894170025047052994235077781708),    -- R₁ 1 2
   (0.9772598390792328497431082523877, 0.9772598390792328497431082523878),    -- R₁ 2 0
   (0.2120452945076403128500959425087, 0.2120452945076403128500959425088),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.0333473833329946681312132920472, 0.0333473833329946681312132920473),    -- R₂ 0 1
   (0.9994438213450730565374020201376, 0.9994438213450730565374020201377),    -- R₂ 0 2
   (0.9277187126121981446618366349607, 0.9277187126121981446618366349608),    -- R₂ 1 0
   (-0.3730724322959609131752784141426, -0.3730724322959609131752784141425),  -- R₂ 1 1
   (0.0124479126740738231369089427873, 0.0124479126740738231369089427874),    -- R₂ 1 2
   (0.3732800426880142049530100090042, 0.3732800426880142049530100090043),    -- R₂ 2 0
   (0.9272027352664669366779716262562, 0.9272027352664669366779716262563),    -- R₂ 2 1
   (-0.0309369915346712868273430320571, -0.030936991534671286827343032057),   -- R₂ 2 2
   (-0.0335505762268351339026507040014, -0.0335505762268351339026507040013),  -- t 0
   (0.0188294531973179204631011754435, 0.0188294531973179204631011754436)]    -- t 1

/-- **The enclosure of the optimum of the metabidiminished icosahedron.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.MetabidiminishedIcosahedron
