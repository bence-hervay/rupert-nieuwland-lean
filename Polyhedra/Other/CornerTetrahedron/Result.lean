import Polyhedra.Other.CornerTetrahedron.Proof.Optimum
import Polyhedra.Other.CornerTetrahedron.Proof.Enclosure

/-!
# The corner tetrahedron: the result

The corner tetrahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.CornerTetrahedron

open Notation

/-- **The corner tetrahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the corner tetrahedron.** The system `system` has exactly one root in its box;
at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`,
and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
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
  [(1.1547005383792515290182975610039, 1.154700538379251529018297561004),     -- ν
   (0.7001400420140049017646470403301, 0.7001400420140049017646470403302),    -- R₁ 0 0
   (-0.1400280084028009803529294080661, -0.140028008402800980352929408066),   -- R₁ 0 1
   (0.7001400420140049017646470403301, 0.7001400420140049017646470403302),    -- R₁ 0 2
   (0.0990147542976674309153273129124, 0.0990147542976674309153273129125),    -- R₁ 1 0
   (0.9901475429766743091532731291244, 0.9901475429766743091532731291245),    -- R₁ 1 1
   (0.0990147542976674309153273129124, 0.0990147542976674309153273129125),    -- R₁ 1 2
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 2 2
   (0.9701425001453318940756258484644, 0.9701425001453318940756258484645),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.2425356250363329735189064621162, -0.2425356250363329735189064621161),  -- R₂ 0 2
   (-0.0571661950475029457928838517407, -0.0571661950475029457928838517406),  -- R₂ 1 0
   (0.9718253158075500784790254795909, 0.971825315807550078479025479591),     -- R₂ 1 1
   (-0.2286647801900117831715354069626, -0.2286647801900117831715354069625),  -- R₂ 1 2
   (0.2357022603955158414669481207016, 0.2357022603955158414669481207017),    -- R₂ 2 0
   (0.2357022603955158414669481207016, 0.2357022603955158414669481207017),    -- R₂ 2 1
   (0.9428090415820633658677924828064, 0.9428090415820633658677924828065),    -- R₂ 2 2
   (0.1616904166908886490126043080774, 0.1616904166908886490126043080775),    -- t 0
   (-0.171498585142508837378651555222, -0.1714985851425088373786515552219)]   -- t 1

/-- **The enclosure of the optimum of the corner tetrahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Other.CornerTetrahedron
