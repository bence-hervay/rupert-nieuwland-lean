import Polyhedra.Johnson.PentagonalRotunda.Proof.Optimum
import Polyhedra.Johnson.PentagonalRotunda.Proof.Enclosure

/-!
# The pentagonal rotunda: the result

The pentagonal rotunda is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.PentagonalRotunda

open Notation

/-- **The pentagonal rotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal rotunda.** The system `system` has exactly one root in its box;
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
  [(1.0226001509349129423814875131527, 1.0226001509349129423814875131528),    -- ν
   (0.5747948029883332489647061808155, 0.5747948029883332489647061808156),    -- R₁ 0 0
   (0.2380744912236238108722630936948, 0.2380744912236238108722630936949),    -- R₁ 0 1
   (-0.7828994003613847677284158331049, -0.7828994003613847677284158331048),  -- R₁ 0 2
   (0.1228919739858118426614230649866, 0.1228919739858118426614230649867),    -- R₁ 1 0
   (0.9207763212724827564441156187942, 0.9207763212724827564441156187943),    -- R₁ 1 1
   (0.3702276717288757229206525095393, 0.3702276717288757229206525095394),    -- R₁ 1 2
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₁ 2 0
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₁ 2 1
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.5257311121191336060256690848479, -0.5257311121191336060256690848478),  -- R₂ 0 1
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₂ 0 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₂ 2 1
   (0.5257311121191336060256690848478, 0.5257311121191336060256690848479),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (-0.1709933673541064590380706562075, -0.1709933673541064590380706562074)]  -- t 1

/-- **The enclosure of the optimum of the pentagonal rotunda.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.PentagonalRotunda
