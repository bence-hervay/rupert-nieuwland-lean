import Polyhedra.Catalan.DisdyakisTriacontahedron.Proof.Optimum
import Polyhedra.Catalan.DisdyakisTriacontahedron.Proof.Enclosure

/-!
# The disdyakis triacontahedron: the result

The disdyakis triacontahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Catalan.DisdyakisTriacontahedron

open Notation

/-- **The disdyakis triacontahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the disdyakis triacontahedron.** The system `system` has exactly one root in
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
  [(1.000743186023585923160950767391, 1.0007431860235859231609507673911),     -- ν
   (0.1264317932616910476101978572764, 0.1264317932616910476101978572765),    -- R₁ 0 0
   (0.9919039455762166890575164733269, 0.991903945576216689057516473327),     -- R₁ 0 1
   (0.0118980840040224449031767987975, 0.0118980840040224449031767987976),    -- R₁ 0 2
   (-0.1324644179292688589662671284003, -0.1324644179292688589662671284002),  -- R₁ 1 0
   (0.0049950687574160991978045145519, 0.004995068757416099197804514552),     -- R₁ 1 1
   (0.9911751748660620487326176787974, 0.9911751748660620487326176787975),    -- R₁ 1 2
   (0.9830911349591618655299208216892, 0.9830911349591618655299208216893),    -- R₁ 2 0
   (-0.1268921275668528073117557292489, -0.1268921275668528073117557292488),  -- R₁ 2 1
   (0.1320235142929642847360808855537, 0.1320235142929642847360808855538),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 1 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 2 0
   (0, 0),                                                                    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the disdyakis triacontahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.DisdyakisTriacontahedron
