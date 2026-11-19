import Polyhedra.Johnson.TriangularHebesphenorotunda.Proof.Optimum
import Polyhedra.Johnson.TriangularHebesphenorotunda.Proof.Enclosure

/-!
# The triangular hebesphenorotunda: the result

The triangular hebesphenorotunda is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.TriangularHebesphenorotunda

open Notation

/-- **The triangular hebesphenorotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triangular hebesphenorotunda.** The system `system` has exactly one root in
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
  [(1.0704662693192697958259095291382, 1.0704662693192697958259095291383),    -- ν
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 0 0
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₁ 0 1
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₁ 0 2
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 1 0
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₁ 1 1
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₁ 1 2
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₁ 2 0
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 1
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 2 2
   (-0.9341723589627156964511186235481, -0.934172358962715696451118623548),   -- R₂ 0 0
   (0.356822089773089931941969843046, 0.3568220897730899319419698430461),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.1784110448865449659709849215231, -0.178411044886544965970984921523),   -- R₂ 1 0
   (-0.4670861794813578482255593117741, -0.467086179481357848225559311774),   -- R₂ 1 1
   (0.8660254037844386467637231707529, 0.866025403784438646763723170753),     -- R₂ 1 2
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₂ 2 0
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₂ 2 1
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₂ 2 2
   (0.0130149103241430915456007184311, 0.0130149103241430915456007184312),    -- t 0
   (-0.08394088062702362466096820877, -0.0839408806270236246609682087699)]    -- t 1

/-- **The enclosure of the optimum of the triangular hebesphenorotunda.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TriangularHebesphenorotunda
