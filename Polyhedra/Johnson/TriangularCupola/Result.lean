import Polyhedra.Johnson.TriangularCupola.Proof.Optimum
import Polyhedra.Johnson.TriangularCupola.Proof.Enclosure

/-!
# The triangular cupola: the result

The triangular cupola is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.TriangularCupola

open Notation

/-- **The triangular cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triangular cupola.** The system `system` has exactly one root in its box;
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
  [(1.0629172211360579385027503334184, 1.0629172211360579385027503334185),    -- ν
   (-0.7015075216516932827020021755813, -0.7015075216516932827020021755812),  -- R₁ 0 0
   (0.5039281680289855955086976205356, 0.5039281680289855955086976205357),    -- R₁ 0 1
   (0.5039281680289855955086976205356, 0.5039281680289855955086976205357),    -- R₁ 0 2
   (-0.7126620496884193427143664401867, -0.7126620496884193427143664401866),  -- R₁ 1 0
   (-0.496040725613281131843430847954, -0.4960407256132811318434308479539),   -- R₁ 1 1
   (-0.496040725613281131843430847954, -0.4960407256132811318434308479539),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 1
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 2 2
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₂ 0 2
   (-0.408248290463863016366214012451, -0.4082482904638630163662140124509),   -- R₂ 1 0
   (0.8164965809277260327324280249019, 0.816496580927726032732428024902),     -- R₂ 1 1
   (-0.408248290463863016366214012451, -0.4082482904638630163662140124509),   -- R₂ 1 2
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₂ 2 0
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₂ 2 1
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₂ 2 2
   (-0.132935208839480383244980002945, -0.1329352088394803832449800029449),   -- t 0
   (0.2302505358247593530792463543064, 0.2302505358247593530792463543065)]    -- t 1

/-- **The enclosure of the optimum of the triangular cupola.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TriangularCupola
