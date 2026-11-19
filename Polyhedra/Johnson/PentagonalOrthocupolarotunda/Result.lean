import Polyhedra.Johnson.PentagonalOrthocupolarotunda.Proof.Optimum
import Polyhedra.Johnson.PentagonalOrthocupolarotunda.Proof.Enclosure

/-!
# The pentagonal orthocupolarotunda: the result

The pentagonal orthocupolarotunda is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.PentagonalOrthocupolarotunda

open Notation

/-- **The pentagonal orthocupolarotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal orthocupolarotunda.** The system `system` has exactly one root
in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
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
  [(1.0226001509349129423814875131527, 1.0226001509349129423814875131528),    -- ν
   (0.1606562433445127420132314663489, 0.160656243344512742013231466349),     -- R₁ 0 0
   (-0.8848603668157648658209300962221, -0.884860366815764865820930096222),   -- R₁ 0 1
   (-0.4372776037177055711509778940915, -0.4372776037177055711509778940914),  -- R₁ 0 2
   (-0.8509932852111282700907491748381, -0.850993285211128270090749174838),   -- R₁ 1 0
   (-0.3486124329770006351217072494542, -0.3486124329770006351217072494541),  -- R₁ 1 1
   (0.3927846739619909543708624788771, 0.3927846739619909543708624788772),    -- R₁ 1 2
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 0
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 2 1
   (-0.8090169943749474241022934171829, -0.8090169943749474241022934171828),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 2
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₂ 1 0
   (-0.5257311121191336060256690848479, -0.5257311121191336060256690848478),  -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0.5257311121191336060256690848478, 0.5257311121191336060256690848479),    -- R₂ 2 0
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0.1383365401148704636749634623448, 0.1383365401148704636749634623449),    -- t 0
   (0.100507379570573003477669604603, 0.1005073795705730034776696046031)]     -- t 1

/-- **The enclosure of the optimum of the pentagonal orthocupolarotunda.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.PentagonalOrthocupolarotunda
