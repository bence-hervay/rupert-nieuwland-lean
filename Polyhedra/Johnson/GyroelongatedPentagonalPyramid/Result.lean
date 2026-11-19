import Polyhedra.Johnson.GyroelongatedPentagonalPyramid.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedPentagonalPyramid.Proof.Enclosure

/-!
# The gyroelongated pentagonal pyramid: the result

The gyroelongated pentagonal pyramid is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedPentagonalPyramid

open Notation

/-- **The gyroelongated pentagonal pyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated pentagonal pyramid.** The system `system` has exactly one
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
  [(1.0146438912363301577972413929182, 1.0146438912363301577972413929183),    -- ν
   (0.1452729237608711229846797527587, 0.1452729237608711229846797527588),    -- R₁ 0 0
   (-0.4301181417268422012375103432121, -0.430118141726842201237510343212),   -- R₁ 0 1
   (-0.8910073859286555947639922280982, -0.8910073859286555947639922280981),  -- R₁ 0 2
   (0.2659111259610264886879209824454, 0.2659111259610264886879209824455),    -- R₁ 1 0
   (-0.8504525894833455662665928811787, -0.8504525894833455662665928811786),  -- R₁ 1 1
   (0.4538960961841500646649032431569, 0.453896096184150064664903243157),     -- R₁ 1 2
   (-0.9529884840396064465180730573927, -0.9529884840396064465180730573926),  -- R₁ 2 0
   (-0.302867590208196737021762447689, -0.3028675902081967370217624476889),   -- R₁ 2 1
   (-0.0091745348314005071427966537919, -0.0091745348314005071427966537918),  -- R₁ 2 2
   (0.9951535870477848434190471350344, 0.9951535870477848434190471350345),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.0983327930343022155952784013849, -0.0983327930343022155952784013848),  -- R₂ 0 2
   (0.0351114996754835090954713683375, 0.0351114996754835090954713683376),    -- R₂ 1 0
   (0.9340783694599410631092307455996, 0.9340783694599410631092307455997),    -- R₂ 1 1
   (0.3553375610565204013013766036207, 0.3553375610565204013013766036208),    -- R₂ 1 2
   (0.0918505349819228639630209340706, 0.0918505349819228639630209340707),    -- R₂ 2 0
   (-0.3570680603289208261162769098197, -0.3570680603289208261162769098196),  -- R₂ 2 1
   (0.9295514399518063903875064924039, 0.929551439951806390387506492404),     -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0.027610392246369953905768110375, 0.0276103922463699539057681103751)]     -- t 1

/-- **The enclosure of the optimum of the gyroelongated pentagonal pyramid.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.GyroelongatedPentagonalPyramid
