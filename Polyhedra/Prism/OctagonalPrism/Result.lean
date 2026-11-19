import Polyhedra.Prism.OctagonalPrism.Proof.Optimum
import Polyhedra.Prism.OctagonalPrism.Proof.Enclosure

/-!
# The octagonal prism: the result

The octagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Prism.OctagonalPrism

open Notation

/-- **The octagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the octagonal prism.** The system `system` has exactly one root in its box; at
the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and
the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.0596191012184288965645352532419, 1.059619101218428896564535253242),     -- ν
   (0.5202703854752282490903603173595, 0.5202703854752282490903603173596),    -- R₁ 0 0
   (0.5202703854752282490903603173595, 0.5202703854752282490903603173596),    -- R₁ 0 1
   (0.6772277696572363777716606876622, 0.6772277696572363777716606876623),    -- R₁ 0 2
   (-0.4788723483324730523272816501611, -0.478872348332473052327281650161),   -- R₁ 1 0
   (-0.4788723483324730523272816501611, -0.478872348332473052327281650161),   -- R₁ 1 1
   (0.7357734352401459097680554122576, 0.7357734352401459097680554122577),    -- R₁ 1 2
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 2 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9577446966649461046545633003221, 0.9577446966649461046545633003222),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.2876197072701562531793491650648, -0.2876197072701562531793491650647),  -- R₂ 0 2
   (0.0795020227170984945936633658724, 0.0795020227170984945936633658725),    -- R₂ 1 0
   (0.9610387482333580035870572688467, 0.9610387482333580035870572688468),    -- R₂ 1 1
   (0.2647337394023479653202707962245, 0.2647337394023479653202707962246),    -- R₂ 1 2
   (0.276413683442155824000710225605, 0.2764136834421558240007102256051),     -- R₂ 2 0
   (-0.2764136834421558240007102256051, -0.276413683442155824000710225605),   -- R₂ 2 1
   (0.9204297644100169702645220555897, 0.9204297644100169702645220555898),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the octagonal prism.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Prism.OctagonalPrism
