import Polyhedra.Platonic.Icosahedron.Proof.Optimum
import Polyhedra.Platonic.Icosahedron.Proof.Enclosure

/-!
# The icosahedron: the result

The icosahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Platonic.Icosahedron

open Notation

/-- **The icosahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the icosahedron.** The system `system` has exactly one root in its box; at the
root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and the
variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
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
  [(1.0108230607529004713654982401957, 1.0108230607529004713654982401958),    -- ν
   (0.8831337463430174622291892504666, 0.8831337463430174622291892504667),    -- R₁ 0 0
   (0.1648429625116080686527718322233, 0.1648429625116080686527718322234),    -- R₁ 0 1
   (-0.4392056281294030367484859682773, -0.4392056281294030367484859682772),  -- R₁ 0 2
   (-0.0620133448997818232988106231574, -0.0620133448997818232988106231573),  -- R₁ 1 0
   (0.9690359097394198874804210157071, 0.9690359097394198874804210157072),    -- R₁ 1 1
   (0.2390057545119689719282887201866, 0.2390057545119689719282887201867),    -- R₁ 1 2
   (0.4650044420481245197226612505391, 0.4650044420481245197226612505392),    -- R₁ 2 0
   (-0.1838374372805807194717645023626, -0.1838374372805807194717645023625),  -- R₁ 2 1
   (0.8660107767976221641864643694531, 0.8660107767976221641864643694532),    -- R₁ 2 2
   (0.9956731479464690705518846100824, 0.9956731479464690705518846100825),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.0929246063126915489816569180866, -0.0929246063126915489816569180865),  -- R₂ 0 2
   (0.0372633557854924692740042394597, 0.0372633557854924692740042394598),    -- R₂ 1 0
   (0.9160752804714107325982505680687, 0.9160752804714107325982505680688),    -- R₂ 1 1
   (0.3992712396665078692681369222141, 0.3992712396665078692681369222142),    -- R₂ 1 2
   (0.0851259347905943350252750186098, 0.0851259347905943350252750186099),    -- R₂ 2 0
   (-0.401006334749497644463803118914, -0.4010063347494976444638031189139),   -- R₂ 2 1
   (0.9121115582629140869190087564429, 0.912111558262914086919008756443),     -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the icosahedron.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Platonic.Icosahedron
