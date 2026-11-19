import Polyhedra.Johnson.MetabiaugmentedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.MetabiaugmentedDodecahedron.Proof.Enclosure

/-!
# The metabiaugmented dodecahedron: the result

The metabiaugmented dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.MetabiaugmentedDodecahedron

open Notation

/-- **The metabiaugmented dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the metabiaugmented dodecahedron.** The system `system` has exactly one root in
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
  [(1.016561740469542023745358749236, 1.0165617404695420237453587492361),     -- ν
   (0.541557009827323407455974396449, 0.5415570098273234074559743964491),     -- R₁ 0 0
   (-0.1442582956343459784800862811614, -0.1442582956343459784800862811613),  -- R₁ 0 1
   (-0.8281941494888514209050431144445, -0.8281941494888514209050431144444),  -- R₁ 0 2
   (-0.79275807312496533153530649033, -0.7927580731249653315353064903299),    -- R₁ 1 0
   (0.2401811533068975233120580046188, 0.2401811533068975233120580046189),    -- R₁ 1 1
   (-0.560221073408846973058885075659, -0.5602210734088469730588850756589),   -- R₁ 1 2
   (0.2797331632146615154444113640132, 0.2797331632146615154444113640133),    -- R₁ 2 0
   (0.9599492474796999521361936274536, 0.9599492474796999521361936274537),    -- R₁ 2 1
   (0.0157098587223856556991171673863, 0.0157098587223856556991171673864),    -- R₁ 2 2
   (0.8008067053256138929487044166063, 0.8008067053256138929487044166064),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.5989228837718052975689549163546, 0.5989228837718052975689549163547),    -- R₂ 0 2
   (-0.0170067015549832379486551072916, -0.0170067015549832379486551072915),  -- R₂ 1 0
   (0.9995967671169010701308451694688, 0.9995967671169010701308451694689),    -- R₂ 1 1
   (0.0227392891634628319454533008882, 0.0227392891634628319454533008883),    -- R₂ 1 2
   (-0.5986813783706280672421761353003, -0.5986813783706280672421761353002),  -- R₂ 2 0
   (-0.0283954779751961115508023876701, -0.02839547797519611155080238767),    -- R₂ 2 1
   (0.800483793729020490502329683241, 0.8004837937290204905023296832411),     -- R₂ 2 2
   (-0.0033752681240870401542397677241, -0.003375268124087040154239767724),   -- t 0
   (-0.0124329139610264664677615846913, -0.0124329139610264664677615846912)]  -- t 1

/-- **The enclosure of the optimum of the metabiaugmented dodecahedron.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.MetabiaugmentedDodecahedron
