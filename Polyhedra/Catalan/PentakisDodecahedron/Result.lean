import Polyhedra.Catalan.PentakisDodecahedron.Proof.Optimum
import Polyhedra.Catalan.PentakisDodecahedron.Proof.Enclosure

/-!
# The pentakis dodecahedron: the result

The pentakis dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Catalan.PentakisDodecahedron

open Notation

/-- **The pentakis dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentakis dodecahedron.** The system `system` has exactly one root in its
box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than
`1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
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
  [(1.0018672277430936521693494238824, 1.0018672277430936521693494238825),    -- ν
   (0.1527314576879885008758318908339, 0.152731457687988500875831890834),     -- R₁ 0 0
   (0.9804732227420439399214129385267, 0.9804732227420439399214129385268),    -- R₁ 0 1
   (-0.1238763953234532427051703872401, -0.12387639532345324270517038724),    -- R₁ 0 2
   (-0.3846886503965861763452633269848, -0.3846886503965861763452633269847),  -- R₁ 1 0
   (0.1744435240781277214863737268209, 0.174443524078127721486373726821),     -- R₁ 1 1
   (0.9064127642323097670392348799302, 0.9064127642323097670392348799303),    -- R₁ 1 2
   (0.9103228790316956965763138214832, 0.9103228790316956965763138214833),    -- R₁ 2 0
   (-0.0907838994152265087990016474005, -0.0907838994152265087990016474004),  -- R₁ 2 1
   (0.4038199345233104752579465772699, 0.40381993452331047525794657727),      -- R₁ 2 2
   (0.3865162702200635410074443047177, 0.3865162702200635410074443047178),    -- R₂ 0 0
   (0.9222825883942355017818961455171, 0.9222825883942355017818961455172),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.3993515519608993336755842645061, -0.399351551960899333675584264506),   -- R₂ 1 0
   (0.1673628823886462909250474494332, 0.1673628823886462909250474494333),    -- R₂ 1 1
   (0.9013922584230381933092830214448, 0.9013922584230381933092830214449),    -- R₂ 1 2
   (0.831338385256925293049852893984, 0.8313383852569252930498528939841),     -- R₂ 2 0
   (-0.348402773730912376770714129263, -0.3484027737309123767707141292629),   -- R₂ 2 1
   (0.4330034600958919949938196592877, 0.4330034600958919949938196592878),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the pentakis dodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.PentakisDodecahedron
