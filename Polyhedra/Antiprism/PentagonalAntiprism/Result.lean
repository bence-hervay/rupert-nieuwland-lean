import Polyhedra.Antiprism.PentagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.PentagonalAntiprism.Proof.Enclosure

/-!
# The pentagonal antiprism: the result

The pentagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Antiprism.PentagonalAntiprism

open Notation

/-- **The pentagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal antiprism.** The system `system` has exactly one root in its
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
  [(1.0378117386301360380125692589104, 1.0378117386301360380125692589105),    -- ν
   (-0.5475736497219353743543198404066, -0.5475736497219353743543198404065),  -- R₁ 0 0
   (0.7993699745441728438444761194008, 0.7993699745441728438444761194009),    -- R₁ 0 1
   (0.2473271960934496252249402038185, 0.2473271960934496252249402038186),    -- R₁ 0 2
   (0.2797392654791436953460547125769, 0.279739265479143695346054712577),     -- R₁ 1 0
   (-0.1036893328785489484764914125932, -0.1036893328785489484764914125931),  -- R₁ 1 1
   (0.9544603006916477468971513545979, 0.954460300691647746897151354598),     -- R₁ 1 2
   (0.7886120982329578668911257730783, 0.7886120982329578668911257730784),    -- R₁ 2 0
   (0.5918244385326191712480069839587, 0.5918244385326191712480069839588),    -- R₁ 2 1
   (-0.1668376230835289860311798747693, -0.1668376230835289860311798747692),  -- R₁ 2 2
   (-0.1529629062111422108242260109229, -0.1529629062111422108242260109228),  -- R₂ 0 0
   (0.9882319309369847070128578490522, 0.9882319309369847070128578490523),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4677468314462586584047956656662, 0.4677468314462586584047956656663),    -- R₂ 1 0
   (0.0723999219912226349741087795626, 0.0723999219912226349741087795627),    -- R₂ 1 1
   (0.8808922482163469290117654111843, 0.8808922482163469290117654111844),    -- R₂ 1 2
   (0.8705258474022621483117614044512, 0.8705258474022621483117614044513),    -- R₂ 2 0
   (0.1347438383460392797521376980034, 0.1347438383460392797521376980035),    -- R₂ 2 1
   (-0.4733168569070299134247923757085, -0.4733168569070299134247923757084),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the pentagonal antiprism.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Antiprism.PentagonalAntiprism
