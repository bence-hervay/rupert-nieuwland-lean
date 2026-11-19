import Polyhedra.Johnson.ParabiaugmentedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.ParabiaugmentedDodecahedron.Proof.Enclosure

/-!
# The parabiaugmented dodecahedron: the result

The parabiaugmented dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ParabiaugmentedDodecahedron

open Notation

/-- **The parabiaugmented dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the parabiaugmented dodecahedron.** The system `system` has exactly one root in
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
  [(1.0287728842057379736975368664039, 1.028772884205737973697536866404),     -- ν
   (0.9873663974572094170276424809337, 0.9873663974572094170276424809338),    -- R₁ 0 0
   (-0.0923538457085370347078423969875, -0.0923538457085370347078423969874),  -- R₁ 0 1
   (-0.1287569973058384768982870881892, -0.1287569973058384768982870881891),  -- R₁ 0 2
   (0.1269488250288127593435357585504, 0.1269488250288127593435357585505),    -- R₁ 1 0
   (0.9473366918912574183329957514923, 0.9473366918912574183329957514924),    -- R₁ 1 1
   (0.2940020204358002269882415550474, 0.2940020204358002269882415550475),    -- R₁ 1 2
   (0.0948240106522385203244800715076, 0.0948240106522385203244800715077),    -- R₁ 2 0
   (-0.3066332652850511369607600749513, -0.3066332652850511369607600749512),  -- R₁ 2 1
   (0.9470926288512922477234638502906, 0.9470926288512922477234638502907),    -- R₁ 2 2
   (0.8994194038237639416420486573505, 0.8994194038237639416420486573506),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4370866459013647846638256440389, 0.437086645901364784663825644039),     -- R₂ 0 2
   (0.0704260441070135253156776628183, 0.0704260441070135253156776628184),    -- R₂ 1 0
   (0.9869338359252762023051806433659, 0.986933835925276202305180643366),     -- R₂ 1 1
   (-0.1449198944840113320211767541367, -0.1449198944840113320211767541366),  -- R₂ 1 2
   (-0.4313756000711468504601426870159, -0.4313756000711468504601426870158),  -- R₂ 2 0
   (0.1611260485018483676253159883547, 0.1611260485018483676253159883548),    -- R₂ 2 1
   (0.8876674423214123813091452482374, 0.8876674423214123813091452482375),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the parabiaugmented dodecahedron.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ParabiaugmentedDodecahedron
