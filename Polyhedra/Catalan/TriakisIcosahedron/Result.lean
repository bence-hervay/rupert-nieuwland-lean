import Polyhedra.Catalan.TriakisIcosahedron.Proof.Optimum
import Polyhedra.Catalan.TriakisIcosahedron.Proof.Enclosure

/-!
# The triakis icosahedron: the result

The triakis icosahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Catalan.TriakisIcosahedron

open Notation

/-- **The triakis icosahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triakis icosahedron.** The system `system` has exactly one root in its box;
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
  [(1.0013089815613548837217040369535, 1.0013089815613548837217040369536),    -- ν
   (0.9986874684281380390373639124254, 0.9986874684281380390373639124255),    -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.0512185552763526071645989412725, 0.0512185552763526071645989412726),    -- R₁ 0 2
   (-0.0407322274950424076232072359928, -0.0407322274950424076232072359927),  -- R₁ 1 0
   (0.6062644537265798083879349973332, 0.6062644537265798083879349973333),    -- R₁ 1 1
   (0.7942193008174152157525413324941, 0.7942193008174152157525413324942),    -- R₁ 1 2
   (-0.0310519894352825452963685924535, -0.0310519894352825452963685924534),  -- R₁ 2 0
   (-0.7952631087555940251882317953741, -0.795263108755594025188231795374),   -- R₁ 2 1
   (0.6054687124901660274954284975313, 0.6054687124901660274954284975314),    -- R₁ 2 2
   (0.9999947319098666593096414805081, 0.9999947319098666593096414805082),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.0032459440096692560965333580812, 0.0032459440096692560965333580813),    -- R₂ 0 2
   (-0.0010532049775943329572088537137, -0.0010532049775943329572088537136),  -- R₂ 1 0
   (0.9458966717587625212908483870201, 0.9458966717587625212908483870202),    -- R₂ 1 1
   (0.3244662958073935959293528241866, 0.3244662958073935959293528241867),    -- R₂ 1 2
   (-0.0030703276354614418135029287611, -0.003070327635461441813502928761),   -- R₂ 2 0
   (-0.3244680051340900275654899728799, -0.3244680051340900275654899728798),  -- R₂ 2 1
   (0.9458916886898388691563774606124, 0.9458916886898388691563774606125),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the triakis icosahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.TriakisIcosahedron
