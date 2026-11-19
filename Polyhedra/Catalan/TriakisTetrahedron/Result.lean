import Polyhedra.Catalan.TriakisTetrahedron.Proof.Optimum
import Polyhedra.Catalan.TriakisTetrahedron.Proof.Enclosure

/-!
# The triakis tetrahedron: the result

The triakis tetrahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Catalan.TriakisTetrahedron

open Notation

/-- **The triakis tetrahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triakis tetrahedron.** The system `system` has exactly one root in its box;
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
  [(1.0000040886394064444856364939547, 1.0000040886394064444856364939548),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.6840941283902629343989558359032, 0.6840941283902629343989558359033),    -- R₁ 0 1
   (-0.7293937369500552904037689692092, -0.7293937369500552904037689692091),  -- R₁ 0 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.7293937369500552904037689692092, -0.7293937369500552904037689692091),  -- R₁ 2 1
   (-0.6840941283902629343989558359033, -0.6840941283902629343989558359032),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₂ 0 1
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 0 2
   (0.9998695736975656654408057654997, 0.9998695736975656654408057654998),    -- R₂ 1 0
   (0.0114200611611388147128126577378, 0.0114200611611388147128126577379),    -- R₂ 1 1
   (0.0114200611611388147128126577378, 0.0114200611611388147128126577379),    -- R₂ 1 2
   (-0.0161504053772127474076981518108, -0.0161504053772127474076981518107),  -- R₂ 2 0
   (0.7070145558636511189229795920609, 0.707014555863651118922979592061),     -- R₂ 2 1
   (0.7070145558636511189229795920609, 0.707014555863651118922979592061),     -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0.0002241915697346317413845474251, 0.0002241915697346317413845474252)]    -- t 1

/-- **The enclosure of the optimum of the triakis tetrahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.TriakisTetrahedron
