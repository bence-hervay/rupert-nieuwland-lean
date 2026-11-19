import Polyhedra.Johnson.BiaugmentedTriangularPrism.Proof.Optimum
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Proof.Enclosure
import Polyhedra.Johnson.BiaugmentedTriangularPrism.Proof.Theta

/-!
# The biaugmented triangular prism: the result

The biaugmented triangular prism is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.BiaugmentedTriangularPrism

open Notation

/-- **The biaugmented triangular prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the biaugmented triangular prism.** The system `system` has exactly one root in
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
  [(1.1246516737930798255694786455248, 1.1246516737930798255694786455249),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 0 2
   (-0.4575882806851119863877107202539, -0.4575882806851119863877107202538),  -- R₁ 1 0
   (0.8891641948367259624005053597085, 0.8891641948367259624005053597086),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (0.8891641948367259624005053597085, 0.8891641948367259624005053597086),    -- R₁ 2 0
   (0.4575882806851119863877107202538, 0.4575882806851119863877107202539),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.5758992897782432065671951144279, -0.5758992897782432065671951144278),  -- R₂ 0 1
   (0.81752064685420334632283926461, 0.8175206468542033463228392646101),      -- R₂ 0 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0.81752064685420334632283926461, 0.8175206468542033463228392646101),      -- R₂ 2 1
   (0.5758992897782432065671951144278, 0.5758992897782432065671951144279),    -- R₂ 2 2
   (-0.1253704189552005760759538066049, -0.1253704189552005760759538066048),  -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the biaugmented triangular prism.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

@[inherit_doc] local notation "θ" => theta

/-- **`θ` is a root of its polynomial**, and it lies between these two rationals, which are at most
`2 ^ -100` apart. -/
theorem theta_isRoot :
    polyEval [1/256, 0, -5/8, 0, 1] θ = 0 ∧
      (0.7865660924854930855822837664288 : ℝ) ≤ θ ∧
      θ ≤ (0.7865660924854930855822837664289 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.BiaugmentedTriangularPrism
