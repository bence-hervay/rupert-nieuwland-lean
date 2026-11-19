import Polyhedra.Johnson.MetabiaugmentedHexagonalPrism.Proof.Optimum
import Polyhedra.Johnson.MetabiaugmentedHexagonalPrism.Proof.Enclosure
import Polyhedra.Johnson.MetabiaugmentedHexagonalPrism.Proof.Theta

/-!
# The metabiaugmented hexagonal prism: the result

The metabiaugmented hexagonal prism is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.MetabiaugmentedHexagonalPrism

open Notation

/-- **The metabiaugmented hexagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the metabiaugmented hexagonal prism.** The system `system` has exactly one root
in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
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
  [(1.1270120776412946121052333563514, 1.1270120776412946121052333563515),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 1 2
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.6424109729333436195768101210907, 0.6424109729333436195768101210908),    -- R₂ 0 1
   (0.7663603211641602543102224766679, 0.766360321164160254310222476668),     -- R₂ 0 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0.7663603211641602543102224766679, 0.766360321164160254310222476668),     -- R₂ 2 1
   (-0.6424109729333436195768101210908, -0.6424109729333436195768101210907),  -- R₂ 2 2
   (0.2104715458584526395354098714935, 0.2104715458584526395354098714936),    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the metabiaugmented hexagonal prism.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
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

end Nieuwland.Johnson.MetabiaugmentedHexagonalPrism
