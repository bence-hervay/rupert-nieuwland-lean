import Polyhedra.Johnson.ParabiaugmentedHexagonalPrism.Proof.Optimum
import Polyhedra.Johnson.ParabiaugmentedHexagonalPrism.Proof.Enclosure
import Polyhedra.Johnson.ParabiaugmentedHexagonalPrism.Proof.Theta

/-!
# The parabiaugmented hexagonal prism: the result

The parabiaugmented hexagonal prism is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ParabiaugmentedHexagonalPrism

open Notation

/-- **The parabiaugmented hexagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the parabiaugmented hexagonal prism.** The system `system` has exactly one root
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
  [(1.1516126864206028779340745044951, 1.1516126864206028779340745044952),    -- ν
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₁ 0 0
   (-0.866025403784438646763723170753, -0.8660254037844386467637231707529),   -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 2
   (-0.866025403784438646763723170753, -0.8660254037844386467637231707529),   -- R₁ 2 0
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 1 1
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₂ 2 1
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the parabiaugmented hexagonal prism.** At the root of
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
    polyEval [25/4, 0, -7, 0, 1] θ = 0 ∧
      (2.4391575887554248179282907036107 : ℝ) ≤ θ ∧
      θ ≤ (2.4391575887554248179282907036108 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ParabiaugmentedHexagonalPrism
