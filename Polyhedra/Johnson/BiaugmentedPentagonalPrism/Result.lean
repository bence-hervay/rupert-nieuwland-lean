import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Proof.Optimum
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Proof.Enclosure
import Polyhedra.Johnson.BiaugmentedPentagonalPrism.Proof.Theta

/-!
# The biaugmented pentagonal prism: the result

The biaugmented pentagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.BiaugmentedPentagonalPrism

open Notation

/-- **The biaugmented pentagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the biaugmented pentagonal prism.** The system `system` has exactly one root in
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
  [(1.0981426854122290489182414241253, 1.0981426854122290489182414241254),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0.6891517577746516785798148918166, 0.6891517577746516785798148918167),    -- R₂ 1 1
   (-0.724617040067446812790110697271, -0.7246170400674468127901106972709),   -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0.7246170400674468127901106972709, 0.724617040067446812790110697271),     -- R₂ 2 1
   (0.6891517577746516785798148918166, 0.6891517577746516785798148918167),    -- R₂ 2 2
   (-0.0892020469411323689277973117061, -0.089202046941132368927797311706),   -- t 0
   (0.0727824809931908505056541686276, 0.0727824809931908505056541686277)]    -- t 1

/-- **The enclosure of the optimum of the biaugmented pentagonal prism.** At the root of `system`,
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
    polyEval [121/65536, 0, -119/2048, 0, 139/256, 0, -11/8, 0, 1] θ = 0 ∧
      (0.6940362703719873214578702692175 : ℝ) ≤ θ ∧
      θ ≤ (0.6940362703719873214578702692176 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.BiaugmentedPentagonalPrism
