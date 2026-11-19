import Polyhedra.Johnson.PentagonalOrthobicupola.Proof.Optimum
import Polyhedra.Johnson.PentagonalOrthobicupola.Proof.Enclosure
import Polyhedra.Johnson.PentagonalOrthobicupola.Proof.Theta

/-!
# The pentagonal orthobicupola: the result

The pentagonal orthobicupola is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.PentagonalOrthobicupola

open Notation

/-- **The pentagonal orthobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal orthobicupola.** The system `system` has exactly one root in its
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
  [(1.0514622242382672120513381696957, 1.0514622242382672120513381696958),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₂ 0 0
   (0.9510565162951535721164393333793, 0.9510565162951535721164393333794),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3858959657112087095137140200971, 0.3858959657112087095137140200972),    -- R₂ 1 0
   (0.1253851999563899693399180139364, 0.1253851999563899693399180139365),    -- R₂ 1 1
   (0.9139818681350903783784216412082, 0.9139818681350903783784216412083),    -- R₂ 1 2
   (0.8692484114654954858354317588342, 0.8692484114654954858354317588343),    -- R₂ 2 0
   (0.2824359298043051617782765999455, 0.2824359298043051617782765999456),    -- R₂ 2 1
   (-0.4057550304312816073253281910099, -0.4057550304312816073253281910098),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the pentagonal orthobicupola.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
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
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.PentagonalOrthobicupola
