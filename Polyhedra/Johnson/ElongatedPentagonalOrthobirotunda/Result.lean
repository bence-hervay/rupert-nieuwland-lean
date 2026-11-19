import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Proof.Optimum
import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Proof.Enclosure
import Polyhedra.Johnson.ElongatedPentagonalOrthobirotunda.Proof.Theta

/-!
# The elongated pentagonal orthobirotunda: the result

The elongated pentagonal orthobirotunda is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedPentagonalOrthobirotunda

open Notation

/-- **The elongated pentagonal orthobirotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated pentagonal orthobirotunda.** The system `system` has exactly one
root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
greater than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with
which the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits
through it (`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
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
  [(1.04602921266804112810626005993, 1.0460292126680411281062600599301),      -- ν
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 0 0
   (0.9510565162951535721164393333793, 0.9510565162951535721164393333794),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.9510565162951535721164393333793, 0.9510565162951535721164393333794),    -- R₁ 1 0
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 0 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 2
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₂ 1 0
   (-0.5877852522924731291687059546391, -0.587785252292473129168705954639),   -- R₂ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 2
   (0.587785252292473129168705954639, 0.5877852522924731291687059546391),     -- R₂ 2 0
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₂ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the elongated pentagonal orthobirotunda.** At the root of
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
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ElongatedPentagonalOrthobirotunda
