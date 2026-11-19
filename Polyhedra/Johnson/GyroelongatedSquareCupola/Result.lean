import Polyhedra.Johnson.GyroelongatedSquareCupola.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedSquareCupola.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedSquareCupola.Proof.Theta

/-!
# The gyroelongated square cupola: the result

The gyroelongated square cupola is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedSquareCupola

open Notation

/-- **The gyroelongated square cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated square cupola.** The system `system` has exactly one root in
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
  [(1.0003610456081216533317338511708, 1.0003610456081216533317338511709),    -- ν
   (-0.0268644810599387584936999606423, -0.0268644810599387584936999606422),  -- R₁ 0 0
   (0.9996390846987627622764611536843, 0.9996390846987627622764611536844),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 2
   (0.9996390846987627622764611536843, 0.9996390846987627622764611536844),    -- R₁ 2 0
   (0.0268644810599387584936999606422, 0.0268644810599387584936999606423),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 0 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.5024913811124105824697075400215, 0.5024913811124105824697075400216),    -- R₂ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 1
   (0.8645822181306657785794611671934, 0.8645822181306657785794611671935),    -- R₂ 1 2
   (0.8645822181306657785794611671934, 0.8645822181306657785794611671935),    -- R₂ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 1
   (-0.5024913811124105824697075400216, -0.5024913811124105824697075400215),  -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (0.0584049618800220019401590846972, 0.0584049618800220019401590846973)]    -- t 1

/-- **The enclosure of the optimum of the gyroelongated square cupola.** At the root of `system`,
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
    polyEval [-1/512, 0, 1/16, 0, -1/2, 0, 1, 0, 1] θ = 0 ∧
      (0.430147784931485783221150388002 : ℝ) ≤ θ ∧
      θ ≤ (0.4301477849314857832211503880021 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedSquareCupola
