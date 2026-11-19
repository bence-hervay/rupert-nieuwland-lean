import Polyhedra.Johnson.SquareGyrobicupola.Proof.Optimum
import Polyhedra.Johnson.SquareGyrobicupola.Proof.Enclosure

/-!
# The square gyrobicupola: the result

The square gyrobicupola is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.SquareGyrobicupola

open Notation

/-- **The square gyrobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the square gyrobicupola.** The system `system` has exactly one root in its box;
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
  [(1.0823922002923939687994464107327, 1.0823922002923939687994464107328),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (-0.3051015928743448369568043968143, -0.3051015928743448369568043968142),  -- R₁ 0 1
   (0.9523198086911442229146817535362, 0.9523198086911442229146817535363),    -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (0.9523198086911442229146817535362, 0.9523198086911442229146817535363),    -- R₁ 1 1
   (0.3051015928743448369568043968142, 0.3051015928743448369568043968143),    -- R₁ 1 2
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.7972688835488182886782571300399, 0.79726888354881828867825713004),      -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.6036243263196247483800605555182, 0.6036243263196247483800605555183),    -- R₂ 0 2
   (-0.1464165974210207593313232552328, -0.1464165974210207593313232552327),  -- R₂ 1 0
   (0.9701357927029309544287008989113, 0.9701357927029309544287008989114),    -- R₂ 1 1
   (0.1933874962770512633468510025246, 0.1933874962770512633468510025247),    -- R₂ 1 2
   (-0.5855975643088618242287261886345, -0.5855975643088618242287261886344),  -- R₂ 2 0
   (-0.2425624532293812762135634306841, -0.242562453229381276213563430684),   -- R₂ 2 1
   (0.7734590803390135784002412463156, 0.7734590803390135784002412463157),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the square gyrobicupola.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.SquareGyrobicupola
