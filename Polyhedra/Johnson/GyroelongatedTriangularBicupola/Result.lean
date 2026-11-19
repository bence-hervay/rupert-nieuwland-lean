import Polyhedra.Johnson.GyroelongatedTriangularBicupola.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedTriangularBicupola.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedTriangularBicupola.Proof.Theta

/-!
# The gyroelongated triangular bicupola: the result

The gyroelongated triangular bicupola is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedTriangularBicupola

open Notation

/-- **The gyroelongated triangular bicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated triangular bicupola.** The system `system` has exactly one
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
  [(1.0063228683887248432827088292862, 1.0063228683887248432827088292863),    -- ν
   (0.9649912489781462618245284243091, 0.9649912489781462618245284243092),    -- R₁ 0 0
   (0.2585686258667947554954911334556, 0.2585686258667947554954911334557),    -- R₁ 0 1
   (0.0439790303776112061677231714188, 0.0439790303776112061677231714189),    -- R₁ 0 2
   (0.258819045102520762348898837624, 0.2588190451025207623488988376241),     -- R₁ 1 0
   (-0.9659258262890682867497431997289, -0.9659258262890682867497431997288),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (0.0424804812568861391885852819896, 0.0424804812568861391885852819897),    -- R₁ 2 0
   (0.0113826106468680854833063022256, 0.0113826106468680854833063022257),    -- R₁ 2 1
   (-0.9990324543712507194440000222024, -0.9990324543712507194440000222023),  -- R₁ 2 2
   (0.3730028358778987066647396181954, 0.3730028358778987066647396181955),    -- R₂ 0 0
   (0.927830202368431937094880871488, 0.9278302023684319370948808714881),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.927830202368431937094880871488, 0.9278302023684319370948808714881),     -- R₂ 2 0
   (-0.3730028358778987066647396181955, -0.3730028358778987066647396181954),  -- R₂ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (0.1673443147224766561420698566996, 0.1673443147224766561420698566997)]    -- t 1

/-- **The enclosure of the optimum of the gyroelongated triangular bicupola.** At the root of
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
    polyEval [-54767/20736, 631/36, -1181/48, -38/3, -5/72, -4, 1, 0, 1] θ = 0 ∧
      (1.9607713926898911079562381813641 : ℝ) ≤ θ ∧
      θ ≤ (1.9607713926898911079562381813642 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedTriangularBicupola
