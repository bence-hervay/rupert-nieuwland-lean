import Polyhedra.Johnson.GyroelongatedTriangularCupola.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedTriangularCupola.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedTriangularCupola.Proof.Theta

/-!
# The gyroelongated triangular cupola: the result

The gyroelongated triangular cupola is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedTriangularCupola

open Notation

/-- **The gyroelongated triangular cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated triangular cupola.** The system `system` has exactly one root
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
  [(1.0010781256342917712378996281932, 1.0010781256342917712378996281933),    -- ν
   (0.4842247867195849910443918102791, 0.4842247867195849910443918102792),    -- R₁ 0 0
   (0.873889052304693031593265892474, 0.8738890523046930315932658924741),     -- R₁ 0 1
   (0.0429450834016877156035666983579, 0.042945083401687715603566698358),     -- R₁ 0 2
   (0.8053745719434686162951076191683, 0.8053745719434686162951076191684),    -- R₁ 1 0
   (-0.4643659491940374770972217740227, -0.4643659491940374770972217740226),  -- R₁ 1 1
   (0.3684237561504351452036653813759, 0.368423756150435145203665381376),     -- R₁ 1 2
   (0.3419037215258809094968533286573, 0.3419037215258809094968533286574),    -- R₁ 2 0
   (-0.143813036582662044219315023623, -0.1438130365826620442193150236229),   -- R₁ 2 1
   (-0.9286655241342960437949617021534, -0.9286655241342960437949617021533),  -- R₁ 2 2
   (-0.5008857017615828715891740965642, -0.5008857017615828715891740965641),  -- R₂ 0 0
   (0.8655134393935236043481341020434, 0.8655134393935236043481341020435),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4527590736933002640575733727574, 0.4527590736933002640575733727575),    -- R₂ 1 0
   (0.2620185152927272417585420418146, 0.2620185152927272417585420418147),    -- R₂ 1 1
   (0.8522649346489503209518100155964, 0.8522649346489503209518100155965),    -- R₂ 1 2
   (0.7376467548625096189697367327186, 0.7376467548625096189697367327187),    -- R₂ 2 0
   (0.4268873198784290467088297323528, 0.4268873198784290467088297323529),    -- R₂ 2 1
   (-0.5231103909958398433613793515599, -0.5231103909958398433613793515598),  -- R₂ 2 2
   (-0.0183917069632726120013875369788, -0.0183917069632726120013875369787),  -- t 0
   (0.2068172529303380750583823657393, 0.2068172529303380750583823657394)]    -- t 1

/-- **The enclosure of the optimum of the gyroelongated triangular cupola.** At the root of
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

end Nieuwland.Johnson.GyroelongatedTriangularCupola
