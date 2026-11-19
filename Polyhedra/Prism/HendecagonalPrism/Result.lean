import Polyhedra.Prism.HendecagonalPrism.Proof.Optimum
import Polyhedra.Prism.HendecagonalPrism.Proof.Enclosure
import Polyhedra.Prism.HendecagonalPrism.Proof.Theta

/-!
# The hendecagonal prism: the result

The hendecagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Prism.HendecagonalPrism

open Notation

/-- **The hendecagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hendecagonal prism.** The system `system` has exactly one root in its box;
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
  [(1.0043863728609251878269284170164, 1.0043863728609251878269284170165),    -- ν
   (-0.013421371235919244916977584089, -0.0134213712359192449169775840889),   -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.9999099293407119874714816492044, 0.9999099293407119874714816492045),    -- R₁ 0 2
   (0.9999099293407119874714816492044, 0.9999099293407119874714816492045),    -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.0134213712359192449169775840889, 0.013421371235919244916977584089),     -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.0943076027683520846189704714498, -0.0943076027683520846189704714497),  -- R₂ 0 1
   (0.9955431060783288404486562177415, 0.9955431060783288404486562177416),    -- R₂ 0 2
   (0.9899106037816515402784355622804, 0.9899106037816515402784355622805),    -- R₂ 1 0
   (0.1410618064560693378098191863854, 0.1410618064560693378098191863855),    -- R₂ 1 1
   (0.0133627572003883289092931080623, 0.0133627572003883289092931080624),    -- R₂ 1 2
   (-0.1416933185462394879652455476426, -0.1416933185462394879652455476425),  -- R₂ 2 0
   (0.9854986772286592699605237703226, 0.9854986772286592699605237703227),    -- R₂ 2 1
   (0.0933560959976195643653213452407, 0.0933560959976195643653213452408),    -- R₂ 2 2
   (0.0217808624902435357957097258959, 0.021780862490243535795709725896),     -- t 0
   (-0.0358131364719288788258916923441, -0.035813136471928878825891692344)]   -- t 1

/-- **The enclosure of the optimum of the hendecagonal prism.** At the root of `system`, the
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
    polyEval [-1/11, 0, 1, 0, -4, 0, 7, 0, -5, 0, 1] θ = 0 ∧
      (1.7747327664421116628568319611689 : ℝ) ≤ θ ∧
      θ ≤ (1.774732766442111662856831961169 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Prism.HendecagonalPrism
