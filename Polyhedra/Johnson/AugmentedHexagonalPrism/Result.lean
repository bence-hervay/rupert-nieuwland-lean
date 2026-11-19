import Polyhedra.Johnson.AugmentedHexagonalPrism.Proof.Optimum
import Polyhedra.Johnson.AugmentedHexagonalPrism.Proof.Enclosure
import Polyhedra.Johnson.AugmentedHexagonalPrism.Proof.Theta

/-!
# The augmented hexagonal prism: the result

The augmented hexagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.AugmentedHexagonalPrism

open Notation

/-- **The augmented hexagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented hexagonal prism.** The system `system` has exactly one root in
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
  [(1.1009395869622868468542573086508, 1.1009395869622868468542573086509),    -- ν
   (-0.5092876492513137503211541559338, -0.5092876492513137503211541559337),  -- R₁ 0 0
   (0.8088066026107607724763211629657, 0.8088066026107607724763211629658),    -- R₁ 0 1
   (0.2940373613901977021956647717681, 0.2940373613901977021956647717682),    -- R₁ 0 2
   (0.7004470646095041069659469315778, 0.7004470646095041069659469315779),    -- R₁ 1 0
   (0.5880747227803954043913295435363, 0.5880747227803954043913295435364),    -- R₁ 1 1
   (-0.4044033013053803862381605814829, -0.4044033013053803862381605814828),  -- R₁ 1 2
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.866025403784438646763723170753, -0.8660254037844386467637231707529),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.2904746245655934646229664991564, 0.2904746245655934646229664991565),    -- R₂ 0 1
   (0.9568826952576149110248626657311, 0.9568826952576149110248626657312),    -- R₂ 0 2
   (0.9056771414531322166853951409616, 0.9056771414531322166853951409617),    -- R₂ 1 0
   (-0.4056876994471306196757734792855, -0.4056876994471306196757734792854),  -- R₂ 1 1
   (0.1231519629018464004607527079845, 0.1231519629018464004607527079846),    -- R₂ 1 2
   (0.4239680594682612854216928489584, 0.4239680594682612854216928489585),    -- R₂ 2 0
   (0.8666267841468853079059454843241, 0.8666267841468853079059454843242),    -- R₂ 2 1
   (-0.2630762276412384665282782421244, -0.2630762276412384665282782421243),  -- R₂ 2 2
   (0.0319965028994514550126031179305, 0.0319965028994514550126031179306),    -- t 0
   (-0.012147768561587482202281166448, -0.0121477685615874822022811664479)]   -- t 1

/-- **The enclosure of the optimum of the augmented hexagonal prism.** At the root of `system`, the
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
    polyEval [25/4, 0, -7, 0, 1] θ = 0 ∧
      (2.4391575887554248179282907036107 : ℝ) ≤ θ ∧
      θ ≤ (2.4391575887554248179282907036108 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.AugmentedHexagonalPrism
