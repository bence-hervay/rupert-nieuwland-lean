import Polyhedra.Antiprism.EnneagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.EnneagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.EnneagonalAntiprism.Proof.Theta

/-!
# The enneagonal antiprism: the result

The enneagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Antiprism.EnneagonalAntiprism

open Notation

/-- **The enneagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the enneagonal antiprism.** The system `system` has exactly one root in its
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
  [(1.0174700937839692077058927197732, 1.0174700937839692077058927197733),    -- ν
   (0.7780452468448142846097240344932, 0.7780452468448142846097240344933),    -- R₁ 0 0
   (-0.0181295867608511982600747913832, -0.0181295867608511982600747913831),  -- R₁ 0 1
   (-0.6279465836725865781197585720013, -0.6279465836725865781197585720012),  -- R₁ 0 2
   (0.5181449869664896981074576376845, 0.5181449869664896981074576376846),    -- R₁ 1 0
   (0.5837116144396116576964429601324, 0.5837116144396116576964429601325),    -- R₁ 1 1
   (0.6251452020529297513390812861983, 0.6251452020529297513390812861984),    -- R₁ 1 2
   (0.3552060899586157551147766119109, 0.355206089958615755114776611911),     -- R₁ 2 0
   (-0.8117586274578071352358593623062, -0.8117586274578071352358593623061),  -- R₁ 2 1
   (0.4635478016387618026339420531477, 0.4635478016387618026339420531478),    -- R₁ 2 2
   (0.9792663177514016325270151877916, 0.9792663177514016325270151877917),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.2025770937633643017763005353859, 0.202577093763364301776300535386),     -- R₂ 0 2
   (-0.0455526754586327468675036565062, -0.0455526754586327468675036565061),  -- R₂ 1 0
   (0.9743897260481163026258361127329, 0.974389726048116302625836112733),     -- R₂ 1 1
   (0.2202035774696617865987032673532, 0.2202035774696617865987032673533),    -- R₂ 1 2
   (-0.1973890388957081115945712061383, -0.1973890388957081115945712061382),  -- R₂ 2 0
   (-0.2248658750719567545076903867448, -0.2248658750719567545076903867447),  -- R₂ 2 1
   (0.9541870390819358473301656439359, 0.954187039081935847330165643936),     -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the enneagonal antiprism.** At the root of `system`, the
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
    polyEval [1/9, 0, -8, 0, 26, 0, -14, 0, 5, 0, -6, 0, 1] θ = 0 ∧
      (2.3234282873061610765105970184552 : ℝ) ≤ θ ∧
      θ ≤ (2.3234282873061610765105970184553 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.EnneagonalAntiprism
