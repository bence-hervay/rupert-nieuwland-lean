import Polyhedra.Johnson.SnubSquareAntiprism.Proof.Optimum
import Polyhedra.Johnson.SnubSquareAntiprism.Proof.Enclosure
import Polyhedra.Johnson.SnubSquareAntiprism.Proof.Theta

/-!
# The snub square antiprism: the result

The snub square antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.SnubSquareAntiprism

open Notation

/-- **The snub square antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the snub square antiprism.** The system `system` has exactly one root in its
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
  [(1.0295410610245774691637306850312, 1.0295410610245774691637306850313),    -- ν
   (-0.3506888879298134002769756754611, -0.350688887929813400276975675461),   -- R₁ 0 0
   (-0.5781119929166743889445146389708, -0.5781119929166743889445146389707),  -- R₁ 0 1
   (-0.7367522158286745175721156099417, -0.7367522158286745175721156099416),  -- R₁ 0 2
   (-0.3821133073905894146621434291562, -0.3821133073905894146621434291561),  -- R₁ 1 0
   (-0.6299152703685526017153415838538, -0.6299152703685526017153415838537),  -- R₁ 1 1
   (0.6761628298505754165903689515721, 0.6761628298505754165903689515722),    -- R₁ 1 2
   (-0.8549893123294440937533178949008, -0.8549893123294440937533178949007),  -- R₁ 2 0
   (0.5186456167774141111855733486655, 0.5186456167774141111855733486656),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9562386443472551916468879541984, 0.9562386443472551916468879541985),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.2925878586970477774043133731215, -0.2925878586970477774043133731214),  -- R₂ 0 2
   (0.0821629743510756180404608604306, 0.0821629743510756180404608604307),    -- R₂ 1 0
   (0.959762001382265557113183971057, 0.9597620013822655571131839710571),     -- R₂ 1 1
   (0.2685258764970195138898782714377, 0.2685258764970195138898782714378),    -- R₂ 1 2
   (0.2808147088432300884435469076335, 0.2808147088432300884435469076336),    -- R₂ 2 0
   (-0.2808147088432300884435469076336, -0.2808147088432300884435469076335),  -- R₂ 2 1
   (0.9177615150977860797072149626457, 0.9177615150977860797072149626458),    -- R₂ 2 2
   (-0.0864796565675468899574192658475, -0.0864796565675468899574192658474),  -- t 0
   (0.0793677006365680401510261070209, 0.079367700636568040151026107021)]     -- t 1

/-- **The enclosure of the optimum of the snub square antiprism.** At the root of `system`, the
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
    polyEval [-1/8192, 0, -7/512, 0, 11/16, 0, -187/32, 0, 355/32, 0, 9, 0, 1] θ = 0 ∧
      (0.1856070212821798475712036428074 : ℝ) ≤ θ ∧
      θ ≤ (0.1856070212821798475712036428075 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.SnubSquareAntiprism
