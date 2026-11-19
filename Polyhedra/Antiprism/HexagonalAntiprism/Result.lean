import Polyhedra.Antiprism.HexagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.HexagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.HexagonalAntiprism.Proof.Theta

/-!
# The hexagonal antiprism: the result

The hexagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Antiprism.HexagonalAntiprism

open Notation

/-- **The hexagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hexagonal antiprism.** The system `system` has exactly one root in its box;
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
  [(1.0011000633015592737154920702493, 1.0011000633015592737154920702494),    -- ν
   (-0.4387497978849930734543323760704, -0.4387497978849930734543323760703),  -- R₁ 0 0
   (0.8978251317108449196691734263548, 0.8978251317108449196691734263549),    -- R₁ 0 1
   (-0.037531956041241706340549209268, -0.0375319560412417063405492092679),   -- R₁ 0 2
   (0.420243596096378221979828534083, 0.4202435960963782219798285340831),     -- R₁ 1 0
   (0.2419246276774708900085994837386, 0.2419246276774708900085994837387),    -- R₁ 1 1
   (0.874567204086170389156945460138, 0.8745672040861703891569454601381),     -- R₁ 1 2
   (0.7942883196899359229533874825172, 0.7942883196899359229533874825173),    -- R₁ 2 0
   (0.3679436198543481444681947470679, 0.367943619854348144468194747068),     -- R₁ 2 1
   (-0.4834496435127624453404635319548, -0.4834496435127624453404635319547),  -- R₁ 2 2
   (-0.5000400785353492563967593553816, -0.5000400785353492563967593553815),  -- R₂ 0 0
   (0.8660022631947111417789295378077, 0.8660022631947111417789295378078),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4789486896837112050034249127439, 0.478948689683711205003424912744),     -- R₂ 1 0
   (0.2765507096024737140060946887446, 0.2765507096024737140060946887447),    -- R₂ 1 1
   (0.8331433596138328227893100446754, 0.8331433596138328227893100446755),    -- R₂ 1 2
   (0.7215040349912243254551631512377, 0.7215040349912243254551631512378),    -- R₂ 2 0
   (0.4166050709725056926276900435951, 0.4166050709725056926276900435952),    -- R₂ 2 1
   (-0.5530570877688628256794982369768, -0.5530570877688628256794982369767),  -- R₂ 2 2
   (-0.0167367054609836169732731653485, -0.0167367054609836169732731653484),  -- t 0
   (0.0162272581783306790728661464578, 0.0162272581783306790728661464579)]    -- t 1

/-- **The enclosure of the optimum of the hexagonal antiprism.** At the root of `system`, the
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
    polyEval [-1/8, 0, 1/2, 0, 1] θ = 0 ∧
      (0.4277998385836760964846178831055 : ℝ) ≤ θ ∧
      θ ≤ (0.4277998385836760964846178831056 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.HexagonalAntiprism
