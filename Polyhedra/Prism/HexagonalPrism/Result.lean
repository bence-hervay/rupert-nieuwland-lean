import Polyhedra.Prism.HexagonalPrism.Proof.Optimum
import Polyhedra.Prism.HexagonalPrism.Proof.Enclosure

/-!
# The hexagonal prism: the result

The hexagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Prism.HexagonalPrism

open Notation

/-- **The hexagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hexagonal prism.** The system `system` has exactly one root in its box; at
the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and
the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.0833333333333333333333333333333, 1.0833333333333333333333333333334),    -- ν
   (0.77813471235593159833012615894, 0.7781347123559315983301261589401),      -- R₁ 0 0
   (0.4492562856444891217630983977953, 0.4492562856444891217630983977954),    -- R₁ 0 1
   (0.4389477864571921836734044999149, 0.438947786457192183673404499915),     -- R₁ 0 2
   (-0.3801399340068754107226217212115, -0.3801399340068754107226217212114),  -- R₁ 1 0
   (-0.2194738932285960918367022499575, -0.2194738932285960918367022499574),  -- R₁ 1 1
   (0.8985125712889782435261967955906, 0.8985125712889782435261967955907),    -- R₁ 1 2
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₁ 2 0
   (-0.866025403784438646763723170753, -0.8660254037844386467637231707529),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.8778955729143843673468089998298, 0.8778955729143843673468089998299),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.4788521306805732912800776362709, -0.4788521306805732912800776362708),  -- R₂ 0 2
   (0.1275994184079022357670338644625, 0.1275994184079022357670338644626),    -- R₂ 1 0
   (0.963843391241666752961181908904, 0.9638433912416667529611819089041),     -- R₂ 1 1
   (0.2339322670811540989062287515147, 0.2339322670811540989062287515148),    -- R₂ 1 2
   (0.4615384615384615384615384615384, 0.4615384615384615384615384615385),    -- R₂ 2 0
   (-0.2664693550105965066965302063856, -0.2664693550105965066965302063855),  -- R₂ 2 1
   (0.8461538461538461538461538461538, 0.8461538461538461538461538461539),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the hexagonal prism.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Prism.HexagonalPrism
