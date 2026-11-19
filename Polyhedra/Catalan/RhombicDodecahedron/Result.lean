import Polyhedra.Catalan.RhombicDodecahedron.Proof.Optimum
import Polyhedra.Catalan.RhombicDodecahedron.Proof.Enclosure

/-!
# The rhombic dodecahedron: the result

The rhombic dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Catalan.RhombicDodecahedron

open Notation

/-- **The rhombic dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the rhombic dodecahedron.** The system `system` has exactly one root in its
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
  [(1.0272279454371652817271689835632, 1.0272279454371652817271689835633),    -- ν
   (0.78359109074327414361970315271, 0.7835910907432741436197031527101),      -- R₁ 0 0
   (-0.1930777759577660081137339059667, -0.1930777759577660081137339059666),  -- R₁ 0 1
   (-0.5905133147855081355059692467434, -0.5905133147855081355059692467433),  -- R₁ 0 2
   (-0.2294595153277208798058554277328, -0.2294595153277208798058554277327),  -- R₁ 1 0
   (0.7933395484266931345094247906565, 0.7933395484266931345094247906566),    -- R₁ 1 1
   (-0.5638800330989722547035693629238, -0.5638800330989722547035693629237),  -- R₁ 1 2
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 0
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 1
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 2
   (0.8983005508702236296012832981147, 0.8983005508702236296012832981148),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.4393815202147818699895724426493, -0.4393815202147818699895724426492),  -- R₂ 0 2
   (-0.0982665066643950192666983640861, -0.098266506664395019266698364086),   -- R₂ 1 0
   (0.9746701333867368047555881979486, 0.9746701333867368047555881979487),    -- R₂ 1 1
   (-0.2009025254989520888588386126045, -0.2009025254989520888588386126044),  -- R₂ 1 2
   (0.428252044915408638985242906318, 0.4282520449154086389852429063181),     -- R₂ 2 0
   (0.2236473364113256882858588112758, 0.2236473364113256882858588112759),    -- R₂ 2 1
   (0.8755467177380600155569605288697, 0.8755467177380600155569605288698),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the rhombic dodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.RhombicDodecahedron
