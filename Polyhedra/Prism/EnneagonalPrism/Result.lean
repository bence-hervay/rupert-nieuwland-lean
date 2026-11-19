import Polyhedra.Prism.EnneagonalPrism.Proof.Optimum
import Polyhedra.Prism.EnneagonalPrism.Proof.Enclosure
import Polyhedra.Prism.EnneagonalPrism.Proof.Theta

/-!
# The enneagonal prism: the result

The enneagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Prism.EnneagonalPrism

open Notation

/-- **The enneagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the enneagonal prism.** The system `system` has exactly one root in its box; at
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
  [(1.005458714564326396569064680313, 1.0054587145643263965690646803131),     -- ν
   (-0.7660444431189780352023926505555, -0.7660444431189780352023926505554),  -- R₁ 0 0
   (0.6427876096865393263226434099072, 0.6427876096865393263226434099073),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 2
   (0.6427876096865393263226434099072, 0.6427876096865393263226434099073),    -- R₁ 2 0
   (0.7660444431189780352023926505554, 0.7660444431189780352023926505555),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (-0.6427876096865393263226434099073, -0.6427876096865393263226434099072),  -- R₂ 0 0
   (0.7660444431189780352023926505554, 0.7660444431189780352023926505555),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.0797153174058391533654530014949, 0.079715317405839153365453001495),     -- R₂ 1 0
   (0.066889093434419443241712613066, 0.0668890934344194432417126130661),     -- R₂ 1 1
   (0.9945709212270424222426780507071, 0.9945709212270424222426780507072),    -- R₂ 1 2
   (0.7618855274936986829612902593548, 0.7618855274936986829612902593549),    -- R₂ 2 0
   (0.63929786511926999497424399293, 0.6392978651192699949742439929301),      -- R₂ 2 1
   (-0.1040609564130186963971621889196, -0.1040609564130186963971621889195),  -- R₂ 2 2
   (0.0443223748415354926953494196593, 0.0443223748415354926953494196594),    -- t 0
   (0.0235199291848032060244794517857, 0.0235199291848032060244794517858)]    -- t 1

/-- **The enclosure of the optimum of the enneagonal prism.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
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
    polyEval [-1/3, 0, 2, 0, -3, 0, 1] θ = 0 ∧
      (1.4619022000815436261163772066831 : ℝ) ≤ θ ∧
      θ ≤ (1.4619022000815436261163772066832 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Prism.EnneagonalPrism
