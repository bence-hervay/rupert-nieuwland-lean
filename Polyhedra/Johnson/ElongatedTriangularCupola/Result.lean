import Polyhedra.Johnson.ElongatedTriangularCupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedTriangularCupola.Proof.Enclosure

/-!
# The elongated triangular cupola: the result

The elongated triangular cupola is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedTriangularCupola

open Notation

/-- **The elongated triangular cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated triangular cupola.** The system `system` has exactly one root in
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
  [(1.0411670252320803380939839198884, 1.0411670252320803380939839198885),    -- ν
   (0.6732973984297649831945730043823, 0.6732973984297649831945730043824),    -- R₁ 0 0
   (-0.7366523991362491307692038389836, -0.7366523991362491307692038389835),  -- R₁ 0 1
   (0.0633550007064841475746308346011, 0.0633550007064841475746308346012),    -- R₁ 0 2
   (0.4618844876528946307552193930622, 0.4618844876528946307552193930623),    -- R₁ 1 0
   (0.3521504075157019714825388105058, 0.3521504075157019714825388105059),    -- R₁ 1 1
   (-0.8140348951685966022377582035682, -0.8140348951685966022377582035681),  -- R₁ 1 2
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 0
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 1
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 2
   (0.9052756936466460029583728842986, 0.9052756936466460029583728842987),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4248245737861499151747221690928, 0.4248245737861499151747221690929),    -- R₂ 0 2
   (0.2791107486112656914364663076496, 0.2791107486112656914364663076497),    -- R₂ 1 0
   (0.7538885167673131940899208836068, 0.7538885167673131940899208836069),    -- R₂ 1 1
   (-0.594768269409220736978861630281, -0.5947682694092207369788616302809),   -- R₂ 1 2
   (-0.3202703678179465615443371421981, -0.320270367817946561544337142198),   -- R₂ 2 0
   (0.6570023624663617090575972446054, 0.6570023624663617090575972446055),    -- R₂ 2 1
   (0.6824769499487705675715959857163, 0.6824769499487705675715959857164),    -- R₂ 2 2
   (0.3304224723144217774789345665337, 0.3304224723144217774789345665338),    -- t 0
   (0.1088650026456166372778380394884, 0.1088650026456166372778380394885)]    -- t 1

/-- **The enclosure of the optimum of the elongated triangular cupola.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ElongatedTriangularCupola
