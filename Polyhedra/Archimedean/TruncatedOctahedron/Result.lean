import Polyhedra.Archimedean.TruncatedOctahedron.Proof.Optimum
import Polyhedra.Archimedean.TruncatedOctahedron.Proof.Enclosure

/-!
# The truncated octahedron: the result

The truncated octahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Archimedean.TruncatedOctahedron

open Notation

/-- **The truncated octahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the truncated octahedron.** The system `system` has exactly one root in its
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
  [(1.0146118723545764888576086083058, 1.0146118723545764888576086083059),    -- ν
   (-0.2357022603955158414669481207017, -0.2357022603955158414669481207016),  -- R₁ 0 0
   (0.2357022603955158414669481207016, 0.2357022603955158414669481207017),    -- R₁ 0 1
   (-0.9428090415820633658677924828065, -0.9428090415820633658677924828064),  -- R₁ 0 2
   (-0.6666666666666666666666666666667, -0.6666666666666666666666666666666),  -- R₁ 1 0
   (0.6666666666666666666666666666666, 0.6666666666666666666666666666667),    -- R₁ 1 1
   (0.3333333333333333333333333333333, 0.3333333333333333333333333333334),    -- R₁ 1 2
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 2 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₂ 0 1
   (0.8164965809277260327324280249019, 0.816496580927726032732428024902),     -- R₂ 0 2
   (0.8660254037844386467637231707529, 0.866025403784438646763723170753),     -- R₂ 1 0
   (0.4082482904638630163662140124509, 0.408248290463863016366214012451),     -- R₂ 1 1
   (-0.288675134594812882254574390251, -0.2886751345948128822545743902509),   -- R₂ 1 2
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₂ 2 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₂ 2 1
   (-0.5000000000000000000000000000001, -0.4999999999999999999999999999999),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the truncated octahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.TruncatedOctahedron
