import Polyhedra.Archimedean.TruncatedCuboctahedron.Proof.Optimum
import Polyhedra.Archimedean.TruncatedCuboctahedron.Proof.Enclosure

/-!
# The truncated cuboctahedron: the result

The truncated cuboctahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Archimedean.TruncatedCuboctahedron

open Notation

/-- **The truncated cuboctahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the truncated cuboctahedron.** The system `system` has exactly one root in its
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
  [(1.0065959643043151078202917848908, 1.0065959643043151078202917848909),    -- ν
   (0.9999976150491379636652799447624, 0.9999976150491379636652799447625),    -- R₁ 0 0
   (-0.0021840091657504679786202236524, -0.0021840091657504679786202236523),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.0021840091657504679786202236523, 0.0021840091657504679786202236524),    -- R₁ 1 0
   (0.9999976150491379636652799447624, 0.9999976150491379636652799447625),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0.9314085370311852536327173363542, 0.9314085370311852536327173363543),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.3639754622847908521837047236056, 0.3639754622847908521837047236057),    -- R₂ 0 2
   (-0.040345822136303544800604199843, -0.0403458221363035448006041998429),   -- R₂ 1 0
   (0.9938374112608823907540673102631, 0.9938374112608823907540673102632),    -- R₂ 1 1
   (0.1032444410823821458269182363832, 0.1032444410823821458269182363833),    -- R₂ 1 2
   (-0.3617324311995994739874098949115, -0.3617324311995994739874098949114),  -- R₂ 2 0
   (-0.1108476430884649857601804748593, -0.1108476430884649857601804748592),  -- R₂ 2 1
   (0.9256686492693588646411619862328, 0.9256686492693588646411619862329),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the truncated cuboctahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.TruncatedCuboctahedron
