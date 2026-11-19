import Polyhedra.Catalan.DeltoidalIcositetrahedron.Proof.Optimum
import Polyhedra.Catalan.DeltoidalIcositetrahedron.Proof.Enclosure

/-!
# The deltoidal icositetrahedron: the result

The deltoidal icositetrahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Catalan.DeltoidalIcositetrahedron

open Notation

/-- **The deltoidal icositetrahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the deltoidal icositetrahedron.** The system `system` has exactly one root in
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
  [(1.0076364653751366191404626482203, 1.0076364653751366191404626482204),    -- ν
   (0.8245919599295941798359827750402, 0.8245919599295941798359827750403),    -- R₁ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 1
   (0.5657279378106322110329398572104, 0.5657279378106322110329398572105),    -- R₁ 0 2
   (-0.0695172336715623788708406344723, -0.0695172336715623788708406344722),  -- R₁ 1 0
   (0.9924214082781396643241984454764, 0.9924214082781396643241984454765),    -- R₁ 1 1
   (0.1013267122425642268066050748864, 0.1013267122425642268066050748865),    -- R₁ 1 2
   (-0.5614405167443154349649335642772, -0.5614405167443154349649335642771),  -- R₁ 2 0
   (-0.1228810334886308699298671285544, -0.1228810334886308699298671285543),  -- R₁ 2 1
   (0.8183427141281591677606814550666, 0.8183427141281591677606814550667),    -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0, 0),                                                                    -- R₂ 2 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the deltoidal icositetrahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Catalan.DeltoidalIcositetrahedron
