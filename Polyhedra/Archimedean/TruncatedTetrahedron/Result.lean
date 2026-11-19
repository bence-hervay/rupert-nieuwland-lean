import Polyhedra.Archimedean.TruncatedTetrahedron.Proof.Optimum
import Polyhedra.Archimedean.TruncatedTetrahedron.Proof.Enclosure

/-!
# The truncated tetrahedron: the result

The truncated tetrahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Archimedean.TruncatedTetrahedron

open Notation

/-- **The truncated tetrahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the truncated tetrahedron.** The system `system` has exactly one root in its
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
  [(1.0142557284164753191174322266246, 1.0142557284164753191174322266247),    -- ν
   (-0.9852806467170092406865346188604, -0.9852806467170092406865346188603),  -- R₁ 0 0
   (-0.1208760671202368905537506103791, -0.120876067120236890553750610379),   -- R₁ 0 1
   (-0.1208760671202368905537506103791, -0.120876067120236890553750610379),   -- R₁ 0 2
   (-0.1709445734877595574350047876535, -0.1709445734877595574350047876534),  -- R₁ 1 0
   (0.6966986266654642876142307192501, 0.6966986266654642876142307192502),    -- R₁ 1 1
   (0.6966986266654642876142307192501, 0.6966986266654642876142307192502),    -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 2 1
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 2
   (0.2108118546331797384426884105318, 0.2108118546331797384426884105319),    -- R₂ 0 0
   (0.9775266553634837299215572611525, 0.9775266553634837299215572611526),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.4941119722296927759792669681942, -0.4941119722296927759792669681941),  -- R₂ 1 0
   (0.1065594075523875370713247157953, 0.1065594075523875370713247157954),    -- R₂ 1 1
   (0.8628432369563821810917463916147, 0.8628432369563821810917463916148),    -- R₂ 1 2
   (0.8434522635249741324907149540894, 0.8434522635249741324907149540895),    -- R₂ 2 0
   (-0.1818975830404710998215994888721, -0.181897583040471099821599488872),   -- R₂ 2 1
   (0.5054716099234778102647511096655, 0.5054716099234778102647511096656),    -- R₂ 2 2
   (-0.1454122006317826607365257457364, -0.1454122006317826607365257457363),  -- t 0
   (-0.1682649486788382218967337715357, -0.1682649486788382218967337715356)]  -- t 1

/-- **The enclosure of the optimum of the truncated tetrahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.TruncatedTetrahedron
