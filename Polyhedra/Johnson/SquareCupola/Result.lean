import Polyhedra.Johnson.SquareCupola.Proof.Optimum
import Polyhedra.Johnson.SquareCupola.Proof.Enclosure

/-!
# The square cupola: the result

The square cupola is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.SquareCupola

open Notation

/-- **The square cupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the square cupola.** The system `system` has exactly one root in its box; at
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
  [(1.0823922002923939687994464107327, 1.0823922002923939687994464107328),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 1 2
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (-0.3826834323650897717284599840304, -0.3826834323650897717284599840303),  -- R₂ 0 0
   (0.9238795325112867561281831893967, 0.9238795325112867561281831893968),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.5052864946091485445487813623216, -0.5052864946091485445487813623215),  -- R₂ 1 0
   (-0.2092965189510691057897009135376, -0.2092965189510691057897009135375),  -- R₂ 1 1
   (0.8371860758042764231588036541503, 0.8371860758042764231588036541504),    -- R₂ 1 2
   (0.7734590803390135784002412463156, 0.7734590803390135784002412463157),    -- R₂ 2 0
   (0.320377241017040735200723738947, 0.3203772410170407352007237389471),     -- R₂ 2 1
   (0.5469181606780271568004824926313, 0.5469181606780271568004824926314),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the square cupola.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.SquareCupola
