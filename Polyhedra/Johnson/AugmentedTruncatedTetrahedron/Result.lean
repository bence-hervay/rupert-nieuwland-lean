import Polyhedra.Johnson.AugmentedTruncatedTetrahedron.Proof.Optimum
import Polyhedra.Johnson.AugmentedTruncatedTetrahedron.Proof.Enclosure

/-!
# The augmented truncated tetrahedron: the result

The augmented truncated tetrahedron is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.AugmentedTruncatedTetrahedron

open Notation

/-- **The augmented truncated tetrahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented truncated tetrahedron.** The system `system` has exactly one root
in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater
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
  [(1.0699200246015727659196390432894, 1.0699200246015727659196390432895),    -- ν
   (-0.4131374809680872767757912410468, -0.4131374809680872767757912410467),  -- R₁ 0 0
   (-0.6439399901463424888107775927296, -0.6439399901463424888107775927295),  -- R₁ 0 1
   (0.6439399901463424888107775927295, 0.6439399901463424888107775927296),    -- R₁ 0 2
   (-0.9106686674193547344220435304592, -0.9106686674193547344220435304591),  -- R₁ 1 0
   (0.2921323143548627323197834377032, 0.2921323143548627323197834377033),    -- R₁ 1 1
   (-0.2921323143548627323197834377033, -0.2921323143548627323197834377032),  -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 1
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 2 2
   (0.0602028991539043782634239309698, 0.0602028991539043782634239309699),    -- R₂ 0 0
   (0.9981861604597936016686516038226, 0.9981861604597936016686516038227),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.1327037523170230998800270938613, 0.1327037523170230998800270938614),    -- R₂ 1 0
   (-0.0080036679875489466070775891913, -0.0080036679875489466070775891912),  -- R₂ 1 1
   (0.9911234309710003372144140660457, 0.9911234309710003372144140660458),    -- R₂ 1 2
   (0.9893256921026801099871085165612, 0.9893256921026801099871085165613),    -- R₂ 2 0
   (-0.0596685039638188406561886845619, -0.0596685039638188406561886845618),  -- R₂ 2 1
   (-0.1329448930206524689689223018743, -0.1329448930206524689689223018742),  -- R₂ 2 2
   (0.2635256419729764331875518466442, 0.2635256419729764331875518466443),    -- t 0
   (0.8719479784539912877638393978539, 0.871947978453991287763839397854)]     -- t 1

/-- **The enclosure of the optimum of the augmented truncated tetrahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.AugmentedTruncatedTetrahedron
