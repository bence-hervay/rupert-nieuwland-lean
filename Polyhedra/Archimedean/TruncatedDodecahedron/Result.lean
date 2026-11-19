import Polyhedra.Archimedean.TruncatedDodecahedron.Proof.Optimum
import Polyhedra.Archimedean.TruncatedDodecahedron.Proof.Enclosure

/-!
# The truncated dodecahedron: the result

The truncated dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Archimedean.TruncatedDodecahedron

open Notation

/-- **The truncated dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the truncated dodecahedron.** The system `system` has exactly one root in its
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
  [(1.0016143617870262302537622347748, 1.0016143617870262302537622347749),    -- ν
   (0.9982582373791359864301753293349, 0.998258237379135986430175329335),     -- R₁ 0 0
   (0.0589907942746062109532895973363, 0.0589907942746062109532895973364),    -- R₁ 0 1
   (-0.0007600628603445532318325219209, -0.0007600628603445532318325219208),  -- R₁ 0 2
   (-0.0550583532285661376216286277811, -0.055058353228566137621628627781),   -- R₁ 1 0
   (0.936185459899843087392153500441, 0.9361854598998430873921535004411),     -- R₁ 1 1
   (0.3471676286923620005322583022631, 0.3471676286923620005322583022632),    -- R₁ 1 2
   (0.0211912539614584590040320306627, 0.0211912539614584590040320306628),    -- R₁ 2 0
   (-0.3465210972840908826322246135109, -0.3465210972840908826322246135108),  -- R₁ 2 1
   (0.9378027830479981005186799501901, 0.9378027830479981005186799501902),    -- R₁ 2 2
   (0.894167168706563618806405009234, 0.8941671687065636188064050092341),     -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4477332625652105774323680256327, 0.4477332625652105774323680256328),    -- R₂ 0 2
   (-0.0235749102992506556269608949306, -0.0235749102992506556269608949305),  -- R₂ 1 0
   (0.9986128203487150752754249664711, 0.9986128203487150752754249664712),    -- R₂ 1 1
   (0.047081404392468963887663115273, 0.0470814043924689638876631152731),     -- R₂ 1 2
   (-0.4471121760941767069823044110852, -0.4471121760941767069823044110851),  -- R₂ 2 0
   (-0.0526539175673084222960102411316, -0.0526539175673084222960102411315),  -- R₂ 2 1
   (0.8929267982052868194299920881182, 0.8929267982052868194299920881183),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the truncated dodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.TruncatedDodecahedron
