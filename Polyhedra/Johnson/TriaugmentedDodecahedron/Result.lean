import Polyhedra.Johnson.TriaugmentedDodecahedron.Proof.Optimum
import Polyhedra.Johnson.TriaugmentedDodecahedron.Proof.Enclosure

/-!
# The triaugmented dodecahedron: the result

The triaugmented dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.TriaugmentedDodecahedron

open Notation

/-- **The triaugmented dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triaugmented dodecahedron.** The system `system` has exactly one root in
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
  [(1.0062805812398542066352902036014, 1.0062805812398542066352902036015),    -- ν
   (0.7159237281288344612672267983913, 0.7159237281288344612672267983914),    -- R₁ 0 0
   (-0.4074392905157215097074892771252, -0.4074392905157215097074892771251),  -- R₁ 0 1
   (0.5669624679343035742152624119499, 0.56696246793430357421526241195),      -- R₁ 0 2
   (-0.4927526858676994723970577724783, -0.4927526858676994723970577724782),  -- R₁ 1 0
   (0.2804304381060024897213949932417, 0.2804304381060024897213949932418),    -- R₁ 1 1
   (0.8237436251369984298089728640846, 0.8237436251369984298089728640847),    -- R₁ 1 2
   (-0.4946190514651442386618299807486, -0.4946190514651442386618299807485),  -- R₁ 2 0
   (-0.8691098859912485168610201143082, -0.8691098859912485168610201143081),  -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9592098803345767611139967707937, 0.9592098803345767611139967707938),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.2826948982003865773516941803331, -0.282694898200386577351694180333),   -- R₂ 0 2
   (-0.0532155875733413943717510820065, -0.0532155875733413943717510820064),  -- R₂ 1 0
   (0.9821223129227837233356620494786, 0.9821223129227837233356620494787),    -- R₂ 1 1
   (-0.1805654000588864766830252087264, -0.1805654000588864766830252087263),  -- R₂ 1 2
   (0.2776409672720345553717614003005, 0.2776409672720345553717614003006),    -- R₂ 2 0
   (0.1882438908947689794103839047907, 0.1882438908947689794103839047908),    -- R₂ 2 1
   (0.9420614262525811270022457876557, 0.9420614262525811270022457876558),    -- R₂ 2 2
   (0.0203629824917848980503377618339, 0.020362982491784898050337761834),     -- t 0
   (-0.0140153397923113527111479097308, -0.0140153397923113527111479097307)]  -- t 1

/-- **The enclosure of the optimum of the triaugmented dodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.TriaugmentedDodecahedron
