import Polyhedra.Archimedean.Icosidodecahedron.Proof.Optimum
import Polyhedra.Archimedean.Icosidodecahedron.Proof.Enclosure

/-!
# The icosidodecahedron: the result

The icosidodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Archimedean.Icosidodecahedron

open Notation

/-- **The icosidodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the icosidodecahedron.** The system `system` has exactly one root in its box;
at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`,
and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
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
  [(1.0008854278875889930430121025324, 1.0008854278875889930430121025325),    -- ν
   (-0.6071232326046353275367768563467, -0.6071232326046353275367768563466),  -- R₁ 0 0
   (-0.535276453454217376466967572738, -0.5352764534542173764669675727379),   -- R₁ 0 1
   (0.5872652712439012646511439912247, 0.5872652712439012646511439912248),    -- R₁ 0 2
   (0.4055494716690904663214472000202, 0.4055494716690904663214472000203),    -- R₁ 1 0
   (0.4268238880840788771974043192876, 0.4268238880840788771974043192877),    -- R₁ 1 1
   (0.8083013018607054666491753079519, 0.808301301860705466649175307952),     -- R₁ 1 2
   (-0.6833235005914983576814189602811, -0.683323500591498357681418960281),   -- R₁ 2 0
   (0.72890361978677590315754183229, 0.7289036197867759031575418322901),      -- R₁ 2 1
   (-0.0420536157912227054414975532209, -0.0420536157912227054414975532208),  -- R₁ 2 2
   (-0.5257311121191336060256690848479, -0.5257311121191336060256690848478),  -- R₂ 0 0
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.850650808352039932181540497063, 0.8506508083520399321815404970631),     -- R₂ 2 0
   (0.5257311121191336060256690848478, 0.5257311121191336060256690848479),    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the icosidodecahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.Icosidodecahedron
