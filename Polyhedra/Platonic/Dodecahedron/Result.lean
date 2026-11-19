import Polyhedra.Platonic.Dodecahedron.Proof.Optimum
import Polyhedra.Platonic.Dodecahedron.Proof.Enclosure

/-!
# The dodecahedron: the result

The dodecahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Platonic.Dodecahedron

open Notation

/-- **The dodecahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the dodecahedron.** The system `system` has exactly one root in its box; at the
root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and the
variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
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
  [(1.0108230607529004713654982401957, 1.0108230607529004713654982401958),    -- ν
   (-0.0013337614562898439822306372194, -0.0013337614562898439822306372193),  -- R₁ 0 0
   (-0.7554095125959067005911217499533, -0.7554095125959067005911217499532),  -- R₁ 0 1
   (0.6552516229357943310681692591419, 0.655251622935794331068169259142),     -- R₁ 0 2
   (0.8595171153488907318520412095162, 0.8595171153488907318520412095163),    -- R₁ 1 0
   (0.3340371269082527403068624019971, 0.3340371269082527403068624019972),    -- R₁ 1 1
   (0.3868456103786128233678767386349, 0.386845610378612823367876738635),     -- R₁ 1 2
   (-0.5111052235134164424552056375291, -0.511105223513416442455205637529),   -- R₁ 2 0
   (0.5637159445381109041691507342918, 0.5637159445381109041691507342919),    -- R₁ 2 1
   (0.6488418793287052391944257529017, 0.6488418793287052391944257529018),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.6530708174152284600707021984499, -0.6530708174152284600707021984498),  -- R₂ 0 1
   (0.7572968423548360019317405344928, 0.7572968423548360019317405344929),    -- R₂ 0 2
   (0.9935245336742180244051813023809, 0.993524533674218024405181302381),     -- R₂ 1 0
   (0.0860423895463104718070255487231, 0.0860423895463104718070255487232),    -- R₂ 1 1
   (0.0742004594904140557392038170914, 0.0742004594904140557392038170915),    -- R₂ 1 2
   (-0.1136177846440759241348852001032, -0.1136177846440759241348852001031),  -- R₂ 2 0
   (0.7523929921535462400515791693499, 0.75239299215354624005157916935),      -- R₂ 2 1
   (0.6488418793287052391944257529017, 0.6488418793287052391944257529018),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the dodecahedron.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Platonic.Dodecahedron
