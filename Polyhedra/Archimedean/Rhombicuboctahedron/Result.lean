import Polyhedra.Archimedean.Rhombicuboctahedron.Proof.Optimum
import Polyhedra.Archimedean.Rhombicuboctahedron.Proof.Enclosure

/-!
# The rhombicuboctahedron: the result

The rhombicuboctahedron is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Archimedean.Rhombicuboctahedron

open Notation

/-- **The rhombicuboctahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the rhombicuboctahedron.** The system `system` has exactly one root in its box;
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
  [(1.0128199002645513282515623763636, 1.0128199002645513282515623763637),    -- ν
   (0.9873298359838769584379820102323, 0.9873298359838769584379820102324),    -- R₁ 0 0
   (0.1586814260587880649584684923425, 0.1586814260587880649584684923426),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.1586814260587880649584684923426, -0.1586814260587880649584684923425),  -- R₁ 1 0
   (0.9873298359838769584379820102323, 0.9873298359838769584379820102324),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0.8451461819943402077697935486315, 0.8451461819943402077697935486316),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.5345352477249648871732291715548, 0.5345352477249648871732291715549),    -- R₂ 0 2
   (-0.1640659021724654122936340434702, -0.1640659021724654122936340434701),  -- R₂ 1 0
   (0.951731489611588533619234603986, 0.9517314896115885336192346039861),     -- R₂ 1 1
   (0.2594022964933844918160469107019, 0.259402296493384491816046910702),     -- R₂ 1 2
   (-0.5087340275671803228659999856466, -0.5087340275671803228659999856465),  -- R₂ 2 0
   (-0.306931868142926382430921277563, -0.3069318681429263824309212775629),   -- R₂ 2 1
   (0.8043522347290201096531282865522, 0.8043522347290201096531282865523),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the rhombicuboctahedron.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Archimedean.Rhombicuboctahedron
