import Polyhedra.Johnson.PentagonalGyrobicupola.Proof.Optimum
import Polyhedra.Johnson.PentagonalGyrobicupola.Proof.Enclosure

/-!
# The pentagonal gyrobicupola: the result

The pentagonal gyrobicupola is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.PentagonalGyrobicupola

open Notation

/-- **The pentagonal gyrobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal gyrobicupola.** The system `system` has exactly one root in its
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
  [(1.0514622242382672120513381696957, 1.0514622242382672120513381696958),    -- ν
   (0.8170571098834485655282419617167, 0.8170571098834485655282419617168),    -- R₁ 0 0
   (-0.1413522818005695007187471801005, -0.1413522818005695007187471801004),  -- R₁ 0 1
   (-0.5589608319181932131509867396987, -0.5589608319181932131509867396986),  -- R₁ 0 2
   (0.2870847944230175636525874350592, 0.2870847944230175636525874350593),    -- R₁ 1 0
   (0.9404935032296853141080272475068, 0.9404935032296853141080272475069),    -- R₁ 1 1
   (0.1818083914285796744090393067489, 0.181808391428579674409039306749),     -- R₁ 1 2
   (0.4999999999999999999999999999999, 0.5000000000000000000000000000001),    -- R₁ 2 0
   (-0.3090169943749474241022934171829, -0.3090169943749474241022934171828),  -- R₁ 2 1
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₁ 2 2
   (0.5377360347984818682787153369081, 0.5377360347984818682787153369082),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.843113252700493314469645080757, -0.8431132527004933144696450807569),   -- R₂ 0 2
   (0.0367461323683608762568918346055, 0.0367461323683608762568918346056),    -- R₂ 1 0
   (0.9990497719831192801157151688084, 0.9990497719831192801157151688085),    -- R₂ 1 1
   (0.023436613587382367431797589767, 0.0234366135873823674317975897671),     -- R₂ 1 2
   (0.8423121028663738714588579397085, 0.8423121028663738714588579397086),    -- R₂ 2 0
   (-0.0435838628448348380548560803886, -0.0435838628448348380548560803885),  -- R₂ 2 1
   (0.5372250629525300050748653769885, 0.5372250629525300050748653769886),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the pentagonal gyrobicupola.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.PentagonalGyrobicupola
