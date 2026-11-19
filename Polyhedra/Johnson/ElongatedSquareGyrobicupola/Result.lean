import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedSquareGyrobicupola.Proof.Enclosure

/-!
# The elongated square gyrobicupola: the result

The elongated square gyrobicupola is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedSquareGyrobicupola

open Notation

/-- **The elongated square gyrobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated square gyrobicupola.** The system `system` has exactly one root
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
  [(1.0179786987660720656945203564605, 1.0179786987660720656945203564606),    -- ν
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 0 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 1 0
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 2
   (0.3826834323650897717284599840303, 0.3826834323650897717284599840304),    -- R₂ 0 0
   (0.9238795325112867561281831893967, 0.9238795325112867561281831893968),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (-0.1533042709695521225375440779453, -0.1533042709695521225375440779452),  -- R₂ 1 0
   (0.0635007082053084426798289723638, 0.0635007082053084426798289723639),    -- R₂ 1 1
   (0.986136633819025309277190227228, 0.9861366338190253092771902272281),     -- R₂ 1 2
   (0.9110714522449750760356612457725, 0.9110714522449750760356612457726),    -- R₂ 2 0
   (-0.3773781518108202707831164776033, -0.3773781518108202707831164776032),  -- R₂ 2 1
   (0.1659353471689548991507750185922, 0.1659353471689548991507750185923),    -- R₂ 2 2
   (0.0637404524407027084762670913443, 0.0637404524407027084762670913444),    -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the elongated square gyrobicupola.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ElongatedSquareGyrobicupola
