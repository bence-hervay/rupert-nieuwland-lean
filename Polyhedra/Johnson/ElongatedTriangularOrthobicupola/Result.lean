import Polyhedra.Johnson.ElongatedTriangularOrthobicupola.Proof.Optimum
import Polyhedra.Johnson.ElongatedTriangularOrthobicupola.Proof.Enclosure

/-!
# The elongated triangular orthobicupola: the result

The elongated triangular orthobicupola is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedTriangularOrthobicupola

open Notation

/-- **The elongated triangular orthobicupola is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated triangular orthobicupola.** The system `system` has exactly one
root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
greater than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with
which the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits
through it (`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
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
  [(1.1148068970409368655939344543668, 1.1148068970409368655939344543669),    -- ν
   (-0.3390764760000373914187666357661, -0.339076476000037391418766635766),   -- R₁ 0 0
   (0.8127880787054377982439613614996, 0.8127880787054377982439613614997),    -- R₁ 0 1
   (-0.4737116027054004068251947257337, -0.4737116027054004068251947257336),  -- R₁ 0 2
   (-0.7427609373749152228404609669903, -0.7427609373749152228404609669902),  -- R₁ 1 0
   (0.0777316266457207095188429773404, 0.0777316266457207095188429773405),    -- R₁ 1 1
   (0.6650293107291945133216179896497, 0.6650293107291945133216179896498),    -- R₁ 1 2
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 0
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 1
   (0.5773502691896257645091487805019, 0.577350269189625764509148780502),     -- R₁ 2 2
   (0.4472135954999579392818347337462, 0.4472135954999579392818347337463),    -- R₂ 0 0
   (0.8944271909999158785636694674925, 0.8944271909999158785636694674926),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3651483716701107423046465218672, 0.3651483716701107423046465218673),    -- R₂ 1 0
   (-0.1825741858350553711523232609337, -0.1825741858350553711523232609336),  -- R₂ 1 1
   (0.912870929175276855761616304668, 0.9128709291752768557616163046681),     -- R₂ 1 2
   (0.8164965809277260327324280249019, 0.816496580927726032732428024902),     -- R₂ 2 0
   (-0.408248290463863016366214012451, -0.4082482904638630163662140124509),   -- R₂ 2 1
   (-0.408248290463863016366214012451, -0.4082482904638630163662140124509),   -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the elongated triangular orthobicupola.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

end Nieuwland.Johnson.ElongatedTriangularOrthobicupola
