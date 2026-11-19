import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.Optimum
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.Enclosure
import Polyhedra.Johnson.ElongatedTriangularDipyramidJ14.Proof.Theta

/-!
# The elongated triangular dipyramid j14: the result

The elongated triangular dipyramid j14 is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedTriangularDipyramidJ14

open Notation

/-- **The elongated triangular dipyramid j14 is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated triangular dipyramid j14.** The system `system` has exactly one
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
  [(1.1168043442846278538453780137791, 1.1168043442846278538453780137792),    -- ν
   (0.8952579132565419483578456842071, 0.8952579132565419483578456842072),    -- R₁ 0 0
   (-0.4455482788111093268647875682814, -0.4455482788111093268647875682813),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.4455482788111093268647875682814, -0.4455482788111093268647875682813),  -- R₁ 1 0
   (-0.8952579132565419483578456842072, -0.8952579132565419483578456842071),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 2
   (-0.4838488576337706514649014053541, -0.483848857633770651464901405354),   -- R₂ 0 0
   (0.8751515771376379916850190989201, 0.8751515771376379916850190989202),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.032626040577220630935764588412, 0.0326260405772206309357645884121),     -- R₂ 1 0
   (0.0180381009127959573144721857563, 0.0180381009127959573144721857564),    -- R₂ 1 1
   (0.999304842573933163330695269617, 0.9993048425739331633306952696171),     -- R₂ 1 2
   (0.8745432090198566585944468700874, 0.8745432090198566585944468700875),    -- R₂ 2 0
   (0.4835125065072925801620635814638, 0.4835125065072925801620635814639),    -- R₂ 2 1
   (-0.037280445387450207729572437371, -0.0372804453874502077295724373709),   -- R₂ 2 2
   (-0.1382868981110539534972594005919, -0.1382868981110539534972594005918),  -- t 0
   (-0.0266622976505491415775988542922, -0.0266622976505491415775988542921)]  -- t 1

/-- **The enclosure of the optimum of the elongated triangular dipyramid j14.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
theorem enclosedBy : system.EnclosedBy layout enclosure (1 / 2 ^ 100) :=
  Proof.enclosedBy

/-- **The polyhedron is full-dimensional**: its hull has an interior point (its points do not
lie in a plane). -/
theorem interior_nonempty : (interior polyhedron.hull).Nonempty :=
  Proof.fullDim

@[inherit_doc] local notation "θ" => theta

/-- **`θ` is a root of its polynomial**, and it lies between these two rationals, which are at most
`2 ^ -100` apart. -/
theorem theta_isRoot :
    polyEval [1/36, 1, 0, -2, 1] θ = 0 ∧
      (1.6051717155225389149870024151529 : ℝ) ≤ θ ∧
      θ ≤ (1.605171715522538914987002415153 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ElongatedTriangularDipyramidJ14
