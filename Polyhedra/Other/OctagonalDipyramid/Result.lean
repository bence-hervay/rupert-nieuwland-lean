import Polyhedra.Other.OctagonalDipyramid.Proof.Optimum
import Polyhedra.Other.OctagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.OctagonalDipyramid.Proof.Theta

/-!
# The octagonal dipyramid: the result

The octagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.OctagonalDipyramid

open Notation

/-- **The octagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the octagonal dipyramid.** The system `system` has exactly one root in its box;
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
  [(1.0596191012184288965645352532419, 1.059619101218428896564535253242),     -- ν
   (0.8503662204526002830890700063712, 0.8503662204526002830890700063713),    -- R₁ 0 0
   (0.3522332214954162419396025453359, 0.352233221495416241939602545336),     -- R₁ 0 1
   (0.3909079799494001855323951642946, 0.3909079799494001855323951642947),    -- R₁ 0 2
   (0.3826834323650897717284599840303, 0.3826834323650897717284599840304),    -- R₁ 1 0
   (-0.9238795325112867561281831893968, -0.9238795325112867561281831893967),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (0.3611518817705833001033321118648, 0.3611518817705833001033321118649),    -- R₁ 2 0
   (0.1495940075059401545075336548071, 0.1495940075059401545075336548072),    -- R₁ 2 1
   (-0.9204297644100169702645220555898, -0.9204297644100169702645220555897),  -- R₁ 2 2
   (-0.3826834323650897717284599840304, -0.3826834323650897717284599840303),  -- R₂ 0 0
   (0.9238795325112867561281831893967, 0.9238795325112867561281831893968),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.9238795325112867561281831893967, 0.9238795325112867561281831893968),    -- R₂ 2 0
   (0.3826834323650897717284599840303, 0.3826834323650897717284599840304),    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the octagonal dipyramid.** At the root of `system`, the
Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
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
    polyEval [1/8, 0, -1, 0, 1] θ = 0 ∧
      (0.3826834323650897717284599840303 : ℝ) ≤ θ ∧
      θ ≤ (0.3826834323650897717284599840304 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.OctagonalDipyramid
