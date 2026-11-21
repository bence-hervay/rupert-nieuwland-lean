import Polyhedra.Other.PentagonalDipyramid.Proof.Optimum
import Polyhedra.Other.PentagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.PentagonalDipyramid.Proof.Theta

/-!
# The pentagonal dipyramid: the result

The pentagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Other.PentagonalDipyramid

open Notation

/-- **The pentagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the pentagonal dipyramid.** The system `system` has exactly one root in its
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
  [(1.0057245304306917556780835915994, 1.0057245304306917556780835915995),    -- ν
   (0.9563765667868628981928303719678, 0.9563765667868628981928303719679),    -- R₁ 0 0
   (0.1167411115557567370881076941813, 0.1167411115557567370881076941814),    -- R₁ 0 1
   (-0.2677972654335729605831879730753, -0.2677972654335729605831879730752),  -- R₁ 0 2
   (0.0522082122415116589015293956144, 0.0522082122415116589015293956145),    -- R₁ 1 0
   (0.8336276979703992402290209566007, 0.8336276979703992402290209566008),    -- R₁ 1 1
   (0.5498537657878848197002820297237, 0.5498537657878848197002820297238),    -- R₁ 1 2
   (0.2874337577173537954663124843842, 0.2874337577173537954663124843843),    -- R₁ 2 0
   (-0.5398484732304975068663318082852, -0.5398484732304975068663318082851),  -- R₁ 2 1
   (0.791167151033953364393882417542, 0.7911671510339533643938824175421),     -- R₁ 2 2
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (0, 0),                                                                    -- R₂ 2 0
   (0, 0),                                                                    -- R₂ 2 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 2 2
   (-0.0277165995033601361507970779317, -0.0277165995033601361507970779316),  -- t 0
   (0.0381486264533651989017658748874, 0.0381486264533651989017658748875)]    -- t 1

/-- **The enclosure of the optimum of the pentagonal dipyramid.** At the root of `system`, the
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
    polyEval [5/16, 0, -5/4, 0, 1] θ = 0 ∧
      (0.587785252292473129168705954639 : ℝ) ≤ θ ∧
      θ ≤ (0.5877852522924731291687059546391 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.PentagonalDipyramid
