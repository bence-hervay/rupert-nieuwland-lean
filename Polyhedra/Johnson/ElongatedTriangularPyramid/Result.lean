import Polyhedra.Johnson.ElongatedTriangularPyramid.Proof.Optimum
import Polyhedra.Johnson.ElongatedTriangularPyramid.Proof.Enclosure
import Polyhedra.Johnson.ElongatedTriangularPyramid.Proof.Theta

/-!
# The elongated triangular pyramid: the result

The elongated triangular pyramid is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedTriangularPyramid

open Notation

/-- **The elongated triangular pyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated triangular pyramid.** The system `system` has exactly one root in
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
  [(1.1168043442846278538453780137791, 1.1168043442846278538453780137792),    -- ν
   (0.9980472690962761085003573702259, 0.998047269096276108500357370226),     -- R₁ 0 0
   (-0.0624631783490515688413675931235, -0.0624631783490515688413675931234),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.0624631783490515688413675931234, 0.0624631783490515688413675931235),    -- R₁ 1 0
   (0.9980472690962761085003573702259, 0.998047269096276108500357370226),     -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.0372868525382050589035972956608, 0.0372868525382050589035972956609),    -- R₂ 0 1
   (0.9993046035257688889480292730739, 0.999304603525768888948029273074),     -- R₂ 0 2
   (0.9998281659534473647472746223296, 0.9998281659534473647472746223297),    -- R₂ 1 0
   (-0.01852459992136198005686991121, -0.0185245999213619800568699112099),    -- R₂ 1 1
   (0.000691204686899310980540872272, 0.0006912046868993109805408722721),     -- R₂ 1 2
   (0.0185374908271242538255460313183, 0.0185374908271242538255460313184),    -- R₂ 2 0
   (0.9991328889720063792624613118965, 0.9991328889720063792624613118966),    -- R₂ 2 1
   (-0.037280445387450207729572437371, -0.0372804453874502077295724373709),   -- R₂ 2 2
   (0.026757942317187238003388843675, 0.0267579423171872380033888436751),     -- t 0
   (-0.1382684231056880760827010743798, -0.1382684231056880760827010743797)]  -- t 1

/-- **The enclosure of the optimum of the elongated triangular pyramid.** At the root of `system`,
the Nieuwland number and the entries of the optimal pose lie in the intervals of `enclosure`, and no
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
    polyEval [1/36, 1, 0, -2, 1] θ = 0 ∧
      (1.6051717155225389149870024151529 : ℝ) ≤ θ ∧
      θ ≤ (1.605171715522538914987002415153 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ElongatedTriangularPyramid
