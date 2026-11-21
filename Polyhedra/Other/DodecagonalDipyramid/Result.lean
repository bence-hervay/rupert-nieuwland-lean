import Polyhedra.Other.DodecagonalDipyramid.Proof.Optimum
import Polyhedra.Other.DodecagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.DodecagonalDipyramid.Proof.Theta

/-!
# The dodecagonal dipyramid: the result

The dodecagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Other.DodecagonalDipyramid

open Notation

/-- **The dodecagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the dodecagonal dipyramid.** The system `system` has exactly one root in its
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
  [(1.0306908085885388809262239458457, 1.0306908085885388809262239458458),    -- ν
   (-0.682794019231518737675459813731, -0.6827940192315187376754598137309),   -- R₁ 0 0
   (-0.682794019231518737675459813731, -0.6827940192315187376754598137309),   -- R₁ 0 1
   (0.2599704879468760784974952649493, 0.2599704879468760784974952649494),    -- R₁ 0 2
   (0.7071067811865475244008443621048, 0.7071067811865475244008443621049),    -- R₁ 1 0
   (-0.7071067811865475244008443621049, -0.7071067811865475244008443621048),  -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (0.1838268949356116938160364737467, 0.1838268949356116938160364737468),    -- R₁ 2 0
   (0.1838268949356116938160364737467, 0.1838268949356116938160364737468),    -- R₁ 2 1
   (0.9656165623044496846044402958859, 0.965616562304449684604440295886),     -- R₁ 2 2
   (-0.2588190451025207623488988376241, -0.258819045102520762348898837624),   -- R₂ 0 0
   (0.9659258262890682867497431997288, 0.9659258262890682867497431997289),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0, 0),                                                                    -- R₂ 1 0
   (0, 0),                                                                    -- R₂ 1 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₂ 1 2
   (0.9659258262890682867497431997288, 0.9659258262890682867497431997289),    -- R₂ 2 0
   (0.258819045102520762348898837624, 0.2588190451025207623488988376241),     -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the dodecagonal dipyramid.** At the root of `system`, the
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
    polyEval [1/16, 0, -1, 0, 1] θ = 0 ∧
      (0.258819045102520762348898837624 : ℝ) ≤ θ ∧
      θ ≤ (0.2588190451025207623488988376241 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.DodecagonalDipyramid
