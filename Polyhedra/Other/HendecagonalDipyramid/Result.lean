import Polyhedra.Other.HendecagonalDipyramid.Proof.Optimum
import Polyhedra.Other.HendecagonalDipyramid.Proof.Enclosure
import Polyhedra.Other.HendecagonalDipyramid.Proof.Theta

/-!
# The hendecagonal dipyramid: the result

The hendecagonal dipyramid is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Other.HendecagonalDipyramid

open Notation

/-- **The hendecagonal dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hendecagonal dipyramid.** The system `system` has exactly one root in its
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
  [(1.0068873712219456120897140497581, 1.0068873712219456120897140497582),    -- ν
   (-0.9096319953545183714117153830791, -0.909631995354518371411715383079),   -- R₁ 0 0
   (-0.4154150130018864255292741492297, -0.4154150130018864255292741492296),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.3984299423922250892657897580344, 0.3984299423922250892657897580345),    -- R₁ 1 0
   (-0.872439878588547116078162457836, -0.8724398785885471160781624578359),   -- R₁ 1 1
   (0.2830233899410601082566059337975, 0.2830233899410601082566059337976),    -- R₁ 1 2
   (-0.1175721652122034566533658895623, -0.1175721652122034566533658895622),  -- R₁ 2 0
   (0.2574471309240864299616999264912, 0.2574471309240864299616999264913),    -- R₁ 2 1
   (0.959113007286560907232752048921, 0.9591130072865609072327520489211),     -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 0 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 2
   (0.7529233720294046572000117849444, 0.7529233720294046572000117849445),    -- R₂ 1 0
   (-0.6581081946396585545984695614835, -0.6581081946396585545984695614834),  -- R₂ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 1 2
   (0.6581081946396585545984695614834, 0.6581081946396585545984695614835),    -- R₂ 2 0
   (0.7529233720294046572000117849444, 0.7529233720294046572000117849445),    -- R₂ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (-0.0054825319768966417785836229772, -0.0054825319768966417785836229771)]  -- t 1

/-- **The enclosure of the optimum of the hendecagonal dipyramid.** At the root of `system`, the
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
    polyEval [-11/1024, 0, 55/256, 0, -77/64, 0, 11/4, 0, -11/4, 0, 1] θ = 0 ∧
      (0.2817325568414296977114179153466 : ℝ) ≤ θ ∧
      θ ≤ (0.2817325568414296977114179153467 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.HendecagonalDipyramid
