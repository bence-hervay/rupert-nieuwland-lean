import Polyhedra.Other.HeptagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.HeptagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.HeptagonalTrapezohedron.Proof.Theta

/-!
# The heptagonal trapezohedron: the result

The heptagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Other.HeptagonalTrapezohedron

open Notation

/-- **The heptagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the heptagonal trapezohedron.** The system `system` has exactly one root in its
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
  [(1.0252098570656144387013651959998, 1.0252098570656144387013651959999),    -- ν
   (-0.0831848320818228238888295044207, -0.0831848320818228238888295044206),  -- R₁ 0 0
   (0.9285784404517129763810569748235, 0.9285784404517129763810569748236),    -- R₁ 0 1
   (0.3616937428817140571685195667304, 0.3616937428817140571685195667305),    -- R₁ 0 2
   (0.9954733594932049559964275159175, 0.9954733594932049559964275159176),    -- R₁ 1 0
   (0.0606875221357646028187065829243, 0.0606875221357646028187065829244),    -- R₁ 1 1
   (0.073142430888871964364860840019, 0.0731424308888719643648608400191),     -- R₁ 1 2
   (0.0459681873781343545997451041315, 0.0459681873781343545997451041316),    -- R₁ 2 0
   (0.3661408261656785239758451414709, 0.366140826165678523975845141471),     -- R₁ 2 1
   (-0.9294233810077531668771417804893, -0.9294233810077531668771417804892),  -- R₁ 2 2
   (-0.5548723048585576756942403956538, -0.5548723048585576756942403956537),  -- R₂ 0 0
   (0.831935529533960841765581453629, 0.8319355295339608417655814536291),     -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3559221904660237819795074232061, 0.3559221904660237819795074232062),    -- R₂ 1 0
   (0.2373878253340390456626486505538, 0.2373878253340390456626486505539),    -- R₂ 1 1
   (0.9038619445009526782565617324983, 0.9038619445009526782565617324984),    -- R₂ 1 2
   (0.7519548654239955921149434413812, 0.7519548654239955921149434413813),    -- R₂ 2 0
   (0.5015279604191813529984035523252, 0.5015279604191813529984035523253),    -- R₂ 2 1
   (-0.427824245786697718461687786454, -0.4278242457866977184616877864539),   -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the heptagonal trapezohedron.** At the root of `system`, the
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
    polyEval [64/2401, 0, -256/343, 0, -16/7, 0, 1248/49, 0, -232/7, 0, 8, 0, 1] θ = 0 ∧
      (0.523104455825618528925954386312 : ℝ) ≤ θ ∧
      θ ≤ (0.5231044558256185289259543863121 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.HeptagonalTrapezohedron
