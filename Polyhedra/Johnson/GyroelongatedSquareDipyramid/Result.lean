import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Proof.Optimum
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Proof.Enclosure
import Polyhedra.Johnson.GyroelongatedSquareDipyramid.Proof.Theta

/-!
# The gyroelongated square dipyramid: the result

The gyroelongated square dipyramid is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.GyroelongatedSquareDipyramid

open Notation

/-- **The gyroelongated square dipyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the gyroelongated square dipyramid.** The system `system` has exactly one root
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
  [(1.0124892567464779793019087326523, 1.0124892567464779793019087326524),    -- ν
   (-0.3826834323650897717284599840304, -0.3826834323650897717284599840303),  -- R₁ 0 0
   (0.9238795325112867561281831893967, 0.9238795325112867561281831893968),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.9215427470221982371605676083935, 0.9215427470221982371605676083936),    -- R₁ 1 0
   (0.3817155041231526610574888125383, 0.3817155041231526610574888125384),    -- R₁ 1 1
   (0.0710791060916509128851862076556, 0.0710791060916509128851862076557),    -- R₁ 1 2
   (0.0656685313072746000858297837135, 0.0656685313072746000858297837136),    -- R₁ 2 0
   (0.0272007962885953325064999011903, 0.0272007962885953325064999011904),    -- R₁ 2 1
   (-0.9974706816128541399765132949876, -0.9974706816128541399765132949875),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.9999999999999999999999999999999, 1),                                    -- R₂ 0 2
   (0.8445068022893244667658362987947, 0.8445068022893244667658362987948),    -- R₂ 1 0
   (0.5355448262163120137509806457698, 0.5355448262163120137509806457699),    -- R₂ 1 1
   (0, 0),                                                                    -- R₂ 1 2
   (-0.5355448262163120137509806457699, -0.5355448262163120137509806457698),  -- R₂ 2 0
   (0.8445068022893244667658362987947, 0.8445068022893244667658362987948),    -- R₂ 2 1
   (0, 0),                                                                    -- R₂ 2 2
   (-0.1464705890312995479117997816319, -0.1464705890312995479117997816318),  -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the gyroelongated square dipyramid.** At the root of `system`,
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
    polyEval [-1/32, 0, 0, 0, 1] θ = 0 ∧
      (0.4204482076268572715155627381166 : ℝ) ≤ θ ∧
      θ ≤ (0.4204482076268572715155627381167 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.GyroelongatedSquareDipyramid
