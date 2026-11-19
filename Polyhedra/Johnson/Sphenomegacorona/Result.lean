import Polyhedra.Johnson.Sphenomegacorona.Proof.Optimum
import Polyhedra.Johnson.Sphenomegacorona.Proof.Enclosure
import Polyhedra.Johnson.Sphenomegacorona.Proof.Theta

/-!
# The sphenomegacorona: the result

The sphenomegacorona is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Johnson.Sphenomegacorona

open Notation

/-- **The sphenomegacorona is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the sphenomegacorona.** The system `system` has exactly one root in its box; at
the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`, and
the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the polyhedron
scaled by `ν polyhedron` fits weakly through itself; no larger copy fits through it
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
  [(1.2610278840605754366766975482124, 1.2610278840605754366766975482125),    -- ν
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 0
   (0.9890900764842391637669685803133, 0.9890900764842391637669685803134),    -- R₁ 0 1
   (0.1473119838994842984753848242171, 0.1473119838994842984753848242172),    -- R₁ 0 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 0
   (0.1473119838994842984753848242171, 0.1473119838994842984753848242172),    -- R₁ 1 1
   (-0.9890900764842391637669685803134, -0.9890900764842391637669685803133),  -- R₁ 1 2
   (-1.0000000000000000000000000000001, -0.9999999999999999999999999999999),  -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.0739830716963196431189994427307, 0.0739830716963196431189994427308),    -- R₂ 0 1
   (0.9972594973738666918828186686429, 0.997259497373866691882818668643),     -- R₂ 0 2
   (0.9999422125138829872346148173344, 0.9999422125138829872346148173345),    -- R₂ 1 0
   (-0.0107209632075579636780378676153, -0.0107209632075579636780378676152),  -- R₂ 1 1
   (0.0007953494468862512836898951659, 0.000795349446886251283689895166),     -- R₂ 1 2
   (0.0107504247748855862047672210939, 0.010750424774885586204767221094),     -- R₂ 2 0
   (0.9972018682545071404330012704937, 0.9972018682545071404330012704938),    -- R₂ 2 1
   (-0.0739787964005910980875603019556, -0.0739787964005910980875603019555),  -- R₂ 2 2
   (-0.0322509789519509929712479885591, -0.032250978951950992971247988559),   -- t 0
   (0.280081867617935858774383202427, 0.2800818676179358587743832024271)]     -- t 1

/-- **The enclosure of the optimum of the sphenomegacorona.** At the root of `system`, the Nieuwland
number and the entries of the optimal pose lie in the intervals of `enclosure`, and no interval is
wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`, `Definitions/Optimum.lean`). -/
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
    polyEval [49/849346560000, 0, -1/147456000, 0, 42983/130056192000, 0, -1472929/162570240000, 0,
      5255653/32514048000, 0, -41173973/20321280000, 0, 188580733/10160640000, 0,
      -21411977/169344000, 0, 3266781419/5080320000, 0, -4752067/1960000, 0, 351820103/52920000, 0,
      -504078991/39690000, 0, 604136401/39690000, 0, -2618923/330750, 0, -599/175, 0, 3172/735, 0,
      1] θ = 0 ∧
      (0.1821041544594690311588087966257 : ℝ) ≤ θ ∧
      θ ≤ (0.1821041544594690311588087966258 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.Sphenomegacorona
