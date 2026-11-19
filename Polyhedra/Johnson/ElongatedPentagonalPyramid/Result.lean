import Polyhedra.Johnson.ElongatedPentagonalPyramid.Proof.Optimum
import Polyhedra.Johnson.ElongatedPentagonalPyramid.Proof.Enclosure
import Polyhedra.Johnson.ElongatedPentagonalPyramid.Proof.Theta

/-!
# The elongated pentagonal pyramid: the result

The elongated pentagonal pyramid is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedPentagonalPyramid

open Notation

/-- **The elongated pentagonal pyramid is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated pentagonal pyramid.** The system `system` has exactly one root in
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
  [(1.0134665071096778497700703802829, 1.013466507109677849770070380283),     -- ν
   (0.9965019067725410960940784311236, 0.9965019067725410960940784311237),    -- R₁ 0 0
   (0.083570029308896463740646815367, 0.0835700293088964637406468153671),     -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0835700293088964637406468153671, -0.083570029308896463740646815367),   -- R₁ 1 0
   (0.9965019067725410960940784311236, 0.9965019067725410960940784311237),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0.8324644394106116225927335701656, 0.8324644394106116225927335701657),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.5540784755941852418840694360036, 0.5540784755941852418840694360037),    -- R₂ 0 2
   (-0.2852960111734791915988607984006, -0.2852960111734791915988607984005),  -- R₂ 1 0
   (0.8572491608707259115474391448605, 0.8572491608707259115474391448606),    -- R₂ 1 1
   (0.4286374484280839442551611632536, 0.4286374484280839442551611632537),    -- R₂ 1 2
   (-0.474983308259646285220077799303, -0.4749833082596462852200777993029),   -- R₂ 2 0
   (-0.5149018121801828410353482273148, -0.5149018121801828410353482273147),  -- R₂ 2 1
   (0.7136294421394660663904906041153, 0.7136294421394660663904906041154),    -- R₂ 2 2
   (-0.0733026404352429683981576775892, -0.0733026404352429683981576775891),  -- t 0
   (-0.0283900235044480745547730421479, -0.0283900235044480745547730421478)]  -- t 1

/-- **The enclosure of the optimum of the elongated pentagonal pyramid.** At the root of `system`,
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
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ElongatedPentagonalPyramid
