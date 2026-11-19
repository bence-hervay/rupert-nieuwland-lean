import Polyhedra.Johnson.TriaugmentedTriangularPrism.Proof.Optimum
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Proof.Enclosure
import Polyhedra.Johnson.TriaugmentedTriangularPrism.Proof.Theta

/-!
# The triaugmented triangular prism: the result

The triaugmented triangular prism is Rupert, and its Nieuwland number and an optimal pose are the
one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.TriaugmentedTriangularPrism

open Notation

/-- **The triaugmented triangular prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the triaugmented triangular prism.** The system `system` has exactly one root
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
  [(1.0081152528281092502574502058057, 1.0081152528281092502574502058058),    -- ν
   (0.6320459222028620128409116005812, 0.6320459222028620128409116005813),    -- R₁ 0 0
   (-0.2212330000202478037066901265317, -0.2212330000202478037066901265316),  -- R₁ 0 1
   (0.742680221851083587447247891649, 0.7426802218510835874472478916491),     -- R₁ 0 2
   (-0.6765559194477235697813265387753, -0.6765559194477235697813265387752),  -- R₁ 1 0
   (0.3097965427196330742649370891328, 0.3097965427196330742649370891329),    -- R₁ 1 1
   (0.6680555291135669779134699519354, 0.6680555291135669779134699519355),    -- R₁ 1 2
   (-0.3778756939616242060339640057212, -0.3778756939616242060339640057211),  -- R₁ 2 0
   (-0.9247064733314045503738955286911, -0.924706473331404550373895528691),   -- R₁ 2 1
   (0.0461291457976118241857278806005, 0.0461291457976118241857278806006),    -- R₁ 2 2
   (0.8428939450458800946386121895488, 0.8428939450458800946386121895489),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.5380797314571446177138081603964, 0.5380797314571446177138081603965),    -- R₂ 0 2
   (-0.175499824168857129815916975309, -0.1754998241688571298159169753089),   -- R₂ 1 0
   (0.9453147469839475277270612524144, 0.9453147469839475277270612524145),    -- R₂ 1 1
   (0.2749178801958422990458704120274, 0.2749178801958422990458704120275),    -- R₂ 1 2
   (-0.5086547051996010956666941383709, -0.5086547051996010956666941383708),  -- R₂ 2 0
   (-0.3261595148614788894191687682299, -0.3261595148614788894191687682298),  -- R₂ 2 1
   (0.7968000763953475133737587917516, 0.7968000763953475133737587917517),    -- R₂ 2 2
   (-0.0663624269123050667303898395253, -0.0663624269123050667303898395252),  -- t 0
   (-0.121664723052829639430121955195, -0.1216647230528296394301219551949)]   -- t 1

/-- **The enclosure of the optimum of the triaugmented triangular prism.** At the root of `system`,
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
    polyEval [1/256, 0, -5/8, 0, 1] θ = 0 ∧
      (0.7865660924854930855822837664288 : ℝ) ≤ θ ∧
      θ ≤ (0.7865660924854930855822837664289 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.TriaugmentedTriangularPrism
