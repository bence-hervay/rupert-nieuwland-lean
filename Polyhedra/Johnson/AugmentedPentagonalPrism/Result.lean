import Polyhedra.Johnson.AugmentedPentagonalPrism.Proof.Optimum
import Polyhedra.Johnson.AugmentedPentagonalPrism.Proof.Enclosure
import Polyhedra.Johnson.AugmentedPentagonalPrism.Proof.Theta

/-!
# The augmented pentagonal prism: the result

The augmented pentagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.AugmentedPentagonalPrism

open Notation

/-- **The augmented pentagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented pentagonal prism.** The system `system` has exactly one root in
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
  [(1.0364493617279314063210351109198, 1.0364493617279314063210351109199),    -- ν
   (0.7730575867506428467273575478672, 0.7730575867506428467273575478673),    -- R₁ 0 0
   (-0.5824858394624249327234258250477, -0.5824858394624249327234258250476),  -- R₁ 0 1
   (-0.2511816362575625040002436906763, -0.2511816362575625040002436906762),  -- R₁ 0 2
   (0.5539769532703919456520532982793, 0.5539769532703919456520532982794),    -- R₁ 1 0
   (0.8128408496290981369998496607943, 0.8128408496290981369998496607944),    -- R₁ 1 1
   (-0.1799980233766466937433435221355, -0.1799980233766466937433435221354),  -- R₁ 1 2
   (0.3090169943749474241022934171828, 0.3090169943749474241022934171829),    -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9510565162951535721164393333793, 0.9510565162951535721164393333794),    -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (-0.2323253715488444679192325289053, -0.2323253715488444679192325289052),  -- R₂ 0 1
   (0.972638124758993481969164542915, 0.9726381247589934819691645429151),     -- R₂ 0 2
   (0.7389341498994988478208269415554, 0.7389341498994988478208269415555),    -- R₂ 1 0
   (0.6553418303417662543500826007654, 0.6553418303417662543500826007655),    -- R₂ 1 1
   (0.1565356429590673820991634007777, 0.1565356429590673820991634007778),    -- R₂ 1 2
   (-0.673777650350844575199165025549, -0.6737776503508445751991650255489),   -- R₂ 2 0
   (0.7187155258786295512627558128578, 0.7187155258786295512627558128579),    -- R₂ 2 1
   (0.1716731509255306028629870167295, 0.1716731509255306028629870167296),    -- R₂ 2 2
   (0.1384102092537129727168308438767, 0.1384102092537129727168308438768),    -- t 0
   (-0.129922204495608866824145563742, -0.1299222044956088668241455637419)]   -- t 1

/-- **The enclosure of the optimum of the augmented pentagonal prism.** At the root of `system`, the
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
    polyEval [1/256, 0, -11/32, 0, 79/16, 0, -9/2, 0, 1] θ = 0 ∧
      (1.6581632974817010965172836954842 : ℝ) ≤ θ ∧
      θ ≤ (1.6581632974817010965172836954843 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.AugmentedPentagonalPrism
