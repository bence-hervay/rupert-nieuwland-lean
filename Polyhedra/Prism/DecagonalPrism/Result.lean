import Polyhedra.Prism.DecagonalPrism.Proof.Optimum
import Polyhedra.Prism.DecagonalPrism.Proof.Enclosure
import Polyhedra.Prism.DecagonalPrism.Proof.Theta

/-!
# The decagonal prism: the result

The decagonal prism is Rupert, and its Nieuwland number and an optimal pose are the one root of the
polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Prism.DecagonalPrism

open Notation

/-- **The decagonal prism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the decagonal prism.** The system `system` has exactly one root in its box; at
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
  [(1.0420303365640580658431134173294, 1.0420303365640580658431134173295),    -- ν
   (0.3570385783035497844615238111759, 0.357038578303549784461523811176),     -- R₁ 0 0
   (0.4914214440877373253684937137922, 0.4914214440877373253684937137923),    -- R₁ 0 1
   (-0.7943729715276715070775353271209, -0.7943729715276715070775353271208),  -- R₁ 0 2
   (0.4669207174837139704705303320507, 0.4669207174837139704705303320508),    -- R₁ 1 0
   (0.6426612338380124899261022573482, 0.6426612338380124899261022573483),    -- R₁ 1 1
   (0.6074303104935554606251927546887, 0.6074303104935554606251927546888),    -- R₁ 1 2
   (0.8090169943749474241022934171828, 0.8090169943749474241022934171829),    -- R₁ 2 0
   (-0.5877852522924731291687059546391, -0.587785252292473129168705954639),   -- R₁ 2 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 2
   (0.9818989922967069455493383751513, 0.9818989922967069455493383751514),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.1894053033225612571664129968471, 0.1894053033225612571664129968472),    -- R₂ 0 2
   (-0.0477799240880884767585608451776, -0.0477799240880884767585608451775),  -- R₂ 1 0
   (0.9676587456014170107109116245855, 0.9676587456014170107109116245856),    -- R₂ 1 1
   (0.2476966509971998340998682913001, 0.2476966509971998340998682913002),    -- R₂ 1 2
   (-0.1832796982233655276323217453978, -0.1832796982233655276323217453977),  -- R₂ 2 0
   (-0.2522628630240529776778408175518, -0.2522628630240529776778408175517),  -- R₂ 2 1
   (0.9501431471931268673301980395103, 0.9501431471931268673301980395104),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the decagonal prism.** At the root of `system`, the Nieuwland
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
    polyEval [1/16, 2, -9/4, -2, 1] θ = 0 ∧
      (2.569090505045048420321026167745 : ℝ) ≤ θ ∧
      θ ≤ (2.5690905050450484203210261677451 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Prism.DecagonalPrism
