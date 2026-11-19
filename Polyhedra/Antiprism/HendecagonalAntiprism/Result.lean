import Polyhedra.Antiprism.HendecagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.HendecagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.HendecagonalAntiprism.Proof.Theta

/-!
# The hendecagonal antiprism: the result

The hendecagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Antiprism.HendecagonalAntiprism

open Notation

/-- **The hendecagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hendecagonal antiprism.** The system `system` has exactly one root in its
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
  [(1.0123169224029981551157319220912, 1.0123169224029981551157319220913),    -- ν
   (0.8469610801420117346692466318264, 0.8469610801420117346692466318265),    -- R₁ 0 0
   (-0.0092784836835659509441090709538, -0.0092784836835659509441090709537),  -- R₁ 0 1
   (-0.5315739256822239734580999885191, -0.531573925682223973458099988519),   -- R₁ 0 2
   (0.4456375291598748824238082318519, 0.445637529159874882423808231852),     -- R₁ 1 0
   (0.5576569504908236763559715860051, 0.5576569504908236763559715860052),    -- R₁ 1 1
   (0.7003041611853785743143882337879, 0.700304161185378574314388233788),     -- R₁ 1 2
   (0.2899381336232928838727099541594, 0.2899381336232928838727099541595),    -- R₁ 2 0
   (-0.8300196595923549758606388226552, -0.8300196595923549758606388226551),  -- R₁ 2 1
   (0.4764485736795029266808375291273, 0.4764485736795029266808375291274),    -- R₁ 2 2
   (0.9817089474232470141607164454277, 0.9817089474232470141607164454278),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.1903878739550931317023459103566, 0.1903878739550931317023459103567),    -- R₂ 0 2
   (-0.0301091924012933066217081994469, -0.0301091924012933066217081994468),  -- R₂ 1 0
   (0.9874156455809392795203767465323, 0.9874156455809392795203767465324),    -- R₂ 1 1
   (0.1552539190968099499969115446994, 0.1552539190968099499969115446995),    -- R₂ 1 2
   (-0.187991965472150779999829939825, -0.1879919654721507799998299398249),   -- R₂ 2 0
   (-0.158146586627650322725488472614, -0.1581465866276503227254884726139),   -- R₂ 2 1
   (0.9693547740925098270965964989713, 0.9693547740925098270965964989714),    -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the hendecagonal antiprism.** At the root of `system`, the
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
    polyEval [1/14641, 0, 2/1331, 0, -349/1331, 0, 694/121, 0, -5728/121, 0, 20792/121, 0, -3147/11,
      0, 2234/11, 0, -49, 0, -2, 0, 1] θ = 0 ∧
      (2.3946955751488308785654099743758 : ℝ) ≤ θ ∧
      θ ≤ (2.3946955751488308785654099743759 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.HendecagonalAntiprism
