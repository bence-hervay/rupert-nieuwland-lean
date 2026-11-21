import Polyhedra.Other.HendecagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.HendecagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.HendecagonalTrapezohedron.Proof.Theta

/-!
# The hendecagonal trapezohedron: the result

The hendecagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Other.HendecagonalTrapezohedron

open Notation

/-- **The hendecagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hendecagonal trapezohedron.** The system `system` has exactly one root in
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
  [(1.0121297825852899164762378114886, 1.0121297825852899164762378114887),    -- ν
   (-0.8611277049370428232316608041227, -0.8611277049370428232316608041226),  -- R₁ 0 0
   (0.4482866607635954387004740404772, 0.4482866607635954387004740404773),    -- R₁ 0 1
   (-0.2397877093832926522958337771925, -0.2397877093832926522958337771924),  -- R₁ 0 2
   (0.45482471062492789954031679606, 0.4548247106249278995403167960601),      -- R₁ 1 0
   (0.8900550996377463608363105321563, 0.8900550996377463608363105321564),    -- R₁ 1 1
   (0.0306006897600690723706920079971, 0.0306006897600690723706920079972),    -- R₁ 1 2
   (0.2271421545966576225618434796803, 0.2271421545966576225618434796804),    -- R₁ 2 0
   (-0.0827102737890916410884732793063, -0.0827102737890916410884732793062),  -- R₁ 2 1
   (-0.9703429559773810141048207435744, -0.9703429559773810141048207435743),  -- R₁ 2 2
   (-0.6920793863276157624401514222727, -0.6920793863276157624401514222726),  -- R₂ 0 0
   (0.7218213927422702622774991502276, 0.7218213927422702622774991502277),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3399922708846964956568984981998, 0.3399922708846964956568984981999),    -- R₂ 1 0
   (0.3259831927342569317913937210454, 0.3259831927342569317913937210455),    -- R₂ 1 1
   (0.8821225616621805112486280177204, 0.8821225616621805112486280177205),    -- R₂ 1 2
   (0.6367349360283743155906424786748, 0.6367349360283743155906424786749),    -- R₂ 2 0
   (0.610498841140906283250731326755, 0.6104988411409062832507313267551),     -- R₂ 2 1
   (-0.4710199424722402788252306949265, -0.4710199424722402788252306949264),  -- R₂ 2 2
   (0, 0),                                                                    -- t 0
   (0, 0)]                                                                    -- t 1

/-- **The enclosure of the optimum of the hendecagonal trapezohedron.** At the root of `system`, the
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
    polyEval [4707057664/1771561, 0, -5048893440/14641, 0, 218992738304/14641, 0,
      -3981910376448/14641, 0, 2616853364736/1331, 0, -5156253202432/1331, 0, 329090251008/121, 0,
      -8273417472/11, 0, 765225184/11, 0, -16272, 0, 1] θ = 0 ∧
      (0.2814694874282152238043849676342 : ℝ) ≤ θ ∧
      θ ≤ (0.2814694874282152238043849676343 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.HendecagonalTrapezohedron
