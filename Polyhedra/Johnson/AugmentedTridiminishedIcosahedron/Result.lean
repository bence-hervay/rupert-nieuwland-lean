import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Proof.Optimum
import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Proof.Enclosure
import Polyhedra.Johnson.AugmentedTridiminishedIcosahedron.Proof.Theta

/-!
# The augmented tridiminished icosahedron: the result

The augmented tridiminished icosahedron is Rupert, and its Nieuwland number and an optimal pose are
the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.AugmentedTridiminishedIcosahedron

open Notation

/-- **The augmented tridiminished icosahedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the augmented tridiminished icosahedron.** The system `system` has exactly one
root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
greater than `1`, and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with
which the polyhedron scaled by `ν polyhedron` fits weakly through itself; no larger copy fits
through it (`Polyhedron.IsOptimum`, `Definitions/Optimum.lean`). -/
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
  [(1.0235021554824507676484935052492, 1.0235021554824507676484935052493),    -- ν
   (0.9098619662836295624159759649045, 0.9098619662836295624159759649046),    -- R₁ 0 0
   (-0.1913820912883023924095885718849, -0.1913820912883023924095885718848),  -- R₁ 0 1
   (-0.3681359768408994156265045303613, -0.3681359768408994156265045303612),  -- R₁ 0 2
   (-0.1578958088488490997331681229786, -0.1578958088488490997331681229785),  -- R₁ 1 0
   (0.6607941072226526323303862757468, 0.6607941072226526323303862757469),    -- R₁ 1 1
   (-0.7337711233128387170690122414723, -0.7337711233128387170690122414722),  -- R₁ 1 2
   (0.3836927362596991458754698681716, 0.3836927362596991458754698681717),    -- R₁ 2 0
   (0.7257575648892220439698914785246, 0.7257575648892220439698914785247),    -- R₁ 2 1
   (0.5710129956030874841728453491483, 0.5710129956030874841728453491484),    -- R₁ 2 2
   (0.9996798089422715523574026798594, 0.9996798089422715523574026798595),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (-0.0253037466226534528801878281803, -0.0253037466226534528801878281802),  -- R₂ 0 2
   (0.0100967221069348935860106501651, 0.0100967221069348935860106501652),    -- R₂ 1 0
   (0.9169418592290382373102951555434, 0.9169418592290382373102951555435),    -- R₂ 1 1
   (0.3988930721337360566269443967285, 0.3988930721337360566269443967286),    -- R₂ 1 2
   (0.0232020644736363541205272125445, 0.0232020644736363541205272125446),    -- R₂ 2 0
   (-0.3990208350369622299840619599213, -0.3990208350369622299840619599212),  -- R₂ 2 1
   (0.9166482626452562022162431586185, 0.9166482626452562022162431586186),    -- R₂ 2 2
   (0.042575621147058590690485628382, 0.0425756211470585906904856283821),     -- t 0
   (-0.018602153963621090390228658873, -0.0186021539636210903902286588729)]   -- t 1

/-- **The enclosure of the optimum of the augmented tridiminished icosahedron.** At the root of
`system`, the Nieuwland number and the entries of the optimal pose lie in the intervals of
`enclosure`, and no interval is wider than `2 ^ -100` (`PolynomialSystem.EnclosedBy`,
`Definitions/Optimum.lean`). -/
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
    polyEval [-31/144, 19/18, -1/18, -2, 1] θ = 0 ∧
      (1.7167605132909615817369541309803 : ℝ) ≤ θ ∧
      θ ≤ (1.7167605132909615817369541309804 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.AugmentedTridiminishedIcosahedron
