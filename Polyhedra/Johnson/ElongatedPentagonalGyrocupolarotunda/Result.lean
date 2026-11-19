import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof.Optimum
import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof.Enclosure
import Polyhedra.Johnson.ElongatedPentagonalGyrocupolarotunda.Proof.Theta

/-!
# The elongated pentagonal gyrocupolarotunda: the result

The elongated pentagonal gyrocupolarotunda is Rupert, and its Nieuwland number and an optimal pose
are the one root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to
within `2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedPentagonalGyrocupolarotunda

open Notation

/-- **The elongated pentagonal gyrocupolarotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated pentagonal gyrocupolarotunda.** The system `system` has exactly
one root in its box; at the root the first variable is the Nieuwland number `ν polyhedron`, which is
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
  [(1.0073424924958740888899169117366, 1.0073424924958740888899169117367),    -- ν
   (0.8663969748782287585131549752742, 0.8663969748782287585131549752743),    -- R₁ 0 0
   (-0.4993558670145509019496051094075, -0.4993558670145509019496051094074),  -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (0.4993558670145509019496051094074, 0.4993558670145509019496051094075),    -- R₁ 1 0
   (0.8663969748782287585131549752742, 0.8663969748782287585131549752743),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0.8813581170240951141645164326032, 0.8813581170240951141645164326033),    -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.4724488009887859394751826323403, 0.4724488009887859394751826323404),    -- R₂ 0 2
   (-0.0995440038046941183264552787462, -0.0995440038046941183264552787461),  -- R₂ 1 0
   (0.9775512083698164705175124552029, 0.977551208369816470517512455203),     -- R₂ 1 1
   (0.1857003670466019939815412380167, 0.1857003670466019939815412380168),    -- R₂ 1 2
   (-0.4618428962994586376692831329447, -0.4618428962994586376692831329446),  -- R₂ 2 0
   (-0.2106979710740273380999344314297, -0.2106979710740273380999344314296),  -- R₂ 2 1
   (0.8615726923034502920582325125458, 0.8615726923034502920582325125459),    -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the elongated pentagonal gyrocupolarotunda.** At the root of
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
    polyEval [1/80, 0, -1/4, 0, 1] θ = 0 ∧
      (0.2628655560595668030128345424239 : ℝ) ≤ θ ∧
      θ ≤ (0.262865556059566803012834542424 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.ElongatedPentagonalGyrocupolarotunda
