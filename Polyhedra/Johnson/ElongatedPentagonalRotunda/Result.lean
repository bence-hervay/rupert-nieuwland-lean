import Polyhedra.Johnson.ElongatedPentagonalRotunda.Proof.Optimum
import Polyhedra.Johnson.ElongatedPentagonalRotunda.Proof.Enclosure
import Polyhedra.Johnson.ElongatedPentagonalRotunda.Proof.Theta

/-!
# The elongated pentagonal rotunda: the result

The elongated pentagonal rotunda is Rupert, and its Nieuwland number and an optimal pose are the one
root of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within
`2 ^ -100`. -/

namespace Nieuwland.Johnson.ElongatedPentagonalRotunda

open Notation

/-- **The elongated pentagonal rotunda is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the elongated pentagonal rotunda.** The system `system` has exactly one root in
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
  [(1.0073424924958740888899169117366, 1.0073424924958740888899169117367),    -- ν
   (0.9997478092040767823306121398818, 0.9997478092040767823306121398819),    -- R₁ 0 0
   (0.0224570254408033067257642261576, 0.0224570254408033067257642261577),    -- R₁ 0 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 0 2
   (-0.0224570254408033067257642261577, -0.0224570254408033067257642261576),  -- R₁ 1 0
   (0.9997478092040767823306121398818, 0.9997478092040767823306121398819),    -- R₁ 1 1
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 1 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- R₁ 2 1
   (0.9999999999999999999999999999999, 1.0000000000000000000000000000001),    -- R₁ 2 2
   (0.929043056928916195378626179276, 0.9290430569289161953786261792761),     -- R₂ 0 0
   (0, 0),                                                                    -- R₂ 0 1
   (0.3699716183333183481943602703165, 0.3699716183333183481943602703166),    -- R₂ 0 2
   (-0.1384172752294448305652238322535, -0.1384172752294448305652238322534),  -- R₂ 1 0
   (0.9273764933473602628966108815254, 0.9273764933473602628966108815255),    -- R₂ 1 1
   (0.3475823607503832818487060459119, 0.347582360750383281848706045912),     -- R₂ 1 2
   (-0.3431029820480007134095847534762, -0.3431029820480007134095847534761),  -- R₂ 2 0
   (-0.3741294422880314642159927654031, -0.374129442288031464215992765403),   -- R₂ 2 1
   (0.8615726923034502920582325125458, 0.8615726923034502920582325125459),    -- R₂ 2 2
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001),   -- t 0
   (-0.0000000000000000000000000000001, 0.0000000000000000000000000000001)]   -- t 1

/-- **The enclosure of the optimum of the elongated pentagonal rotunda.** At the root of `system`,
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

end Nieuwland.Johnson.ElongatedPentagonalRotunda
