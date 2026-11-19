import Polyhedra.Antiprism.DecagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.DecagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.DecagonalAntiprism.Proof.Theta

/-!
# The decagonal antiprism: the result

The decagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Antiprism.DecagonalAntiprism

open Notation

/-- **The decagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the decagonal antiprism.** The system `system` has exactly one root in its box;
at the root the first variable is the Nieuwland number `ν polyhedron`, which is greater than `1`,
and the variables of `layout` are rotations `R₁`, `R₂` and a translation `t` with which the
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
  [(1.0004787708596922884875926396103, 1.0004787708596922884875926396104),    -- ν
   (-0.6197759665442298665743124725852, -0.6197759665442298665743124725851),  -- R₁ 0 0
   (0.7844756255485638472422949578039, 0.784475625548563847242294957804),     -- R₁ 0 1
   (0.0218115614836513253011551874203, 0.0218115614836513253011551874204),    -- R₁ 0 2
   (0.3923267702022344064660960929648, 0.3923267702022344064660960929649),    -- R₁ 1 0
   (0.2856478820547343258147507126123, 0.2856478820547343258147507126124),    -- R₁ 1 1
   (0.8743483246740555998795340096823, 0.8743483246740555998795340096824),    -- R₁ 1 2
   (0.6796745226039069490017598878213, 0.6796745226039069490017598878214),    -- R₁ 2 0
   (0.5504573374911392970822490755457, 0.5504573374911392970822490755458),    -- R₁ 2 1
   (-0.4848084806656306352403551142709, -0.4848084806656306352403551142708),  -- R₁ 2 2
   (-0.5878631106089906892309275647906, -0.5878631106089906892309275647905),  -- R₂ 0 0
   (0.8089604212723398611675021413713, 0.8089604212723398611675021413714),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4487228865172254350884565186612, 0.4487228865172254350884565186613),    -- R₂ 1 0
   (0.3260822469590957638581335464968, 0.3260822469590957638581335464969),    -- R₂ 1 1
   (0.8320565721955187496959631072216, 0.8320565721955187496959631072217),    -- R₂ 1 2
   (0.6731008351657059134226752359184, 0.6731008351657059134226752359185),    -- R₂ 2 0
   (0.4891353647335118856400524307314, 0.4891353647335118856400524307315),    -- R₂ 2 1
   (-0.5546907793232581711889051997477, -0.5546907793232581711889051997476),  -- R₂ 2 2
   (-0.0098240578743301041803518062504, -0.0098240578743301041803518062503),  -- t 0
   (-0.0168356507139813934887484435744, -0.0168356507139813934887484435743)]  -- t 1

/-- **The enclosure of the optimum of the decagonal antiprism.** At the root of `system`, the
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
    polyEval [281/256, 59/8, 277/32, -17/2, -211/16, 7, 4, -4, 1] θ = 0 ∧
      (2.0492324906796240899281131768195 : ℝ) ≤ θ ∧
      θ ≤ (2.0492324906796240899281131768196 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.DecagonalAntiprism
