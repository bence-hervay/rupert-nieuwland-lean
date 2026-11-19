import Polyhedra.Johnson.Hebesphenomegacorona.Proof.Optimum
import Polyhedra.Johnson.Hebesphenomegacorona.Proof.Enclosure
import Polyhedra.Johnson.Hebesphenomegacorona.Proof.Theta

/-!
# The hebesphenomegacorona: the result

The hebesphenomegacorona is Rupert, and its Nieuwland number and an optimal pose are the one root of
the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`. -/

namespace Nieuwland.Johnson.Hebesphenomegacorona

open Notation

/-- **The hebesphenomegacorona is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the hebesphenomegacorona.** The system `system` has exactly one root in its
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
  [(1.0294194365860297751739137903613, 1.0294194365860297751739137903614),    -- ν
   (0.0625664800338559080435022124682, 0.0625664800338559080435022124683),    -- R₁ 0 0
   (0.9900928136571324641232806624111, 0.9900928136571324641232806624112),    -- R₁ 0 1
   (-0.1257046376259678048047770471297, -0.1257046376259678048047770471296),  -- R₁ 0 2
   (0.9510231441460882733760978206144, 0.9510231441460882733760978206145),    -- R₁ 1 0
   (-0.0209411279153769030039219202966, -0.0209411279153769030039219202965),  -- R₁ 1 1
   (0.3084095466423184963209449143092, 0.3084095466423184963209449143093),    -- R₁ 1 2
   (0.3027216788977322580269283829304, 0.3027216788977322580269283829305),    -- R₁ 2 0
   (-0.1388441194510397438389180854957, -0.1388441194510397438389180854956),  -- R₁ 2 1
   (-0.9429113933022570552795296627563, -0.9429113933022570552795296627562),  -- R₁ 2 2
   (0, 0),                                                                    -- R₂ 0 0
   (0.5667137690854339568172211638133, 0.5667137690854339568172211638134),    -- R₂ 0 1
   (0.8239147431190811259955688308102, 0.8239147431190811259955688308103),    -- R₂ 0 2
   (0.9998941710983644135836730409984, 0.9998941710983644135836730409985),    -- R₂ 1 0
   (-0.0119863767983404237209857072178, -0.0119863767983404237209857072177),  -- R₂ 1 1
   (0.0082445967010495917430389207139, 0.008244596701049591743038920714),     -- R₂ 1 2
   (0.0145480790317743131934823227509, 0.014548079031774313193482322751),     -- R₂ 2 0
   (0.8238275491267754673089368734542, 0.8238275491267754673089368734543),    -- R₂ 2 1
   (-0.5666537943897098819928869611052, -0.5666537943897098819928869611051),  -- R₂ 2 2
   (-0.2655459718503265964258152618476, -0.2655459718503265964258152618475),  -- t 0
   (0.0861380924020081724936223319168, 0.0861380924020081724936223319169)]    -- t 1

/-- **The enclosure of the optimum of the hebesphenomegacorona.** At the root of `system`, the
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
    polyEval [729/20552089600, 0, -603/321126400, 0, 435823/11560550400, 0, -637433/1445068800, 0,
      4314871/1156055040, 0, -2194643/90316800, 0, 85548047/722534400, 0, -38449237/90316800, 0,
      156349133/144506880, 0, -758221/470400, 0, 1] θ = 0 ∧
      (0.3529540763371607483505637509522 : ℝ) ≤ θ ∧
      θ ≤ (0.3529540763371607483505637509523 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Johnson.Hebesphenomegacorona
