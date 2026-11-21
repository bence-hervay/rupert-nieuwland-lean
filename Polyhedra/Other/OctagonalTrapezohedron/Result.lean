import Polyhedra.Other.OctagonalTrapezohedron.Proof.Optimum
import Polyhedra.Other.OctagonalTrapezohedron.Proof.Enclosure
import Polyhedra.Other.OctagonalTrapezohedron.Proof.Theta

/-!
# The octagonal trapezohedron: the result

The octagonal trapezohedron is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Other.OctagonalTrapezohedron

open Notation

/-- **The octagonal trapezohedron is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the octagonal trapezohedron.** The system `system` has exactly one root in its
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
  [(1.0010437302836081359318606151047, 1.0010437302836081359318606151048),    -- ν
   (-0.8940578714652104923316094637082, -0.8940578714652104923316094637081),  -- R₁ 0 0
   (0.307710159365597789448266822507, 0.3077101593655977894482668225071),     -- R₁ 0 1
   (-0.3255379859467947945144197113383, -0.3255379859467947945144197113382),  -- R₁ 0 2
   (0.3198885847437386349384909538351, 0.3198885847437386349384909538352),    -- R₁ 1 0
   (0.9473047157403822076609971987586, 0.9473047157403822076609971987587),    -- R₁ 1 1
   (0.0168839831402903227019513767899, 0.01688398314029032270195137679),      -- R₁ 1 2
   (0.3135790423828497821117192554125, 0.3135790423828497821117192554126),    -- R₁ 2 0
   (-0.0890406275765847970984608310132, -0.0890406275765847970984608310131),  -- R₁ 2 1
   (-0.9453782051745337475687210276994, -0.9453782051745337475687210276993),  -- R₁ 2 2
   (-0.6619437048478216208916691464099, -0.6619437048478216208916691464098),  -- R₂ 0 0
   (0.7495535548660549279461603659441, 0.7495535548660549279461603659442),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.3403899090182553568953261598222, 0.3403899090182553568953261598223),    -- R₂ 1 0
   (0.3006042143427914661948234518274, 0.3006042143427914661948234518275),    -- R₂ 1 1
   (0.8909387274992017798803285145936, 0.8909387274992017798803285145937),    -- R₂ 1 2
   (0.6678062903648661017211909352781, 0.6678062903648661017211909352782),    -- R₂ 2 0
   (0.5897512820732253992809117100646, 0.5897512820732253992809117100647),    -- R₂ 2 1
   (-0.4541235336801023728523997754782, -0.4541235336801023728523997754781),  -- R₂ 2 2
   (0.0053606671936032418963147494027, 0.0053606671936032418963147494028),    -- t 0
   (0.0033440064092709412123836508314, 0.0033440064092709412123836508315)]    -- t 1

/-- **The enclosure of the optimum of the octagonal trapezohedron.** At the root of `system`, the
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
    polyEval [-2, 0, 40, 0, -248, 0, 480, 0, 1] θ = 0 ∧
      (0.3161948661519344012820893758066 : ℝ) ≤ θ ∧
      θ ≤ (0.3161948661519344012820893758067 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Other.OctagonalTrapezohedron
