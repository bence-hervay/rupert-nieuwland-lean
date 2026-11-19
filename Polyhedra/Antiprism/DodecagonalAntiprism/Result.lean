import Polyhedra.Antiprism.DodecagonalAntiprism.Proof.Optimum
import Polyhedra.Antiprism.DodecagonalAntiprism.Proof.Enclosure
import Polyhedra.Antiprism.DodecagonalAntiprism.Proof.Theta

/-!
# The dodecagonal antiprism: the result

The dodecagonal antiprism is Rupert, and its Nieuwland number and an optimal pose are the one root
of the polynomial system `system` (`Polynomials.lean`); `enclosure` holds them to within `2 ^ -100`.
-/

namespace Nieuwland.Antiprism.DodecagonalAntiprism

open Notation

/-- **The dodecagonal antiprism is Rupert.** -/
theorem isRupert : polyhedron.IsRupert :=
  Proof.isRupert

/-- **The optimum of the dodecagonal antiprism.** The system `system` has exactly one root in its
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
  [(1.0003435367389334460387334991857, 1.0003435367389334460387334991858),    -- ν
   (-0.5286001092842375813945961502099, -0.5286001092842375813945961502098),  -- R₁ 0 0
   (0.848678092003492781891807597286, 0.8486780920034927818918075972861),     -- R₁ 0 1
   (0.018094767696854440734386024727, 0.0180947676968544407343860247271),     -- R₁ 0 2
   (0.4202354203735563161547956225844, 0.4202354203735563161547956225845),    -- R₁ 1 0
   (0.2431042459465879531635797970586, 0.2431042459465879531635797970587),    -- R₁ 1 1
   (0.8742439688474844055546378129908, 0.8742439688474844055546378129909),    -- R₁ 1 2
   (0.737552788570521571002510651508, 0.7375527885705215710025106515081),     -- R₁ 2 0
   (0.4697295197835153257493969432673, 0.4697295197835153257493969432674),    -- R₁ 2 1
   (-0.4851495257297440554303480266829, -0.4851495257297440554303480266828),  -- R₁ 2 2
   (-0.5000807170613731352342573943326, -0.5000807170613731352342573943325),  -- R₂ 0 0
   (0.8659787967516195878578593580131, 0.8659787967516195878578593580132),    -- R₂ 0 1
   (0, 0),                                                                    -- R₂ 0 2
   (0.4807042205951637947853524961825, 0.4807042205951637947853524961826),    -- R₂ 1 0
   (0.2775944540806199753639951395782, 0.2775944540806199753639951395783),    -- R₂ 1 1
   (0.8317840893920000151092257926315, 0.8317840893920000151092257926316),    -- R₂ 1 2
   (0.7203073848888257595718090577869, 0.720307384888825759571809057787),     -- R₂ 2 0
   (0.4159591838633926590237913259696, 0.4159591838633926590237913259697),    -- R₂ 2 1
   (-0.5550992961933219096513999222984, -0.5550992961933219096513999222983),  -- R₂ 2 2
   (0.0081560596661664222481784888063, 0.0081560596661664222481784888064),    -- t 0
   (0.0169421410661504541384256660177, 0.0169421410661504541384256660178)]    -- t 1

/-- **The enclosure of the optimum of the dodecagonal antiprism.** At the root of `system`, the
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
    polyEval [71/128, -17/8, -297/16, 11, 229/8, -14, -5, 0, 1] θ = 0 ∧
      (2.3636116857475321235186088937421 : ℝ) ≤ θ ∧
      θ ≤ (2.3636116857475321235186088937422 : ℝ) :=
  Proof.theta_isRoot

end Nieuwland.Antiprism.DodecagonalAntiprism
